param([string]$Lake = 'lake', [string]$Python = 'python', [switch]$Resume)
$ErrorActionPreference = 'Stop'
$root = $PSScriptRoot
& $Python (Join-Path $root 'prepare_verification.py')
if ($LASTEXITCODE -ne 0) { throw 'Current-source closure preparation failed.' }
$runRoot = Join-Path $root '_build/verification'
$closure = Get-Content -LiteralPath (Join-Path $runRoot 'closure.json') -Raw | ConvertFrom-Json
$logs = Join-Path $runRoot 'build-logs'
New-Item -ItemType Directory -Force -Path $logs | Out-Null
$ledgerPath = Join-Path $runRoot 'verified-source.jsonl'
$known = @{}
if ($Resume -and (Test-Path -LiteralPath $ledgerPath)) {
    Get-Content -LiteralPath $ledgerPath | ForEach-Object {
        $record = $_ | ConvertFrom-Json
        if ($record.exitCode -eq 0) { $known[$record.module] = $record.fingerprint }
    }
}
Push-Location $root
try {
    $n = 0
    $fingerprints = @{}
    $moduleData = @{}
    foreach ($m in $closure.modules) { $moduleData[$m.name] = $m }
    $dependencySeed = $closure.configuration_sha256
    foreach ($module in $closure.order) {
        $n++
        $vendor = $module -eq 'QIT' -or $module.StartsWith('QIT.')
        $packageRoot = if ($vendor) { 'vendor/Lean-QIT' } else { '.' }
        $source = Join-Path $packageRoot ($module.Replace('.', '/') + '.lean')
        $out = Join-Path $packageRoot ('.lake/build/lib/lean/' + $module.Replace('.', '/') + '.olean')
        $hash = (Get-FileHash -LiteralPath $source -Algorithm SHA256).Hash.ToLowerInvariant()
        if ($hash -ne $moduleData[$module].sha256) { throw "Source hash changed: $module" }
        $inputs = $hash + $dependencySeed
        foreach ($dependency in $moduleData[$module].imports) {
            $inputs += $dependency + $fingerprints[$dependency]
        }
        $hasher = [System.Security.Cryptography.SHA256]::Create()
        try { $fingerprint = ([BitConverter]::ToString($hasher.ComputeHash([Text.Encoding]::UTF8.GetBytes($inputs)))).Replace('-','').ToLowerInvariant() }
        finally { $hasher.Dispose() }
        $fingerprints[$module] = $fingerprint
        if ($Resume -and $known[$module] -eq $fingerprint -and (Test-Path -LiteralPath $out)) {
            continue
        }
        New-Item -ItemType Directory -Force -Path (Split-Path $out) | Out-Null
        $log = Join-Path $logs ($module + '.log')
        $started = [DateTime]::UtcNow
        $leanArgs = @('env', 'lean', '-j1', '-s524288', '-R', $packageRoot)
        if ($vendor) { $leanArgs += '-DautoImplicit=false' }
        $leanArgs += @($source, '-o', $out)
        & $Lake @leanArgs *> $log
        $exitCode = $LASTEXITCODE
        $record = [ordered]@{ module=$module; sha256=$hash; fingerprint=$fingerprint; exitCode=$exitCode;
            startedUTC=$started.ToString('o'); seconds=([DateTime]::UtcNow-$started).TotalSeconds }
        ($record | ConvertTo-Json -Compress) | Add-Content -LiteralPath $ledgerPath -Encoding UTF8
        if ($exitCode -ne 0) { throw "Lean failed on $module. Read $log" }
        if (($n % 25) -eq 0 -or $n -eq $closure.order.Count) {
            Write-Output "Checked $n/$($closure.order.Count): $module"
        }
    }
    & $Lake env lean -t0 -j1 -s524288 Audit.lean *> (Join-Path $runRoot 'theorem-axioms.txt')
    if ($LASTEXITCODE -ne 0) { throw 'Theorem audit failed; read _build/verification/theorem-axioms.txt' }
    & $Python (Join-Path $root 'prepare_verification.py') --check-audit (Join-Path $runRoot 'theorem-axioms.txt')
    if ($LASTEXITCODE -ne 0) { throw 'Current endpoint axiom validation failed.' }
    Write-Output 'Source closure and theorem axiom audit completed successfully.'
} finally { Pop-Location }
