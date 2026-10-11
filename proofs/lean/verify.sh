#!/usr/bin/env sh
set -eu
cd "$(dirname "$0")"
"${PYTHON:-python3}" prepare_verification.py
mkdir -p _build/verification/build-logs
while IFS= read -r module; do
  [ -n "$module" ] || continue
  rel=$(printf '%s' "$module" | tr . /)
  case "$module" in
    QIT|QIT.*) root=vendor/Lean-QIT; auto=-DautoImplicit=false ;;
    *) root=.; auto= ;;
  esac
  out="$root/.lake/build/lib/lean/$rel.olean"
  mkdir -p "$(dirname "$out")"
  lake env lean -j1 -s524288 -R "$root" $auto "$root/$rel.lean" -o "$out" >"_build/verification/build-logs/$module.log" 2>&1
done < _build/verification/source-order.txt
lake env lean -t0 -j1 -s524288 Audit.lean >_build/verification/theorem-axioms.txt 2>&1
"${PYTHON:-python3}" prepare_verification.py --check-audit _build/verification/theorem-axioms.txt
printf '%s\n' 'Source closure and theorem axiom audit completed successfully.'
