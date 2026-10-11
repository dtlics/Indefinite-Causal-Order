"""Verify the canonical RG source and certificate chain without modifying it.

Usage: python verify_proof.py --tier full --report /tmp/proof-report.json
All proof scripts run in a temporary copy because several regenerate JSON files.
"""
from pathlib import Path
import argparse,ast,hashlib,json,re,shutil,subprocess,sys,tempfile,time

OLD_CORE=[
 'auxiliary_full_boundary_checks.py',
 'continuous_product_supported_cut_audit_all_cylinders.py',
 'auxiliary_multiplicity_free_exact.py',
 'phase_mask_exact_verifier.py',
 'auxiliary_cut_complete_polynomial.py',
 'auxiliary_tangent_verify_extras.py',
 'auxiliary_new_projector_closed_forms.py',
 'auxiliary_tangent_projector_extensions.py',
 'auxiliary_joint_phase_four_row_verifier.py',
 'auxiliary_four_sector_independent_audit.py',
 'auxiliary_four_sector_qubit_obstruction.py',
 'auxiliary_cut_C4_joint_independent_check.py',
 'auxiliary_host_all_curvature_independent_audit.py',
 'auxiliary_host_all_components_independent_audit.py',
 'native_branch_cover_checks.py',
 'native_single_branch_centrality_checks.py',
 'native_branch_cooccurrence_baseline_counterexample.py',
 'native_strict_partition_rank_checks.py',
 'auxiliary_strict_m4_cocycle_obstruction.py',
 'strict_auxiliary_complete_independent_audit.py',
]
OLD_FULL=[
 'auxiliary_tangent_independent_audit.py',
 'continuous_product_classification.py',
 'auxiliary_new_projector_independent_audit.py',
 'auxiliary_four_sector_input_flags.py',
 'auxiliary_host_curvature_independent_audit.py',
 'auxiliary_multiplicity_free_independent_audit.py',
 'seven_context_synthesis_reduction.py',
 'seven_context_lugano_rewrite_check.py',
 'auxiliary_host_compatibility_independent_audit.py',
]

V3_CORE=['branch_flag_loop_branched_calibration.py', 'branch_flag_loop_same_scc_calibration.py', 'branch_condensation_cut_record_checks.py', 'verify_commuting_origin_rigidity.py', 'green_layer_future_marker_independent_check.py', 'branch_layer_joint_occurrence_checks.py', 'branch_layer_product_dimension_checks.py', 'cross_serial_cylinder_independent_audit.py', 'branch_layer_saturated_passive_checks.py', 'branch_path_phase_causality_checks.py', 'branch_layer_scalar_record_lift_checks.py', 'branch_red_full_input_record_checks.py', 'branch_red_original34_commutator_checks.py', 'non_green_input_gather_checks.py', 'non_green_input_gather_quantum_audit.py', 'core_group_cut_branch_independent_check.py', 'upstream_matrix_causality/check_downset_exchange_permutation.py', 'upstream_matrix_causality/red_split_vertex_calibration.py', 'core_ancestral_controlled_factor_independent_check.py', 'aggregate_core_carrier_checks.py', 'bounded_layer_tensor_normal_form_independent_check.py']
V3_FULL=OLD_CORE+OLD_FULL

CORE=['quartet_process_definition_checks.py', 'context_closure.py', 'locked_contexts.py', 'verify_first_port_serial_ideals.py', 'verify_last_port_maximality.py', 'independent_maximality_check.py', 'native_single_branch_centrality_checks.py', 'cross_serial_cylinder_independent_audit.py', 'verify_commuting_origin_rigidity.py', 'green_layer_future_marker_independent_check.py', 'branch_layer_joint_occurrence_checks.py', 'branch_layer_product_dimension_checks.py', 'branch_path_phase_causality_checks.py', 'branch_layer_saturated_passive_checks.py', 'non_green_input_gather_quantum_audit.py', 'branch_red_original34_commutator_checks.py', 'rank_two_recurrence_audit/check_lugano_rank_two.py']
FULL=[s for s in V3_CORE+V3_FULL if s not in CORE]

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--tier',choices=['integrity','core','full'],default='core')
 ap.add_argument('--report',type=Path)
 ap.add_argument('--log-dir',type=Path)
 ap.add_argument('--allow-unfrozen',action='store_true',help='Staging only: allow absence of the final checksum manifest')
 args=ap.parse_args();root=Path(__file__).resolve().parent;start=time.time();result={'tier':args.tier,'status':'RUNNING','checks':[]}
 manifest=root/'SHA256SUMS.json'
 if manifest.exists():
  for output in [args.report,args.log_dir]:
   if output is not None:assert not output.resolve().is_relative_to(root),'Report/log output must be outside the canonical source tree'
  hashes=json.loads(manifest.read_text());actual={p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p!=manifest}
  assert actual==set(hashes),(sorted(actual-set(hashes)),sorted(set(hashes)-actual))
  for name,expected in hashes.items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==expected,name
  result['integrity_files']=len(hashes);result['sha256_manifest']='PASS'
 else:
  assert args.allow_unfrozen,'Missing final SHA256SUMS.json'
  result['sha256_manifest']='STAGING: not finalized yet'
 sources=list(root.rglob('*.py'))
 for p in sources:ast.parse(p.read_text(),filename=str(p))
 result['python_syntax_files']=len(sources)
 # Statements/scopes live in the canonical sections; verify their unique
 # navigation anchors without a second status registry.
 result_documents=list((root/'results').glob('*.md'))
 anchors=[]
 for doc in result_documents:
  anchors.extend(re.findall(r'<a id="(rg-\d{3})"></a>',doc.read_text(encoding='utf-8')))
 assert len(anchors)==len(set(anchors)),'Duplicate canonical result anchors'
 assert set(anchors)=={f'rg-{i:03d}' for i in range(1,78)},'Missing canonical result'
 result['canonical_result_anchors']=len(anchors)
 deps=json.loads((root/'PROOF_DEPENDENCY_MANIFEST.json').read_text())
 for node in deps['nodes']:
  for f in node['files']:
   p=root/f['path'];assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256'],f['path']
 
   if 'anchor' in f:assert ('id=\"'+f['anchor']+'\"') in p.read_text(encoding='utf-8'),f['anchor']
 result['proof_dependency_nodes']=len(deps['nodes']);result['proof_dependency_hashes']='PASS'
 if args.tier!='integrity':
  scripts=CORE+(FULL if args.tier=='full' else [])
  if args.log_dir:args.log_dir.mkdir(parents=True,exist_ok=True)
  with tempfile.TemporaryDirectory(prefix='routed-proof-verify-') as td:
   work=Path(td)/'work';shutil.copytree(root,work,ignore=shutil.ignore_patterns('__pycache__'))
   for script in scripts:
    assert (work/script).is_file(),script
    tick=time.time();proc=subprocess.run([sys.executable,Path(script).name],cwd=work / Path(script).parent,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    rec={'script':script,'exit_code':proc.returncode,'seconds':round(time.time()-tick,3),'status':'PASS' if proc.returncode==0 else 'FAIL'};result['checks'].append(rec)
    if args.log_dir:(args.log_dir/(Path(script).stem+'.log')).write_text(proc.stdout)
    print(json.dumps(rec),flush=True)
    if proc.returncode:
     print(proc.stdout[-12000:]);result['status']='FAIL';break
 result['status']='PASS' if result['status']!='FAIL' else 'FAIL';result['seconds']=round(time.time()-start,3)
 if args.report:args.report.parent.mkdir(parents=True,exist_ok=True);args.report.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2));return 0 if result['status']=='PASS' else 1
if __name__=='__main__':raise SystemExit(main())
