"""Draft fail-closed local manifest assembly: never download or execute a binary."""
from pathlib import Path
import argparse,hashlib,json,shutil,sys
sys.dont_write_bytecode=True
sys.path.insert(0,str(Path(__file__).resolve().parent))
from verify_release_tree import ROOT,verify,safe_relative,sha
MODULES={'NativeArithmetic','NativeGraph','NativeEntropy','NativeSubset','NativeReplay','NativeSamplingProtocol'}
FLAGS=['scientific_guarantee_enabled','scientific_rejection_authorized','tv_assurance_authorized','ideal_randomness_claim','graph_refinement_binary_claim']
def digest_ok(s):return isinstance(s,str)and len(s)==64 and all(c in '0123456789abcdef'for c in s)
def validated_profile(approval,profile):
 if type(approval.get('schema'))is not int or approval['schema']!=1:raise ValueError('approval schema')
 p=approval['profiles'][profile]
 if any(p.get(k)is not False for k in FLAGS):raise ValueError('scientific flags must remain false')
 if p.get('approved_for_local_install')is not True:raise ValueError('release_backend_not_approved')
 if p.get('proof_transfer_status')!='accepted'or not digest_ok(p.get('independent_binary_review_sha256')):raise ValueError('accepted proof/binary review binding missing')
 if p.get('release_review_status')not in ['pending_mainreview','GO']:raise ValueError('release review status')
 if p['release_review_status']=='GO'and not digest_ok(p.get('final_release_review_sha256')):raise ValueError('GO review binding missing')
 if set(p.get('source_modules',{}))!=MODULES:raise ValueError('source module set')
 if any(not digest_ok(h)for h in p['source_modules'].values()):raise ValueError('source digest')
 if p.get('native_executable_name')!='NativeSamplingProtocol.exe'or not digest_ok(p.get('native_executable_sha256')):raise ValueError('binary descriptor')
 for k in ['accepted_core_manifest','build_receipts']:
  x=p.get(k)
  if not isinstance(x,dict)or not digest_ok(x.get('sha256')):raise ValueError('missing provenance descriptor')
  safe_relative(x['path'])
 extras=p.get('additional_artifacts')
 if not isinstance(extras,list):raise ValueError('artifact descriptors')
 for x in extras:
  if not isinstance(x,dict)or not digest_ok(x.get('sha256')):raise ValueError('artifact descriptor')
  safe_relative(x['path'])
 for x in approval.get('python_artifacts',[]):
  safe_relative(x['path'])
  if not digest_ok(x['sha256']):raise ValueError('Python descriptor')
 required={'src/curveball_budget/arithmetic_invocation.py','src/curveball_budget/sampling_invocation.py','src/curveball_budget/sampling_protocol.py','src/curveball_budget/sampling_cli.py','src/curveball_budget/__init__.py'}
 if len(approval.get('python_artifacts',[]))!=len(required)or {x['path']for x in approval.get('python_artifacts',[])}!=required:raise ValueError('Python source set')
 return p
def install(profile,runtime_dir,output,python_package_dir=None):
 verify();approval=json.loads((ROOT/'backend-approval.json').read_bytes());p=validated_profile(approval,profile)
 source=Path(runtime_dir);out=Path(output)
 if source.is_symlink()or not source.is_dir():raise ValueError('runtime directory')
 if out.exists():raise ValueError('output already exists')
 descriptions=[{'path':n+'.lean','sha256':h}for n,h in sorted(p['source_modules'].items())]
 descriptions +=[{'path':p['native_executable_name'],'sha256':p['native_executable_sha256']},p['accepted_core_manifest'],p['build_receipts']]+p['additional_artifacts']
 names=set()
 for d in descriptions:
  rel=safe_relative(d['path']);q=source/rel.as_posix()
  if rel.parts[0].casefold()=='installation.json':raise ValueError('reserved installation manifest artifact path')
  if d['path'].casefold()in names:raise ValueError('duplicate artifact')
  names.add(d['path'].casefold())
  components=[source.joinpath(*rel.parts[:i])for i in range(1,len(rel.parts)+1)]
  if any(x.is_symlink()for x in components)or not q.is_file()or not q.resolve().is_relative_to(source.resolve())or sha(q)!=d['sha256']:raise ValueError('runtime artifact mismatch')
 pkg=Path(python_package_dir)if python_package_dir is not None else ROOT/'src/curveball_budget'
 for d in approval['python_artifacts']:
  q=pkg/Path(d['path']).name
  if pkg.is_symlink()or q.is_symlink()or sha(q)!=d['sha256']:raise ValueError('installed Python source changed')
 # All source/proof/review checks precede mutation. Preserve partial failure evidence.
 out.mkdir(parents=True,exist_ok=False);artifacts=[]
 for d in descriptions:
  q=out/d['path'];q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source/d['path'],q)
  if sha(q)!=d['sha256']:raise ValueError('copied artifact mismatch')
  artifacts.append({'path':str(q.resolve()),'sha256':d['sha256']})
 artifacts +=[{'path':str((pkg/Path(d['path']).name).resolve()),'sha256':d['sha256']}for d in approval['python_artifacts']]
 m={'schema':1,'protocol':'CBSAMPLE1','build_status':'native_built','native_executable':str((out/p['native_executable_name']).resolve()),
  'source_modules':{n:str((out/(n+'.lean')).resolve())for n in p['source_modules']},'accepted_core_manifest':str((out/p['accepted_core_manifest']['path']).resolve()),
  'build_receipts':str((out/p['build_receipts']['path']).resolve()),'artifacts':artifacts,'assurance':None,**{k:False for k in FLAGS},
  'profile':profile,'candidate_binary_review_sha256':p['independent_binary_review_sha256'],
  'python_runtime_sources':{Path(d['path']).name:d['sha256']for d in approval['python_artifacts']},
  'conditional_contract':p.get('conditional_contract'),'release_review_status':p['release_review_status'],'final_release_review_sha256':p.get('final_release_review_sha256'),
  'trusted_python_scope':'Exact separately pinned Python bytes; Python/physical I/O/compiler/entropy remain trusted correspondences'}
 target=out/'installation.json';target.write_text(json.dumps(m,indent=2)+'\n',encoding='utf-8')
 return {'status':'local_manifest_created_scientific_flags_false','installation':str(target.resolve()),'installation_sha256':sha(target),'binary_executed':False,'network_calls':0}
def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--profile',choices=['optimized','frozen'],required=True)
 parser.add_argument('--runtime-dir',type=Path,required=True);parser.add_argument('--output',type=Path,required=True);parser.add_argument('--python-package-dir',type=Path);a=parser.parse_args()
 try:print(json.dumps(install(a.profile,a.runtime_dir,a.output,a.python_package_dir),indent=2));return 0
 except (OSError,ValueError,KeyError,TypeError)as e:print(json.dumps({'status':'blocked','reason':str(e),'binary_executed':False,'network_calls':0}));return 2
if __name__=='__main__':raise SystemExit(main())
