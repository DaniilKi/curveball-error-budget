"""Check the explicit sanitized source inventory; no compilation or networking."""
from pathlib import Path,PurePosixPath
import hashlib,json,sys
ROOT=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def safe_relative(s):
 if not isinstance(s,str)or not s or '\\'in s or ':'in s:raise ValueError('unsafe relative path')
 p=PurePosixPath(s)
 if not p.parts or p.is_absolute()or any(x in ('..','.')for x in p.parts)or p.as_posix()!=s:raise ValueError('unsafe relative path')
 for part in p.parts:
  if part.endswith(('.', ' '))or part.split('.')[0].casefold()in {'con','prn','aux','nul',*[f'com{i}'for i in range(1,10)],*[f'lpt{i}'for i in range(1,10)]}:raise ValueError('Windows alias/reserved path')
 return p
def verify(root=ROOT):
 root=Path(root);path=root/'RELEASE-FILES.json'
 if root.is_symlink():raise ValueError('symlink root')
 manifest=json.loads(path.read_bytes());rows=manifest['files']
 if manifest.get('schema')!=1 or type(manifest.get('schema'))is not int:raise ValueError('manifest schema')
 names=set()
 for r in rows:
  rel=safe_relative(r['path']);name=rel.as_posix()
  if name.casefold()in {x.casefold()for x in names}:raise ValueError('duplicate inventory path')
  names.add(name);p=root/name
  if p.is_symlink()or not p.is_file():raise ValueError('missing/symlink artifact '+name)
  if not p.resolve().is_relative_to(root.resolve()):raise ValueError('escaped artifact')
  if p.stat().st_size!=r['bytes']or sha(p)!=r['sha256']:raise ValueError('artifact mismatch '+name)
 allpaths=list(root.rglob('*'))
 if any(p.is_symlink()for p in allpaths):raise ValueError('symlink in source tree')
 if any('__pycache__'in p.parts for p in allpaths):raise ValueError('cache directory in sanitized source tree')
 actual={p.relative_to(root).as_posix()for p in allpaths if p.is_file()}
 if actual!=names|{'RELEASE-FILES.json'}:raise ValueError('unexpected/missing files '+repr(sorted(actual^(names|{'RELEASE-FILES.json'}))))
 status=json.loads((root/'RELEASE-STATUS.json').read_bytes())
 if any(status.get(k)is not False for k in ['scientific_rejection_authorized','tv_assurance_authorized','ideal_randomness_claim','graph_refinement_binary_claim']):raise ValueError('assurance flag enabled or absent')
 if status.get('published')is not False or status.get('public_version_or_tag_created')is not False:raise ValueError('publication hold missing')
 return {'status':'source_inventory_verified_publication_still_held','files':len(rows),'inventory_sha256':sha(path)}
if __name__=='__main__':
 try:print(json.dumps(verify(),indent=2))
 except (OSError,ValueError,KeyError,TypeError)as e:print(json.dumps({'status':'blocked','reason':str(e)}));raise SystemExit(2)
