"""Verify current 0.5.0 source inventory; no sampling or compilation."""
from pathlib import Path
import hashlib,json
root=Path(__file__).resolve().parents[1]
inventory=json.loads((root/'release/0.5.0/SOURCE-FILES.json').read_bytes())
assert inventory['excluded_inventory_path']=='release/0.5.0/SOURCE-FILES.json'
for name,digest in inventory['files'].items():
 p=root/name
 assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest()==digest,name
print(json.dumps({'status':'source_bytes_verified','version':'0.5.0','files':len(inventory['files']),'proof_or_runtime_claim':False}))
