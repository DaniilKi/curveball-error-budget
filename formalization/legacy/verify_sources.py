"""Verify exact focused upstream bodies, scopes and successful receipt hashes."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def sha(data):return hashlib.sha256(data).hexdigest()
def load(rel):return json.loads((ROOT/rel).read_text(encoding='utf-8-sig'))
mapping=load('provenance/exact-body-extraction-map.json');receipt=load('provenance/focused-verification.json')
lock={x['path']:x for x in load('provenance/focused-source-lock.json')['files']}
extraction=(ROOT/'ExactBodyExtraction.lean').read_bytes();text=extraction.decode('utf-8').replace('\r\n','\n')
assert sha(extraction)==receipt['exact_extraction_sha256']==mapping['extraction_sha256']
assert sha(text.encode('utf-8'))==mapping['extraction_normalized_utf8_lf_sha256']
assert sha((ROOT/'CurveballAssurance.lean').read_bytes())==receipt['wrapper_sha256']==mapping['private_wrapper_sha256']
assert len(mapping['mapping'])==receipt['proof_bodies_checked']==153
for record in mapping['mapping']:
    data=(ROOT/'upstream'/record['source_path'].removeprefix('lean/')).read_bytes()
    assert sha(data)==record['original_sha256']==lock[record['source_path']]['sha256']
    body=re.sub(r'^import [^\n]*\n','',data.decode('utf-8'),flags=re.M)
    assert sha(body.encode('utf-8'))==record['proof_body_sha256']
    marker='/- BEGIN exact official body: '+record['source_path']+' -/\nsection\n'
    ending='\nend\n/- END exact official body: '+record['source_path']+' -/'
    assert text.split(marker,1)[1].split(ending,1)[0]==body
    assert record['original_namespace_section_stack_balanced']
assert receipt['compiler_exit_code']==0 and not receipt['sorryAx_or_extra_axioms']
assert len(receipt['axiom_reports'])==5
assert all(set(value)<={'propext','Classical.choice','Quot.sound'}for value in receipt['axiom_reports'].values())
assert all(x['expected']==x['actual']for x in receipt['dependency_revisions'])
print(json.dumps({'status':'passed','official_bodies':153,'extraction_sha256':sha(extraction),'wrapper_sha256':receipt['wrapper_sha256'],'scope':'hash/body and recorded receipt verification; this script does not compile Lean'}))
