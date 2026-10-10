"""Bounded captured JSON -> finite Lean certificate; no sampling or compilation.

The emitted certificate proves deterministic properties of the provided data.
Source-binding metadata is a provenance assertion, not proof of execution or
authenticity. Occurrence labels are deterministic and have no random-input law.
This portable helper is a NEW integration-review candidate.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import sys

MAX_INPUT_BYTES = 65536
MAX_VERTICES = 8
MAX_STUBS = 16
TOP_KEYS = {'schema_version','n','target_degrees','fixed_edges','owners',
            'returned_adjacency','source_binding'}
BINDING_KEYS = {'reference_sha256','function_source_sha256','function_ast_sha256'}

class InvalidCapture(ValueError):
    pass

def require(ok, message):
    if not ok:
        raise InvalidCapture(message)

def distinct_object(pairs):
    result = {}
    for key,value in pairs:
        require(key not in result,'duplicate JSON object key')
        result[key] = value
    return result

def natural(value, upper, label):
    require(type(value) is int and 0 <= value <= upper, label+' must be a bounded integer')
    return value

def validate_capture(data):
    require(type(data) is dict and set(data)==TOP_KEYS,'unknown or missing top-level key')
    require(type(data['schema_version']) is int and data['schema_version']==1,'schema_version must be 1')
    n=natural(data['n'],MAX_VERTICES,'n'); require(n>=1,'n must be positive')
    d=data['target_degrees']
    require(type(d) is list and len(d)==n,'target_degrees length must equal n')
    for v in d:natural(v,n-1,'degree')
    fixed=data['fixed_edges']
    require(type(fixed) is list and len(fixed)<=n*(n-1)//2,'fixed_edges must be a bounded list')
    fixed_set=set(); fadj=[set() for _ in range(n)]
    for edge in fixed:
        require(type(edge) is list and len(edge)==2,'fixed edge must have two endpoints')
        a=natural(edge[0],n-1,'fixed endpoint'); b=natural(edge[1],n-1,'fixed endpoint')
        require(a<b,'fixed edges must have increasing endpoints')
        require((a,b) not in fixed_set,'duplicate fixed edge')
        fixed_set.add((a,b)); fadj[a].add(b); fadj[b].add(a)
    owners=data['owners']
    require(type(owners) is list and len(owners)<=MAX_STUBS,'owners exceeds stub bound')
    require(len(owners)%2==0,'owner array must have even length')
    for v in owners:natural(v,n-1,'owner')
    s=[d[v]-len(fadj[v]) for v in range(n)]
    require(all(v>=0 for v in s),'fixed degree exceeds target degree')
    counts=[0]*n; labels=[]
    for v in owners:
        labels.append([v,counts[v]]); counts[v]+=1
    require(counts==s,'owner multiplicities must equal residual degrees')
    adjacency=data['returned_adjacency']
    require(type(adjacency) is list and len(adjacency)==n,'returned_adjacency length must equal n')
    adj=[]
    for v,neighbors in enumerate(adjacency):
        require(type(neighbors) is list and len(neighbors)<=n-1,'invalid neighbor list')
        for w in neighbors:natural(w,n-1,'neighbor')
        require(len(set(neighbors))==len(neighbors),'duplicate adjacency entry')
        require(v not in neighbors,'output self-loop')
        adj.append(set(neighbors))
    require(all(v in adj[w] for v in range(n) for w in adj[v]),'asymmetric adjacency')
    require([len(x) for x in adj]==d,'output degrees differ from target')
    projected=set()
    for i in range(0,len(owners),2):
        a,b=owners[i:i+2]; require(a!=b,'owner-pair self-loop')
        edge=(min(a,b),max(a,b))
        require(edge not in fixed_set,'owner-pair retained-edge collision')
        require(edge not in projected,'duplicate projected owner edge')
        projected.add(edge)
    output={(v,w) for v in range(n) for w in adj[v] if v<w}
    require(output==fixed_set|projected,'output is not exactly fixed union owner-pair edges')
    binding=data['source_binding']
    require(type(binding) is dict and set(binding)==BINDING_KEYS,'invalid source-binding keys')
    for value in binding.values():
        require(type(value) is str and re.fullmatch(r'[0-9a-f]{64}',value) is not None,'source-binding hash must be lowercase SHA-256')
    normalized={'schema_version':1,'n':n,'target_degrees':list(d),
        'fixed_edges':[list(e) for e in sorted(fixed_set)],'owners':list(owners),
        'returned_adjacency':[sorted(x) for x in adj],
        'source_binding':{k:binding[k] for k in sorted(binding)}}
    return normalized,s,labels,[list(e) for e in sorted(output)]

def load_capture(path):
    with Path(path).open('rb') as stream:
        raw=stream.read(MAX_INPUT_BYTES+1)
    require(len(raw)<=MAX_INPUT_BYTES,'capture exceeds byte limit')
    try:
        data=json.loads(raw.decode('utf-8'),object_pairs_hook=distinct_object,
                        parse_constant=lambda value: (_ for _ in ()).throw(InvalidCapture('nonfinite JSON value')))
    except (UnicodeDecodeError,json.JSONDecodeError,RecursionError) as error:
        raise InvalidCapture('invalid bounded UTF-8 JSON') from error
    return validate_capture(data)

def vertex_function(values):
    return 'fun v => match v.val with\n'+'\n'.join(
        f'  | {i} => {v}' for i,v in enumerate(values[:-1]))+f'\n  | _ => {values[-1]}'

def position_function(values):
    if not values:return 'fun z => Fin.elim0 z.1'
    m=len(values)//2
    return f'fun z => match (pairIndex {m} z).val with\n'+'\n'.join(
        f'  | {i} => {v}' for i,v in enumerate(values[:-1]))+f'\n  | _ => {values[-1]}'

def lean_edges(edges):
    return '['+','.join(f'({a},{b})' for a,b in edges)+']'

def module_identifier(checked):
    encoded=json.dumps(checked[0],sort_keys=True,separators=(',',':')).encode('utf-8')
    return 'OwnerCapture_'+hashlib.sha256(encoded).hexdigest()

def emit_lean(checked):
    data,s,labels,output=checked; n=data['n']; m=len(data['owners'])//2
    namespace='ConfigurationPairing.CapturedOwnerCertificates.'+module_identifier(checked)
    # Only validated integers enter the Lean source. User strings are never emitted.
    lines=['import ConfigurationOwnerCertificate',
        '/- Deterministic properties of provided captured data; no RNG/IID claim. -/',
        'namespace '+namespace,'open ConfigurationPairing',
        f'def fixedEdges : List (Fin {n} × Fin {n}) := '+lean_edges(data['fixed_edges']),
        f'def outputEdges : List (Fin {n} × Fin {n}) := '+lean_edges(output),
        'def F := edgeListGraph fixedEdges','def G := edgeListGraph outputEdges',
        'instance fixedAdjDecidable : DecidableRel F.Adj := edgeListGraphDecidable fixedEdges',
        'instance outputAdjDecidable : DecidableRel G.Adj := edgeListGraphDecidable outputEdges',
        f'def d : Fin {n} → Nat := '+vertex_function(data['target_degrees']),
        f'def s : Fin {n} → Nat := '+vertex_function(s),
        f'def owners : Fin {m} × Bool → Fin {n} := '+position_function([str(v) for v in data['owners']]),
        f'def lift : Fin {m} × Bool → Stub s := '+position_function([f'⟨{v},⟨{k},by decide⟩⟩' for v,k in labels]),
        'theorem raw_edge_encoding_checked : CanonicalEdgeEncoding fixedEdges ∧ CanonicalEdgeEncoding outputEdges := by decide',
        'theorem certificate_checked : ownerCertificateCheck F G d s owners lift = true := by decide',
        'theorem captured_output_decodes :',
        f'    ∃ (g : TargetGraph F d) (slots : Fin {m} × Bool ≃ Stub (residualDegree F d)),',
        '      g.val = G ∧ (∀ z, (slots z).1 = owners z) ∧',
        f'      graphDecoder F d (adjacentPairing (residualDegree F d) {m} slots) = some g :=',
        '  ownerCertificateCheck_sound F G d s owners lift certificate_checked',
        'set_option pp.all true in','#check @captured_output_decodes',
        '#print axioms raw_edge_encoding_checked','#print axioms certificate_checked',
        '#print axioms captured_output_decodes','end '+namespace]
    return '\n'.join(lines)+'\n'

def write_new_directory(directory, checked):
    path=Path(directory)
    require(not path.exists(),'output directory must not exist; existing artifacts are preserved')
    lean=emit_lean(checked).encode('utf-8')
    normalized=(json.dumps(checked[0],indent=2,sort_keys=True)+'\n').encode('utf-8')
    path.mkdir(parents=False,exist_ok=False)
    source_name=module_identifier(checked)+'.lean'
    for name,value in [(source_name,lean),('capture.normalized.json',normalized)]:
        with (path/name).open('xb') as stream:stream.write(value)
    return {'lean_source_file':source_name,'lean_sha256':hashlib.sha256(lean).hexdigest(),
            'normalized_capture_sha256':hashlib.sha256(normalized).hexdigest()}

def main(argv=None):
    parser=argparse.ArgumentParser(description='Validate bounded captured data and optionally emit a Lean certificate. Does not execute a decoder, RNG or compiler.')
    parser.add_argument('capture',type=Path)
    parser.add_argument('--output-dir',type=Path,help='A new directory; omit for validation only.')
    args=parser.parse_args(argv)
    try:
        checked=load_capture(args.capture)
        result={'validation':'PASS','n':checked[0]['n'],'distinct_stubs':len(checked[0]['owners']),
                'claim':'Deterministic properties of provided finite data; source metadata is not execution authentication.',
                'review_status':'Portable helper candidate; entrypoint use requires independent integration review.',
                'compiler_runs':0,'rng_calls':0,'decoder_calls':0}
        if args.output_dir is not None:result.update(write_new_directory(args.output_dir,checked))
        print(json.dumps(result,sort_keys=True));return 0
    except (InvalidCapture,OSError,ValueError) as error:
        print('Capture refused: '+str(error),file=sys.stderr);return 2

if __name__=='__main__':
    raise SystemExit(main())
