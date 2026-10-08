"""Native sampling command, dormant until an exact native installation exists."""
import argparse,json
from pathlib import Path
from .sampling_invocation import invoke
from .sampling_protocol import MAX_REQUEST,MAX_ENTROPY

def main(argv=None):
 p=argparse.ArgumentParser(description='Bounded native reference; conditional uniform-degree null contract, independent-byte/physical-IO trust; supplied tapes unassured')
 p.add_argument('--request',required=True);p.add_argument('--installation',required=True)
 p.add_argument('--installation-sha256',required=True);p.add_argument('--entropy-file')
 p.add_argument('--resume',action='store_true');p.add_argument('--timeout',type=float,default=45)
 p.add_argument('--predeclared',action='store_true',help='record configuration/statistic fixed before observation')
 p.add_argument('--fixed-degree-null',action='store_true',help='declare uniform labeled simple graph conditional on exact labeled degrees; not arbitrary fixed graph')
 p.add_argument('--trust-uniform-bytes',action='store_true',help='acknowledge independent uniform full-byte provider law as external trust; not measured')
 p.add_argument('--evidence-dir')
 a=p.parse_args(argv)
 try:
  with Path(a.request).open('rb') as f:wire=f.read(MAX_REQUEST+1)
  tape=None
  if a.entropy_file is not None:
   with Path(a.entropy_file).open('rb') as f:tape=f.read(MAX_ENTROPY+1)
  result=invoke(wire,a.installation,a.installation_sha256,
   entropy_mode='provided' if a.entropy_file is not None else 'os',entropy=tape,resume=a.resume,
   timeout_seconds=a.timeout,evidence_dir=a.evidence_dir,predeclared=a.predeclared,fixed_degree_null=a.fixed_degree_null,trust_uniform_bytes=a.trust_uniform_bytes)
 except OSError as e:result={'status':'blocked','error':'request_or_entropy_read_failure','detail':str(e),
  'assurance':None,'scientific_rejection_authorized':False,'tv_assurance_authorized':False,'ideal_randomness_claim':False,'graph_refinement_binary_claim':False,'conditional_model_eligibility':False}
 print(json.dumps(result,indent=2))
 return 0 if result['status'] in ('completed_unassured_native_sampling','completed_conditional_native_sampling') else 2
if __name__=='__main__':raise SystemExit(main())
