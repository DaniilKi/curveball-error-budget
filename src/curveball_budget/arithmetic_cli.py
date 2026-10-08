"""Check one canonical arithmetic request using an explicitly pinned installation."""
from pathlib import Path
import argparse
import json
from .arithmetic_invocation import invoke

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--installation',type=Path,required=True)
    parser.add_argument('--installation-sha256',required=True)
    parser.add_argument('--request',type=Path,required=True)
    parser.add_argument('--backend',default='lean_arithmetic')
    parser.add_argument('--resume',action='store_true')
    args=parser.parse_args()
    try:
        with args.request.open('rb') as stream:wire=stream.read(1025)
        receipt=invoke(wire,args.installation,args.installation_sha256,
                       backend=args.backend,resume=args.resume)
    except OSError as exc:
        receipt={'status':'blocked','error':'request_read_failure','detail':str(exc),
                 'assurance':None,'scientific_rejection_authorized':False}
    print(json.dumps(receipt,indent=2))
    # False is a successfully computed arithmetic predicate, not a scientific
    # nonrejection certificate. Both computed values exit zero.
    return 0 if receipt['status']=='completed' else 2

if __name__=='__main__':raise SystemExit(main())
