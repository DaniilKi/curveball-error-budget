"""Read saved descriptive evidence; never execute a study or sampler."""
import argparse
import json
import sys
from .study import load_pwr002,render_pwr002


def main(argv=None):
    parser=argparse.ArgumentParser(description='Read exact reviewed PWR-002 descriptive evidence; no sampling or scientific authorization.')
    parser.add_argument('--format',choices=['markdown','json'],default='markdown')
    args=parser.parse_args(argv)
    try:
        evidence=load_pwr002()
        # Text stdout adds the platform newline once. Preserve report/API bytes,
        # but normalize the Markdown stream before Windows LF translation.
        output=json.dumps(evidence,indent=2) if args.format=='json' else render_pwr002(evidence).replace('\r\n','\n')
        print(output,end='\n' if args.format=='json' else '')
        return 0
    except (OSError,ValueError,KeyError,TypeError) as exc:
        print(json.dumps({'status':'blocked','error':str(exc),'scientific_runtime_authorization_promoted':False}),file=sys.stderr)
        return 2


if __name__=='__main__':raise SystemExit(main())
