"""Print source-only ordered replay plan; deliberately never launches compiler."""
from pathlib import Path
import argparse,json
p=argparse.ArgumentParser();p.add_argument("--print-plan",action="store_true",required=True);p.parse_args()
print(json.dumps(json.loads((Path(__file__).parent/"replay-plan.json").read_bytes()),indent=2))
