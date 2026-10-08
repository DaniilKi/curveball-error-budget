"""Checkout entry for the source-only native sampling command."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent/'src'))
from curveball_budget.sampling_cli import main
if __name__=='__main__':raise SystemExit(main())
