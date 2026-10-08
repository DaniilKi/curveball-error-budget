"""Local launcher without installation; normal Python and isolated runtime supported."""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent/'src'))
from degree_null.cli import main
if __name__=='__main__':raise SystemExit(main())
