"""Private research prototype for degree-preserving network comparisons."""
__version__ = "0.4.0"
from .inputs import read_network
from .jobs import make_plan, run_job, resume_job
from .planning import CurveballTradePlan, curveball_trade_plan
from .networkit_graph import NetworkitGraphTradePlan, curveball_trade_plan_from_networkit
