# Dependency licensing and redistribution

This repository and its pure-Python package artifacts distribute authored wrapper code, documentation and synthetic examples under Apache-2.0. They do **not** bundle third-party runtimes, compiled libraries or dependency wheels.

Installed dependencies retain their upstream licenses:

- NetworKit11.2.2: MIT; [upstream license](https://github.com/networkit/networkit/blob/11.2.2/License.txt).
- psutil7.2.2: BSD-3-Clause.
- NetworkX3.7: BSD-3-Clause.
- tabulate0.10.0: MIT.
- NumPy2.5.3: its wheel metadata declares BSD-3-Clause, 0BSD, MIT, Zlib and CC0-1.0 components.
- SciPy1.18.1: BSD-3-Clause core with additional bundled-library notices in its wheel. Read those notices when redistributing its binaries.
- setuptools is a build dependency installed separately.

The lock file pins the pilot environment. Pip obtains dependencies from their own distributions and notices. This list does not replace upstream license texts for anyone who chooses to redistribute dependency binaries. NetworKit algorithm citations are retained in NOTICE and the documentation.

Pinned NumPy2.5.3, SciPy1.18.1 and NetworkX3.7 require Python>=3.12; NetworkX also excludes Python3.14.1. Package metadata uses that qualified range. The measured and tested environment was Python3.14.8 on Windows AMD64. Other versions/platforms require validation and suitable binary-wheel availability.
