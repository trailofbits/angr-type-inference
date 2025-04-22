# Fork note:

This is a fork of the [angr project](https://github.com/angr/angr) for experimentation. This code is experimental.

The fork expriments with an algebraic subtyping-based type solver in Clinic/Typehoon. 
Further details are available in the paper: [BinSub: The Simple Essence of Polymorphic Type Inference for Machine Code](https://arxiv.org/abs/2409.01841).

The original README is below. There are two relevant branches:
* [ian/updated-fork](https://github.com/trailofbits/angr-type-inference/tree/ian/updated-fork) this branch was used for the paper's experiments.
* [ian/depth-subtyping](https://github.com/trailofbits/angr-type-inference/tree/ian/depth-subtyping) some further experiments where width subtyping is eliminated internal to functions

If you reference this work please cite the paper as follows:

```bibtex
@inproceedings{smith_binsub_2025,
	address = {Cham},
	title = {{BinSub}: {The} {Simple} {Essence} of {Polymorphic} {Type} {Inference} for {Machine} {Code}},
	isbn = {978-3-031-74776-2},
	shorttitle = {{BinSub}},
	doi = {10.1007/978-3-031-74776-2_17},
	abstract = {Recovering high-level type information in binaries is a key task in reverse engineering and binary analysis. Binaries contain very little explicit type information. The structure of binary code is incredibly flexible allowing for ad-hoc subtyping and polymorphism. Prior work has shown that precise type inference on binary code requires expressive subtyping and polymorphism.},
	language = {en},
	booktitle = {Static {Analysis}},
	publisher = {Springer Nature Switzerland},
	author = {Smith, Ian},
	editor = {Giacobazzi, Roberto and Gorla, Alessandra},
	year = {2025},
	pages = {425--450},
}
```
# angr

[![Latest Release](https://img.shields.io/pypi/v/angr.svg)](https://pypi.python.org/pypi/angr/)
[![Python Version](https://img.shields.io/pypi/pyversions/angr)](https://pypi.python.org/pypi/angr/)
[![PyPI Statistics](https://img.shields.io/pypi/dm/angr.svg)](https://pypistats.org/packages/angr)
[![License](https://img.shields.io/github/license/angr/angr.svg)](https://github.com/angr/angr/blob/master/LICENSE)

angr is a platform-agnostic binary analysis framework.
It is brought to you by [the Computer Security Lab at UC Santa Barbara](https://seclab.cs.ucsb.edu), [SEFCOM at Arizona State University](https://sefcom.asu.edu), their associated CTF team, [Shellphish](https://shellphish.net), the open source community, and **[@rhelmot](https://github.com/rhelmot)**.

## Project Links
Homepage: https://angr.io

Project repository: https://github.com/angr/angr

Documentation: https://docs.angr.io

API Documentation: https://api.angr.io/en/latest/

## What is angr?

angr is a suite of Python 3 libraries that let you load a binary and do a lot of cool things to it:

- Disassembly and intermediate-representation lifting
- Program instrumentation
- Symbolic execution
- Control-flow analysis
- Data-dependency analysis
- Value-set analysis (VSA)
- Decompilation

The most common angr operation is loading a binary: `p = angr.Project('/bin/bash')` If you do this in an enhanced REPL like IPython, you can use tab-autocomplete to browse the [top-level-accessible methods](https://docs.angr.io/docs/toplevel) and their docstrings.

The short version of "how to install angr" is `mkvirtualenv --python=$(which python3) angr && python -m pip install angr`.

## Example

angr does a lot of binary analysis stuff.
To get you started, here's a simple example of using symbolic execution to get a flag in a CTF challenge.

```python
import angr

project = angr.Project("angr-doc/examples/defcamp_r100/r100", auto_load_libs=False)

@project.hook(0x400844)
def print_flag(state):
    print("FLAG SHOULD BE:", state.posix.dumps(0))
    project.terminate_execution()

project.execute()
```

# Quick Start

- [Install Instructions](https://docs.angr.io/introductory-errata/install)
- Documentation as [HTML](https://docs.angr.io/) and sources in the angr [Github repository](https://github.com/angr/angr/tree/master/docs)
- Dive right in: [top-level-accessible methods](https://docs.angr.io/core-concepts/toplevel)
- [Examples using angr to solve CTF challenges](https://docs.angr.io/examples).
- [API Reference](https://angr.io/api-doc/)
- [awesome-angr repo](https://github.com/degrigis/awesome-angr)
