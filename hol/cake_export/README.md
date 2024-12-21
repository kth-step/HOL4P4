This directory contains facilities to compile P4 programs to binary using CakeML. Currently, this uses the unverified export mechanism.

The translations from HOL4 uses the version of CakeML at commit [`d4f0662af`](https://github.com/CakeML/cakeml/tree/d4f0662af8596e6f964e54519b206be44e5b9f71), which for our use case appears to be compatible with the Trindemossen-1 release of HOL4 currently used for HOL4P4 (no CakeML release is compatible with Trindemossen-1).

The compilation of the CakeML S-expression obtained from translation uses the release [v2702](https://github.com/CakeML/cakeml/releases/tag/v2702) of CakeML - note that this release is later than the commit used for obtaining the S-expression in the first place. You may want to consider using release [v2419](https://github.com/CakeML/cakeml/releases/tag/v2419) if any issue arises at this step, since this is closer to the commit being used for translation.

To download this release, run in this directory e.g.:

```bash
wget https://github.com/CakeML/cakeml/releases/download/v2702/cake-x64-64.tar.gz
tar -xvf cake-x64-64.tar.gz -C test/ --strip-components=1
rm cake-x64-64.tar.gz
cd test && make cake && cd ..
```

Two example programs are featured: a tiny program from the symbolic executor in `p4_conditional_cakeProgScript.sml` and the VSS example in `p4_vss_example_cakeProgScript.sml`. To compile your own programs to binary, use the HOL4P4 import tool to obtain the static environment `actx` and initial state `astate`, then supply a suitably large amount of maximum steps to `n_max`. Your programs may feature additional externs which have not been translated yet - in that case, you will have to add the translations in the corresponding `p4_exec_sem_ARCH_cakeProgScript.sml`, where "`ARCH`" is replaced by your architecture.

To test the translation of the VSS example, after downloading the necessary CakeML release run:

```bash
./vss_test.sh
```
