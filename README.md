# HOL4P4

HOL4P4 is a small-step, heapless formalisation and a type system of the P4 language implemented in HOL4. The syntax and semantics is written in the Ott metalanguage, which co-organizes export of definitions to multiple interactive theorem provers.

## Content

* [Semantics](ott/p4_sem.ott) and [type system](ott/p4_types.ott) in Ott
* [Proof of determinism for the semantics](hol/p4_deterScript.sml)
* [Type preservation](hol/p4_frames_subject_reductionScript.sml) and [progress](hol/p4_frames_progressScript.sml) proofs up to the frame level
* [Executable semantics](hol/p4_exec_semScript.sml) with [soundness proof](hol/p4_exec_sem_arch_soundnessScript.sml)
* [.p4 import tool (using Petr4 as backend)](hol/p4_from_json)
* [Symbolic execution tool](hol/symb_exec)
* [Extraction and compilation of executable semantics to software switch](hol/retrofit_sem) and [optimized version](hol/cake_sem)
* Architecture models:
  * [eBPF](hol/p4_ebpfScript.sml)
  * [VSS](hol/p4_vssScript.sml)
  * [V1Model](hol/p4_v1modelScript.sml)


## Installation
To set up the development environment, follow the instructions in [INSTALL.md](INSTALL.md). The [CI scripts](scripts) may also provide some guidance.

Additional tools for benchmarking can be found in [this](https://github.com/kth-step/swswitch-perf.git) repository.


## Papers

* A. Alshnakat, D. Lundberg, R. Guanciale, M. Dam and K. Palmskog, ["HOL4P4: Semantics for a Verified Data Plane"](https://doi.org/10.1145/3565475.3569081) (EuroP4 '22).
* A. Alshnakat, D. Lundberg, R. Guanciale, and M. Dam, ["HOL4P4: Mechanized Small-Step Semantics for P4"](https://doi.org/10.1145/3649819) (OOPSLA '24).
* D. Lundberg, R. Guanciale, and M. Dam, ["Proof-Producing Symbolic Execution for P4"](https://doi.org/10.1007/978-3-031-86695-1_5) (VSTTE '24).
* D. Lundberg and R. Guanciale, "HOL4P4.EXE: A Formally Verified P4 Software Switch" (VSTTE '25).
