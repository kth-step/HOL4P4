# HOL4P4

[![Build Status][workflow-badge]][workflow-link]

[workflow-badge]: https://github.com/kth-step/HOL4P4/actions/workflows/build.yaml/badge.svg?branch=main
[workflow-link]: https://github.com/kth-step/HOL4P4/actions/workflows/build.yaml

HOL4P4 is a small-step, heapless formalisation and a type system of the P4 language implemented in HOL4. The syntax and semantics is written in the Ott metalanguage, which co-organizes export of definitions to multiple interactive theorem provers.

## Content

* [Semantics](ott/p4_sem.ott) and [type system](ott/p4_types.ott) in Ott
* [Proof of determinism for the semantics](hol/p4_deterScript.sml)
* [Type preservation](hol/p4_frames_subject_reductionScript.sml) and [progress](hol/p4_frames_progressScript.sml) proofs up to the frame level
* [Executable semantics](hol/p4_exec_semScript.sml) with [soundness proof](hol/p4_exec_sem_arch_soundnessScript.sml)
* [.p4 import tool (using Petr4 as backend)](hol/p4_from_json)
* [Symbolic execution tool](hol/symb_exec)
* Architecture models:
  * [eBPF](hol/p4_ebpfScript.sml)
  * [VSS](hol/p4_vssScript.sml)
  * [V1Model](hol/p4_v1modelScript.sml)

## Installation
Follow the instructions in [INSTALL.md](INSTALL.md). The [CI scripts](scripts) may also provide some guidance.

## Papers

* A. Alshnakat, D. Lundberg, R. Guanciale, M. Dam and K. Palmskog, ["HOL4P4: Semantics for a Verified Data Plane"](https://doi.org/10.1145/3565475.3569081) (EuroP4 '22).
* A. Alshnakat, D. Lundberg, R. Guanciale, and M. Dam, ["HOL4P4: Mechanized Small-Step Semantics for P4"](https://doi.org/10.1145/3649819) (OOPSLA '24).
* D. Lundberg, R. Guanciale, and M. Dam, ["Proof-Producing Symbolic Execution for P4"](https://doi.org/10.1007/978-3-031-86695-1_5) (VSTTE '24).

## License

This project is distributed under the terms of the Apache License (Version 2.0), and the BSD 3-Clause License; users may pick which license to apply.

See [`COPYRIGHT`](COPYRIGHT), [`LICENSE-APACHE`](LICENSE-APACHE) and [`LICENSE-BSD`](LICENSE-BSD) for details.
