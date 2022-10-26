# HOL4P4

HOL4P4 is a small-step, heapless formalisation of the P4 language implemented in HOL4. The syntax and semantics is written in the Ott metalanguage, which co-organizes export of definitions to multiple interactive theorem provers.

## Content

* [Proof of determinism for the semantics](hol/deterScript.sml)
* [Executable semantics](hol/p4_exec_semScript.sml)
  * Soundness proof - for [expression](hol/p4_exec_sem_e_soundnessScript.sml), [statement](hol/p4_exec_sem_stmt_soundnessScript.sml), [frame](hol/p4_exec_sem_frames_soundnessScript.sml) and [architecture](hol/p4_exec_sem_arch_soundnessScript.sml) semantics
* [Verification, testing and debugging tools](hol/p4_testLib.sml)
* Examples: [concrete execution](test-vss.sml), [interference-freeness](test-vss-ttl.sml)

## Installation

Installation instructions for Ubuntu can be found in [INSTALL.md](INSTALL.md).

## Papers

A. Alshnakat, D. Lundberg, R. Guanciale, M. Dam and K. Palmskog, "HOL4P4: Semantics for a Verified Data Plane", in P4 Workshop in Europe (EuroP4 '22), 2022.
