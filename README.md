# HOL4P4

HOL4P4 is a small-step, heapless formalisation and a type system of the P4 language implemented in HOL4. The syntax and semantics is written in the Ott metalanguage, which co-organizes export of definitions to multiple interactive theorem provers.

## Content

* [Semantics](ott/p4_sem.ott)
  * [Expression](ott/p4_sem.ott#L2494-L2847) 
  * [Statement](ott/p4_sem.ott#L2858-L2896) 
  * [Frame](ott/p4_sem.ott#L2994-L3026) 
  * [Architecture](ott/p4_sem.ott#L3033-L3102) 
  * [Concurrency](ott/p4_sem.ott#L3116-L3132) 

* [Executable semantics](hol/p4_exec_semScript.sml)
  * [Expression](hol/p4_exec_semScript.sml#L279-L259) 
  * [Statement](hol/p4_exec_semScript.sml#L504-L671) 
  * [Frame](hol/p4_exec_semScript.sml#L2171-L2249) 
  * [Architecture](hol/p4_exec_semScript.sml#L2342-L2424) 

* [Type System](ott/p4_types.ott)

* [Proof of determinism for the semantics](hol/deterScript.sml)

  * Soundness proof - for [expression](hol/p4_exec_sem_e_soundnessScript.sml), [statement](hol/p4_exec_sem_stmt_soundnessScript.sml), [frame](hol/p4_exec_sem_frames_soundnessScript.sml) and [architecture](hol/p4_exec_sem_arch_soundnessScript.sml) semantics
* [Verification, testing and debugging tools](hol/p4_testLib.sml)
* Examples: [concrete execution](hol/test-vss.sml), [non-interference](hol/test-vss-ttl.sml)

## Installation

Installation instructions for Ubuntu can be found in [INSTALL.md](INSTALL.md).

## Papers

A. Alshnakat, D. Lundberg, R. Guanciale, M. Dam and K. Palmskog, "HOL4P4: Semantics for a Verified Data Plane", in P4 Workshop in Europe (EuroP4 '22), 2022.
