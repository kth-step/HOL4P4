# HOL4P4

HOL4P4 is a small-step, heapless formalisation and a type system of the P4 language implemented in HOL4. The syntax and semantics is written in the Ott metalanguage, which co-organizes export of definitions to multiple interactive theorem provers.

## Content

* [Semantics](ott/p4_sem.ott), more specifically:
  * [Expression](ott/p4_sem.ott#L2494-L2847) 
  * [Statement](ott/p4_sem.ott#L2858-L2986) 
  * [P4 state](ott/p4_sem.ott#L2994-L3026) 
  * [Architecture-Level](ott/p4_sem.ott#L3033-L3102) 
  * [Concurrent Architecture-Level](ott/p4_sem.ott#L3116-L3132) 

* [Proof of determinism for the semantics](hol/p4_deterScript.sml)


* [Type system](ott/p4_types.ott), more specifically:
  * [Value](ott/p4_types.ott#L402-L447)
  * [Expression](ott/p4_types.ott#L542-L661)
  * [Statement](ott/p4_types.ott#L693-L780)
  * [Single frame](ott/p4_types.ott#L855-L896)
  * [P4 state](ott/p4_types.ott#L1454-L1484)


* Type preservation proof for:
  * [Expression](hol/p4_e_subject_reductionScript.sml#L5262-L6682)
  * [Statement](hol/p4_stmt_subject_reductionScript.sml#L4499-L4598)
  * [P4 state](hol/p4_frames_subject_reductionScript.sml#L2958-L3440)

* Type progress proof for:
  * [Expression](hol/p4_e_progressScript.sml#L1479-L2367)
  * [Statement](hol/p4_stmt_progressScript.sml#L885-L923)
  * [P4 state](hol/p4_frames_progressScript.sml#L996-L1295)


* [Executable semantics](hol/p4_exec_semScript.sml), more specifically:
  * [Expression](hol/p4_exec_semScript.sml#L279-L457)
  * [Statement](hol/p4_exec_semScript.sml#L504-L671)
  * [Frame](hol/p4_exec_semScript.sml#L2171-L2249)
  * [Architecture](hol/p4_exec_semScript.sml#L2324-L2424)

* Proof of soundness of the executable semantics:
  * [Expression](hol/p4_exec_sem_e_soundnessScript.sml#L755-L833)
  * [Statement](hol/p4_exec_sem_stmt_soundnessScript.sml#L458-L475)
  * [Frame](hol/p4_exec_sem_frames_soundnessScript.sml#L16-L155)
  * [Architecture](hol/p4_exec_sem_arch_soundnessScript.sml#L17-L268)

* [.p4 import tool (using Petr4 as backend)](hol/p4_from_json)

* Case studies: 
  * Pipeline interference: [Concrete execution](hol/p4_from_json/concurrency_tests/concur1_interferenceScript.sml), [Concurrency theory](hol/p4_concurrentScript.sml)
  * VSS: [Concrete execution](hol/test-vss.sml), [Data non-interference](hol/test-vss-ttl.sml)


* Architecture instantiations
  * [eBPF](hol/p4_ebpfScript.sml)
  * [VSS](hol/p4_vssScript.sml)
  * [V1Model](hol/p4_v1modelScript.sml)


* [Verification, testing and debugging tools](hol/p4_testLib.sml)


## Installation
To set up the development environment, follow instructions in [INSTALL.md](INSTALL.md).

## Papers

A. Alshnakat, D. Lundberg, R. Guanciale, M. Dam and K. Palmskog, "HOL4P4: Semantics for a Verified Data Plane", in P4 Workshop in Europe (EuroP4 '22), 2022.

A. Alshnakat, D. Lundberg, R. Guanciale, and M. Dam "HOL4P4: Mechanized Small-Step Semantics for P4", to appear in (OOPSLA '24).
