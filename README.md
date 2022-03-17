# P4 SOS for secure programmable networks
## Background
P4 is an open-source domain-specific language (DSL) that allows expressing the network packet behaviour that occurs in the packet forwarding plane i.e. data plane. The programmable data plane permits the user to define the control as a Software-Defined Network (SDN), which offers a great deal of flexibility in multiple applications; for instance, 5G and integrating clouds.
This type of flexibility might lead to multiple security challenges; for example, a failure in a centralized switch service (CSS) network component can lead the entire network to collapse, unless an alternative switch is on standby to take the place of the faulty switch.
To ensure higher security guarantees, one method is to formalize Small-step Operational Semantics (SOS) and prove properties that are relevant to a real-time switch.

## Features
### Supported
Base types:
* Booleans
* Fixed-width bitstrings with widths up to 64
* Errors
* Strings

Derived types:
* Headers
* Structs

Expressions:
* Constants
* Variables
* Arithmetic operations
* Function (including extern) calls
* Selects

Statements:
* Assignments
* Method (including extern) calls
* Conditional
* Declarations
* Blocks
* Return
* Verify
* Transition
* Apply

Programmable blocks:
* Parsers
* Control blocks

### Partially Supported

Expressions:
* Bitslicing
* Concatenation

### Not Supported Yet
Base types:
* Fixed-width signed bitstrings
* Dynamically sized integers (`varbit`)
* Arbitrary-sized constants

Derived types:
* Enumeration types
* Header stacks
* Header unions
* Tuples
* Sets

Expressions:
* Conditional expression
* Casts
* Operations on unimplemented types

Statements:
* Exit
* Switch

Type specialization

Specific architecture support:
* Tofino (TNA)

## Versioning
Currently, the developer team is working on v0.2, which will include a proofs of determinism, subject reduction, termination as well as soundness and completeness of the executable semantics.

## Prerequisites
The project has the following dependencies, listed with recommended versions:

1. [Ott 0.31](https://github.com/ott-lang/ott/tree/0.31)
2. [HOL4 (kananaskis-14)](https://github.com/HOL-Theorem-Prover/HOL/tree/kananaskis-14)

## Authors

* **Mads Dam, Prof.**
* **Roberto Guanciale, Assoc. Prof.**
* **Karl Palmskog, Postdoc**
* **Didrik Lundberg, PhD student**
* **Anoud Alshnakat, PhD student**
