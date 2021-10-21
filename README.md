This repository contains our TLA+ specifications for Skeen's atomic multicast protocol, and configuration files to check this protocol with the model checkers TLC and APALACHE. The specifications are stored in two folders spec_old_type_annotations and spec_intint_t. The first is with type annotations of Apalache version 0.15.2, and the latter is with type annotations of Apalache version 0.16.2.
  - File skeen.tla is the main one that specifies the Skeen protocol
  - Files integrity.tla, termination.tla, total_order.tla, validity.tla describe the properties Integrity, Termination, Total Order, and Validity
  - Files iinv.tla, toinv.tla, vinv.tla describe inductive invariants that implies the properties Integrity, Termination, and Total Order, respectively.
  - Files in folder config describe the cases in our experiments.
