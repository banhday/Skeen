This repository contains our TLA+ specifications for Skeen's atomic multicast protocol, and configuration files to check this protocol with the model checkers TLC and APALACHE. The specifications are stored in folder spec, and the configuration files are stored in folder config.
  - File skeen.tla is the main one that specifies the Skeen protocol
  - Files integrity.tla, termination.tla, total_order.tla, validity.tla describe the properties Integrity, Termination, Total Order, and Validity
  - Files iinv.tla, toinv.tla, vinv.tla describe inductive invariants that implies the properties Integrity, Termination, and Total Order, respectively.
  - Files in folder config describe the cases in our experiments.
