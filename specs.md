### Specs
* `theorems.dfy`
* `theorem_defs.dfy`
* `node_auxiliary_functions.dfy`:     
    * fromBlockChainToRawBlockchain
    * fromBlockToRawBlock
    * recoverSigned*Author: those functions should only be used in trusted portions
    * f
* `types.dfy`: 
    * everything except NodeState and Optional (the blockchain field under NodeState is part of spec, but others is not)
* `distributed_system.dfy`
* `network.dfy`
* `adversary.dfy`
* `common_functions.dfy`:
    * isUniqueSequence
    * seqToSet
    * isMsgWithSignedPayload
    * recoverSignature
    * signed*Payloads
    * getCommitSeals
* `trace_defs.dfy`
    * Trace
    * validTrace

### Trusted but Part of Implementation
Under this category, the function is defined for the implementation of the protocol, but it involves some axioms due to unspecified behavior.

`node_auxiliary_functions`:
    * Cryptographic primitives: digest, sign*, recoverSigned*
    * validatorsOnRawBlockchain
    * validateRawEthereumBlock
`axioms.dfy`:
    * axiomRawValidatorsNeverChange

### Unimplemented Function
`node_auxiliary_functions`:
    * minSet, getNewBlock


