 /**
 * Copyright © 2021 EEA Inc. 
 *
 * This document is available under the terms of the Apache 2.0 License
 * (http://www.apache.org/licenses/LICENSE-2.0.html)
 */
module L1_SpecTypes
{
    /** =======================================================================
     * UNDEFINED TYPES
     *
     * This section includes the declarations of those types that are left
     * undefined in this specification.
     ========================================================================*/
    type Address = int

    type BlockBody = int

    type Transaction = string

    type Hash = int
    
    type Signature = int

    /** =======================================================================
     * BLOCKCHAIN TYPES
     *
     * This section includes the declaration of the types that are related to
     * sequences of blocks.
     * 
     * - The only difference between `Block` and `RawBlock` is that the header
     *   of a `RawBlock` does not include the field `commitSeals`.
     ========================================================================*/
    type Blockchain = seq<Block>

    datatype BlockHeader = BlockHeader (
        proposer: Address, 
        roundNumber: nat,
        commitSeals: set<Signature>,
        height:nat,
        timestamp: nat
    )

    datatype Block = Block (
        header: BlockHeader,
        body: BlockBody,
        transactions: seq<Transaction>
    )

    type RawBlockchain = seq<RawBlock>     

    datatype RawBlockHeader = RawBlockHeader (
        proposer: Address,
        height:nat,
        timestamp: nat
    ) 

    datatype RawBlock = RawBlock (
        header: RawBlockHeader,
        body: BlockBody,
        transactions: seq<Transaction>
    )     

    /** =======================================================================
     * MESSAGE TYPES
     *
     * This section includes the declaration of those types that are used to
     * define the various QBFT messages.
     *
     * - `Unsigned*` types represent messages without signature.
     * - `Signed*` types represent messages carrying a signature.
     * - `QbtMessage` is the datatype representing any QBFT message.
     * - `QbtMessageWithRecipient` is the datatype used to indicate which node
     *   a message should be sent to.
     *
     ========================================================================*/
    datatype UnsignedProposal = UnsignedProposal (
        height:nat, 
        round:nat, 
        digest: Hash
    )

    datatype UnsignedPrepare = UnsignedPrepare (
        height:nat, 
        round:nat, 
        digest:Hash
    )

    datatype UnsignedCommit = UnsignedCommit (
        height:nat, 
        round:nat, 
        commitSeal: Signature,
        digest:Hash
    )

    datatype UnsignedRoundChange = UnsignedRoundChange (
        height:nat, 
        round:nat, 
        preparedValue: Optional<Hash>, 
        preparedRound: Optional<nat>
    )

    datatype SignedProposal = SignedProposal (
        unsignedPayload: UnsignedProposal,
        signature: Signature
    )

    datatype SignedPrepare = SignedPrepare(
        unsignedPayload: UnsignedPrepare,
        signature: Signature
    )

    datatype SignedCommit = SignedCommit(
        unsignedPayload: UnsignedCommit,
        signature: Signature
    )

    datatype SignedRoundChange = SignedRoundChange(
        unsignedPayload: UnsignedRoundChange,
        signature: Signature
    )

    datatype QbftMessage =
        | Proposal(
            proposalPayload: SignedProposal,
            proposedBlock:Block, 
            proposalJustification: set<SignedRoundChange>, // this is the newest value
            roundChangeJustification: set<SignedPrepare> // this is indeed a prepared value
        )
        | Prepare(
            preparePayload: SignedPrepare
        )
        | Commit(
            commitPayload: SignedCommit
        )
        | RoundChange(
            roundChangePayload: SignedRoundChange,
            proposedBlockForNextRound: Optional<Block>, // not taking advantage of digest here?
            roundChangeJustification: set<SignedPrepare> // this is indeed a prepared value
        )
        | NewBlock(
            block: Block
        )

    datatype QbftMessageWithRecipient = QbftMessageWithRecipient(
        message: QbftMessage,
        recipient: Address
    )    

    /** =======================================================================
     * STATE TYPES
     *
     * This section includes the declaration of the types that are used in the
     * representation of the state of a QBFT node.
     *
     ========================================================================*/

    /**
     * This type groups the configuration parameters for a QBFT network.
     */
    datatype Configuration = Configuration(
        nodes: seq<Address>, // Ordered set of the ids of all the nodes
        genesisBlock : Block,
        blockTime: nat
    )

    /**
     * This type represents the state associated with any QBFT node.
     */
    datatype NodeState = NodeState (
        blockchain: Blockchain,
        round: nat,
        localTime: nat,
        id: Address,
        configuration: Configuration,
        messagesReceived: set<QbftMessage>,
        proposalAcceptedForCurrentRound: Optional<QbftMessage>,
        lastPreparedBlock: Optional<Block>,
        lastPreparedRound: Optional<nat>,
        timeLastRoundStart: nat
    )

    /** =======================================================================
     * GENERAL TYPES
     *
     * This section includes the declaration of the types that have general
     * usage.
     *
     ========================================================================*/
    /**
     * This type is used to represent a single value that may be not present.
     */
    datatype Optional<T> = Optional(value:T) | None          

}