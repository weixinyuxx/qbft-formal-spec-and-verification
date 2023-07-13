include "../../../spec/L1/types.dfy"
include "common_functions.dfy"
include "network.dfy"
include "../../../spec/L1/node_auxiliary_functions.dfy"

module L1_Adversary
{
    import opened L1_SpecTypes
    import opened L1_SpecNetwork
    import opened L1_AuxiliaryFunctionsAndLemmas
    import opened L1_CommonFunctions
        
    datatype Adversary = Adversary (
        messagesReceived: set<QbftMessage>,
        byz: set<Address>
    )

    predicate AdversaryInit(a:Adversary, configuration:Configuration)
    {
        && a.messagesReceived == {}
        &&  a.byz <= seqToSet(configuration.nodes)
        && |a.byz| <= f(|validators([configuration.genesisBlock])|)
    }    

    predicate isHonestByConfig(c: Configuration, a: Adversary, address: Address) {
        address in (seqToSet(c.nodes) - a.byz)
    }

    predicate AdvPrepare(preparePayload: SignedPrepare, c: Configuration, messagesReceived: set<QbftMessage>, a: Adversary) {
        || preparePayload in signedPreparePayloads(messagesReceived)
        || !isHonestByConfig(c, a, recoverSignedPrepareAuthor(preparePayload))
    }

    predicate AdvBlock(b: Block, c: Configuration, messagesReceived: set<QbftMessage>, a: Adversary) {
        forall cs | cs in b.header.commitSeals ::
            || (cs in getCommitSeals(messagesReceived))
            || (forall block:Block :: !isHonestByConfig(c, a, recoverSignedHashAuthor(hashBlockForCommitSeal(block),cs)))
    }

    predicate AdvRoundChange(m: SignedRoundChange, c: Configuration, messagesReceived: set<QbftMessage>, a: Adversary) {
        || m in signedRoundChangePayloads(messagesReceived)
        || !isHonestByConfig(c, a, recoverSignedRoundChangeAuthor(m)) 
    }

    
    predicate AdversaryNext(
        c: Configuration,
        a: Adversary, 
        inQbftMessages: set<QbftMessage>, 
        a': Adversary,
        outQbftMessages: set<QbftMessageWithRecipient>
        )
    {
        var messagesReceived := a.messagesReceived + inQbftMessages;

        && a' == a.(messagesReceived := messagesReceived)
        && (forall m | m in outQbftMessages ::
                        || m.message in messagesReceived
                        || (
                            && m.message.Proposal?
                            && (
                                || m.message.proposalPayload in signedProposalPayloads(messagesReceived)
                                || !isHonestByConfig(c, a, recoverSignedProposalAuthor(m.message.proposalPayload))
                            )
                            && AdvBlock(m.message.proposedBlock, c, messagesReceived, a)
                            && (forall m' | m' in m.message.proposalJustification ::
                                AdvRoundChange(m', c, messagesReceived, a)
                            )
                            && (forall m' | m' in m.message.roundChangeJustification ::
                                AdvPrepare(m', c, messagesReceived, a)
                            )
                        )
                        || (
                            && m.message.RoundChange?
                            && AdvRoundChange(m.message.roundChangePayload, c, messagesReceived, a)
                            && (
                                || m.message.proposedBlockForNextRound.None?
                                || AdvBlock(m.message.proposedBlockForNextRound.value, c, messagesReceived, a)
                            )               
                            && (forall m' | m' in m.message.roundChangeJustification ::
                                    AdvPrepare(m', c, messagesReceived, a)
                            )
                        ) 
                        || (
                            && m.message.Prepare?
                            && AdvPrepare(m.message.preparePayload, c, messagesReceived, a)
                        )
                        || (
                            && m.message.Commit?
                            && !isHonestByConfig(c, a, recoverSignature(m.message))
                            &&  var uPayload := m.message.commitPayload.unsignedPayload;
                                var cs := uPayload.commitSeal;
                            && (
                                || (cs in getCommitSeals(messagesReceived))
                                || (forall b :: !isHonestByConfig(c, a, recoverSignedHashAuthor(hashBlockForCommitSeal(b), cs)))                            )
                        )                                        
                        || (
                            && m.message.NewBlock?
                            && AdvBlock(m.message.block, c, messagesReceived, a)
                        )
        )
    }    

}