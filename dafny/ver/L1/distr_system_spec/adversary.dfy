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

    predicate AdvPrepare(preparePayload: SignedPrepare, c: Configuration, messagesReceived: set<QbftMessage>, a: Adversary) {
        || preparePayload in signedPreparePayloads(messagesReceived)
        || !(recoverSignedPrepareAuthor(preparePayload) in seqToSet(c.nodes) - a.byz)
    }

    predicate AdvBlock(b: Block, c: Configuration, messagesReceived: set<QbftMessage>, a: Adversary) {
        forall cs | cs in b.header.commitSeals ::
            || (cs in getCommitSeals(messagesReceived))
            || !(recoverSignedHashAuthor(hashBlockForCommitSeal(b),cs) in seqToSet(c.nodes) - a.byz)
    }

    predicate AdvRoundChange(m: SignedRoundChange, c: Configuration, messagesReceived: set<QbftMessage>, a: Adversary) {
        || m in signedRoundChangePayloads(messagesReceived)
        || !(recoverSignedRoundChangeAuthor(m) in seqToSet(c.nodes) - a.byz) 
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
                                || !(recoverSignedProposalAuthor(m.message.proposalPayload) in seqToSet(c.nodes) - a.byz)
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
                            && !(recoverSignature(m.message) in seqToSet(c.nodes) - a.byz)
                            &&  var uPayload := m.message.commitPayload.unsignedPayload;
                                var cs := uPayload.commitSeal;
                            && (
                                || (cs in getCommitSeals(messagesReceived))
                                || (forall b :: !(recoverSignedHashAuthor(hashBlockForCommitSeal(b), cs) in seqToSet(c.nodes) - a.byz))
                                // not sure whether this is implementable (by public key cryptography)
                            )
                        )                                        
                        || (
                            && m.message.NewBlock?
                            && AdvBlock(m.message.block, c, messagesReceived, a)
                        )
        )
    }    

}