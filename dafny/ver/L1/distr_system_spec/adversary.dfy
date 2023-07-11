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

    predicate AdversaryNext(
        a: Adversary, 
        inQbftMessages: set<QbftMessage>, 
        a': Adversary,
        outQbftMessages: set<QbftMessageWithRecipient>
        )
    {
        var messagesReceived := a.messagesReceived + inQbftMessages;

        && a' == a.(messagesReceived := messagesReceived)
        // *** adversary should also be able to send other messages (unsigned or incorrectly signed)
        // *** if the implementation does not check signature (and only read the author), the proof will still pass
        && (forall m | m in outQbftMessages ::
                        || m.message in messagesReceived
                        || (
                            && m.message.Proposal?
                            && (
                                || m.message.proposalPayload in signedProposalPayloads(messagesReceived)
                                || recoverSignedProposalAuthor(m.message.proposalPayload) in a.byz // random signature
                                // Block cannot be properly signed
                            )
                            
                            && (forall m' | m' in m.message.proposalJustification ::
                                || m' in signedRoundChangePayloads(messagesReceived)
                                || recoverSignedRoundChangeAuthor(m') in a.byz // random
                            )
                            && (forall m' | m' in m.message.roundChangeJustification ::
                                || m' in signedPreparePayloads(messagesReceived)
                                || recoverSignedPrepareAuthor(m') in a.byz // random
                            )                            
                        )
                        || (
                            && m.message.RoundChange?
                            && m.message.roundChangePayload in signedRoundChangePayloads(messagesReceived)
                            // it may be signed by adversaries
                            && (forall m' | m' in m.message.roundChangeJustification ::
                                || m' in signedPreparePayloads(messagesReceived)
                                || recoverSignedPrepareAuthor(m') in a.byz // random
                            )               
                            // block cannot be properly signed              
                        ) 
                        || (
                            && m.message.Prepare?
                            && recoverSignature(m.message) in a.byz // random
                        )   
                        || (
                            && m.message.Commit?
                            && recoverSignature(m.message) in a.byz // random
                            &&  var uPayload := m.message.commitPayload.unsignedPayload;
                                var cs := uPayload.commitSeal;
                            && (
                                || (cs in getCommitSeals(messagesReceived))
                                || (forall b :: 
                                        recoverSignedHashAuthor(hashBlockForCommitSeal(b),cs) in a.byz) // random
                            )
                        )                                        
                        || (
                            && m.message.NewBlock?
                            && (forall cs | cs in m.message.block.header.commitSeals :: 
                                            || (cs in getCommitSeals(messagesReceived))
                                            || (recoverSignedHashAuthor(hashBlockForCommitSeal(m.message.block),cs) in a.byz)) // random
                        )
        )
    }    
}