include "../../../spec/L1/types.dfy"
include "../distr_system_spec/common_functions.dfy"
include "../distr_system_spec/network.dfy"
include "../../../spec/L1/node_auxiliary_functions.dfy"
include "../../../spec/L1/node.dfy"
include "../distr_system_spec/distributed_system.dfy"
include "../../common/sets.dfy"
include "instrumented_specs.dfy"
include "axioms.dfy"
include "aux_functions.dfy"
include "basic_invariants.dfy"
include "instr_dsstate_networking_common_invariants.dfy"
include "networking_invariants.dfy"
include "networking_invariants_lemmas.dfy"
include "networking_step_lemmas.dfy"
include "instr_node_state_invariants.dfy"
include "quorum.dfy"
include "general_lemmas.dfy"
include "instr_dsstate_invariants_defs.dfy"
include "../theorems_defs.dfy"
include "instr_dsstate_invariants_1.dfy"


// TODO: Rename file and module
module L1_InstrDSStateInvariantsHeavyb
{
    import opened L1_SpecTypes
    import opened L1_SpecNetwork
    import opened L1_AuxiliaryFunctionsAndLemmas
    import opened L1_CommonFunctions
    import opened L1_Spec
    import opened HelperLemmasSets
    import opened L1_DistributedSystem
    import opened L1_InstrumentedSpecs
    import opened L1_Axioms
    import opened L1_AuxFunctionsProof
    import opened L1_AuxBasicInvariantsProof
    import opened L1_NetworkingInvariants
    import opened L1_InstrNodeStateInvariants
    import opened L1_LemmaQuorum
    import opened L1_GeneralLemmas
    import opened L1_InstrDSStateNetworkingCommonInvariants
    import opened L1_InstrDSStateInvariantsDefs
    import opened L1_NetworkingInvariantsLemmas
    import opened L1_NetworkingStepLemmas
    import opened L1_TheoremsDefs
    import opened L1_InstrDSStateInvariantsHeavy
    import opened L1_Adversary

    lemma getCommitSealsReverse(msg:set<QbftMessage>, cs: Signature) returns (m: QbftMessage)
        requires cs in getCommitSeals(msg)
        ensures m in msg
        ensures || (
            && m.NewBlock?
            && cs in m.block.header.commitSeals
        ) || (
            && m.Commit?
            && m.commitPayload.unsignedPayload.commitSeal == cs
        ) || (
            && m.Proposal?
            && cs in m.proposedBlock.header.commitSeals
        ) || (
            && m.RoundChange?
            && m.proposedBlockForNextRound.Optional?
            && cs in m.proposedBlockForNextRound.value.header.commitSeals
        )
        {
            m :| 
                && m in msg
                && ((
                    && m.NewBlock?
                    && cs in m.block.header.commitSeals
                ) || (
                    && m.Commit?
                    && m.commitPayload.unsignedPayload.commitSeal == cs
                ) || (
                    && m.Proposal?
                    && cs in m.proposedBlock.header.commitSeals
                ) || (
                    && m.RoundChange?
                    && m.proposedBlockForNextRound.Optional?
                    && cs in m.proposedBlockForNextRound.value.header.commitSeals
                ));
        }
// 222 s 
    // TODO: Check names invariants that are used more like ind invariant. Perhaps we should not discriminate between the two anyway.
    // Then should we change the name of the lemma?
    lemma lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(
        s:InstrDSState, 
        s': InstrDSState
    )    
    requires seqToSet(s.configuration.nodes) == s.nodes.Keys
    requires validInstrDSStateEx(s)   
    requires liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s)
    requires indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires invIfPreparePaylodSentThenPrepareSent(s)
    requires invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s)
    requires invForEveryCommitSealsSignedByAnHonestNodeExcludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s)
    requires invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s)
    requires invCommitSealsInAdversaryMessagesReceivedAreSubsetOfCommitSealsSent(s)
    requires InstrDSNextSingle(s, s')
    // ensures liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s')
    // ensures indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s')
    // ensures invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s')    
    // ensures invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s')  
    // ensures invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s')
    // ensures invCommitSealsInAdversaryMessagesReceivedAreSubsetOfCommitSealsSent(s')
    {
        lemmaInvNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s, s');
        lemmaSignedHash();
        lemmaDigest();
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedProposal();
        lemmaSignedRoundChange();
        lemmaGetSetOfSignedPayloads();

        
        // lemmaIndInvInstrNodeStateLifterToInstrDSState(s,s');
        // assume invCommitSealsInAdversaryMessagesReceivedAreSubsetOfCommitSealsSent(s');

        if s != s'
        {
            var node, messagesSentByTheNodes, messagesReceivedByTheNodes :|
                    InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);
            
            assert isNodeThatTakesStep(s, s', node);
  
            if isInstrNodeHonest(s,node)
            {
                var messagesReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;
                
                assert s.nodes[node].nodeState.id == node;
                     
                forall b, cs, csAuthor |
                    && cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s'))
                    && csAuthor == recoverSignedHashAuthor(hashBlockForCommitSeal(b), cs)
                    && isInstrNodeHonest(s', csAuthor)
                ensures true
                {
                    if cs !in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                    {
                        var current := s.nodes[node];
                        var next := s'.nodes[node];   
                        var newMessagesReceived := current.nodeState.messagesReceived + messagesReceived;                     
                        var newMessagesSentToItself :=  (next.nodeState.messagesReceived - messagesReceived - current.nodeState.messagesReceived);
                        

                        var allMessagesSentIncToItself  := fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)) + newMessagesSentToItself;

                        assert cs in getCommitSeals(allMessagesSentIncToItself) by {
                            assert next.messagesSentToItself == current.messagesSentToItself + newMessagesSentToItself;
                            lemmaAllMesssagesSentIncSentToItselfWithoutRecipientEqualOldPlusAllMessagesSentAtCurrentHonestStep(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);
                            assert allMesssagesSentIncSentToItselfWithoutRecipient(s') == 
                                    allMesssagesSentIncSentToItselfWithoutRecipient(s) +
                                    fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)) + 
                                    newMessagesSentToItself;

                            lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper2(s, s');

                            assert allMesssagesSentIncSentToItselfWithoutRecipient(s) <= allMesssagesSentIncSentToItselfWithoutRecipient(s');

                            lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper1_2(
                                allMesssagesSentIncSentToItselfWithoutRecipient(s'),
                                allMesssagesSentIncSentToItselfWithoutRecipient(s),
                                fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)),
                                newMessagesSentToItself,
                                cs
                            );

                            assert cs in getCommitSeals(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)) + 
                                    newMessagesSentToItself);
                        }
                        var m := getCommitSealsReverse(allMessagesSentIncToItself, cs);
        
                        if m.Commit?
                        {
                            assert validInstrState(current);
                            assert indInvInstrNodeStateTypes(current);
                            assert InstrNodeNextSingleStep(current,messagesReceived,next,messagesSentByTheNodes);
                            assert m in allMessagesSentIncToItself && isMsgWithSignedPayload(m);
                            lemmaAllSentAreSignedByTheNodeExNotForAll(s.nodes[node],messagesReceived,s'.nodes[node],messagesSentByTheNodes, m);
                            assert recoverSignature(m) == s.nodes[node].nodeState.id;
                            assert recoverSignature(m) == node;
                            assert node == csAuthor;
                            // assert m in s'.nodes[node].nodeState.messagesReceived;
                            // lemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s, s');
                            lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper4(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node, m, csAuthor);
                            assert m in getAllMessagesSentByTheNode(s', csAuthor);
                            assert m in getAllMessagesSentByInsrNodeState(s'.nodes[node]);
                            var pm :|    
                                && pm in s'.nodes[node].proposalsAccepted
                                &&  var cuPayload := m.commitPayload.unsignedPayload;
                                    var puPayload := pm.proposalPayload.unsignedPayload;
                                &&  puPayload.height == cuPayload.height
                                &&  puPayload.round == cuPayload.round
                                &&  digest(pm.proposedBlock) == cuPayload.digest
                                &&  signHash(hashBlockForCommitSeal(pm.proposedBlock), s.nodes[node].nodeState.id) == cuPayload.commitSeal;

                            var b' := pm.proposedBlock;
                            assert hashBlockForCommitSeal(b') == hashBlockForCommitSeal(b);
                            assert areBlocksTheSameExceptForTheCommitSeals(b',b);
                            assert pm.proposalPayload.unsignedPayload.round == b'.header.roundNumber;

                            assert m in getAllMessagesSentByTheNode(s', csAuthor); 
                            assert pm in s'.nodes[csAuthor].proposalsAccepted;
                            assert pm.proposedBlock == b';
                            assert areBlocksTheSameExceptForTheCommitSeals(b',b);
                            assert m.commitPayload.unsignedPayload.round == b.header.roundNumber;
                            assert m.commitPayload.unsignedPayload.digest == digest(b'); 
                        
                            assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor);
                        }                                                                                            
                    }
                    
                }               
            }
        }    
    }  
}