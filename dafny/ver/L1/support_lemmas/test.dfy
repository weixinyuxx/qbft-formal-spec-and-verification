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
    lemma getCommitSealsTransitivity(msg1:set<QbftMessage>, msg2:set<QbftMessage>, cs: Signature)
        requires msg1 <= msg2
        requires cs in getCommitSeals(msg1)
        ensures getCommitSeals(msg1) <= getCommitSeals(msg2)
        ensures cs in getCommitSeals(msg2)
        {
        }
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

    lemma lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerb(
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
    {
        if s != s'
        {
            var node :| (exists messagesSentByTheNodes,
                    messagesReceivedByTheNodes
                    ::
                    InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node));
            
            assert isNodeThatTakesStep(s, s', node);

            var messagesSentByTheNodes, messagesReceivedByTheNodes :|
                    InstrDSNextNodeSingle(s,s',messagesSentByTheNodes,messagesReceivedByTheNodes,node);  
            if !isInstrNodeHonest(s, node)
            {
                forall b, cs, csAuthor |
                    && cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s'))
                    && csAuthor == recoverSignedHashAuthor(hashBlockForCommitSeal(b), cs)
                    && isInstrNodeHonest(s', csAuthor)
                    ensures true
                {
                    if !(cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s)))
                    {
                        assert cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s)) by {
                            assert cs in getCommitSeals(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.environment.allMessagesSent)) by {
                                lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper0(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node, cs);
                                assert cs in getCommitSeals(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)));
                                lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper1(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);
                                getCommitSealsTransitivity(s'.adversary.messagesReceived, fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.environment.allMessagesSent), cs);
                                assert cs in getCommitSeals(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.environment.allMessagesSent));
                            }
                            getCommitSealsTransitivity(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.environment.allMessagesSent), allMesssagesSentIncSentToItselfWithoutRecipient(s), cs);
                        }
                        assert false;
                    }
                }

            }
        }
  

    }
    lemma lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerc(
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
    {
        if s != s'
        {
            var node :| (exists messagesSentByTheNodes,
                    messagesReceivedByTheNodes
                    ::
                    InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node));
            
            assert isNodeThatTakesStep(s, s', node);

            var messagesSentByTheNodes, messagesReceivedByTheNodes :|
                    InstrDSNextNodeSingle(s,s',messagesSentByTheNodes,messagesReceivedByTheNodes,node);  
            if isInstrNodeHonest(s,node)
            {
                var messagesReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;
                
                // assert s.nodes[node].nodeState.id == node;
                     
                forall b, cs, csAuthor |
                    && cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s'))
                    && csAuthor == recoverSignedHashAuthor(hashBlockForCommitSeal(b), cs)
                    && isInstrNodeHonest(s', csAuthor)
                ensures true 
                {
                    // assume pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor);
                    if cs !in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                    {
                        var current := s.nodes[node];
                        var next := s'.nodes[node];   
                        var newMessagesReceived := current.nodeState.messagesReceived + messagesReceived;                     
                        var newMessagesSentToItself :=  (next.nodeState.messagesReceived - newMessagesReceived - current.nodeState.messagesReceived);
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
                        var allMessagesSentIncToItself  := fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)) + newMessagesSentToItself;

                        assert cs in getCommitSeals(allMessagesSentIncToItself);

                        var m := getCommitSealsReverse(allMessagesSentIncToItself, cs);

                        if m.Commit?
                        {
                            assert validInstrState(s.nodes[node]);
                            assert indInvInstrNodeStateTypes(s.nodes[node]);
                            assert InstrNodeNextSingleStep(s.nodes[node],messagesReceived,s'.nodes[node],messagesSentByTheNodes);
                            assert m in allMessagesSentIncToItself && isMsgWithSignedPayload(m);
                            // lemmaAllSentAreSignedByTheNodeExNotForAll(s.nodes[node],messagesReceived,s'.nodes[node],messagesSentByTheNodes, m);
                            // assert recoverSignature(m) == s.nodes[node].nodeState.id;
                            // assert recoverSignature(m) == node;
                            // assert node == csAuthor;
                            // // assert m in s'.nodes[node].nodeState.messagesReceived;
                            // // lemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s, s');
                            // lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper4(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node, m, csAuthor);
                            // assert m in getAllMessagesSentByTheNode(s', csAuthor);
                            // assert m in getAllMessagesSentByInsrNodeState(s'.nodes[node]);

                            // assert InstrNodeNextSingleStep(s.nodes[node], messagesReceived, s'.nodes[node],messagesSentByTheNodes);
                            // assert NodeNextSingleStep(current.nodeState, messagesReceived, next.nodeState, messagesSentByTheNodes);
                            // var newTime :| 
                            //     var currentWithNewMessagesReceived :=
                            //         current.nodeState.(
                            //             messagesReceived := newMessagesReceived,
                            //             localTime := newTime
                            //         );

                            //     NodeNextSubStep(currentWithNewMessagesReceived, next.nodeState, messagesSentByTheNodes);
                            // var currentWithNewMessagesReceived :=
                            //         current.nodeState.(
                            //             messagesReceived := newMessagesReceived,
                            //             localTime := newTime
                            //         );
                            // assert NodeNextSubStep(currentWithNewMessagesReceived, next.nodeState, messagesSentByTheNodes);
                            // // assert m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)) + 
                            // //     newMessagesSentToItself;
                            // assume m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes));
                            // assert exists msg:QbftMessageWithRecipient | msg in messagesSentByTheNodes :: msg.message.Commit?;
                            // var msg:QbftMessageWithRecipient :| msg in messagesSentByTheNodes
                            //             && msg.message.Commit?
                            //             && msg.message == m;
                            // // assert !UponNewBlock(currentWithNewMessagesReceived, next.nodeState, messagesSentByTheNodes);
                            // // assert !UponBlockTimeout(currentWithNewMessagesReceived, next.nodeState, messagesSentByTheNodes);
                            // // assert !UponProposal(currentWithNewMessagesReceived, next.nodeState, messagesSentByTheNodes);
                            // // assert !UponCommit(currentWithNewMessagesReceived, next.nodeState, messagesSentByTheNodes);
                            // // assert !UponRoundChange(currentWithNewMessagesReceived, next.nodeState, messagesSentByTheNodes);
                            // // assert !UponRoundTimeout(currentWithNewMessagesReceived, next.nodeState, messagesSentByTheNodes);
                            // assume UponPrepare(currentWithNewMessagesReceived, next.nodeState, messagesSentByTheNodes);


                            // // assert validInstrState(s.nodes[node]);
                            // // assert indInvInstrNodeStateTypes(s.nodes[node]);
                            // // assert InstrNodeNextSingleStep(s.nodes[node],messagesReceived,s'.nodes[node],messagesSentByTheNodes);
                            // // // assert m in allMessagesSentIncToItself && isMsgWithSignedPayload(m);
                            // // lemmaAllSentAreSignedByTheNodeExNotForAll(s.nodes[node],messagesReceived,s'.nodes[node],messagesSentByTheNodes, m);
                            // // assert recoverSignature(m) == s.nodes[node].nodeState.id;
                            // // assert recoverSignature(m) == node;
                            // // assert node == csAuthor;
                            // // // // assert m in s'.nodes[node].nodeState.messagesReceived;
                            // // // // lemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s, s');
                            // // lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper4(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node, m, csAuthor);
                            // // assert m in getAllMessagesSentByTheNode(s', csAuthor);
                            // // assert m in getAllMessagesSentByInsrNodeState(s'.nodes[node]);

                            // assert optionIsPresent(currentWithNewMessagesReceived.proposalAcceptedForCurrentRound);
                            // var pm := currentWithNewMessagesReceived.proposalAcceptedForCurrentRound.value;
                            // assert &&   var cuPayload := m.commitPayload.unsignedPayload;
                            //             var puPayload := pm.proposalPayload.unsignedPayload;
                            //     &&  puPayload.height == cuPayload.height
                            //     &&  puPayload.round == cuPayload.round
                            //     &&  digest(pm.proposedBlock) == cuPayload.digest
                            //     &&  signHash(hashBlockForCommitSeal(pm.proposedBlock), s.nodes[node].nodeState.id) == cuPayload.commitSeal
                            //     && pm in s'.nodes[node].proposalsAccepted;
                            // var b' := pm.proposedBlock;
                            // assert forall mm:QbftMessageWithRecipient | mm in messagesSentByTheNodes
                            //             :: mm.message == Commit(
                            //                                 signCommit(
                            //                                     UnsignedCommit(
                            //                                         |current.nodeState.blockchain|,
                            //                                         current.nodeState.round,
                            //                                         signHash(hashBlockForCommitSeal(b'), node),
                            //                                         digest(b')),
                            //                                         node
                            //                                     )
                            //                                 );
                            
                            // assert m.commitPayload.unsignedPayload.height == b.header.height
                            //     && m.commitPayload.unsignedPayload.round == b.header.roundNumber by {
                            //         lemmaSignedHash();
                            //     }


                            
                            
                            // assert 
                            //     && pm in s'.nodes[node].proposalsAccepted
                            //     &&  var cuPayload := m.commitPayload.unsignedPayload;
                            //         var puPayload := pm.proposalPayload.unsignedPayload;
                            //     &&  puPayload.height == cuPayload.height
                            //     &&  puPayload.round == cuPayload.round
                            //     &&  digest(pm.proposedBlock) == cuPayload.digest
                            //     &&  signHash(hashBlockForCommitSeal(pm.proposedBlock), s.nodes[node].nodeState.id) == cuPayload.commitSeal;

                            // var b' := pm.proposedBlock;
                            // assert hashBlockForCommitSeal(b') == hashBlockForCommitSeal(b);
                            // assert areBlocksTheSameExceptForTheCommitSeals(b',b);
                            // assert pm.proposalPayload.unsignedPayload.round == b'.header.roundNumber;

                            // assert && m in getAllMessagesSentByTheNode(s', csAuthor)
                            //     && m.Commit?
                            //     && m.commitPayload.unsignedPayload.height == b.header.height
                            //     && m.commitPayload.unsignedPayload.round == b.header.roundNumber
                            //     && m.commitPayload.unsignedPayload.digest == digest(b');

                            // assert m in getAllMessagesSentByTheNode(s', csAuthor); 
                            // assert pm in s'.nodes[csAuthor].proposalsAccepted;
                            // assert pm.proposedBlock == b';
                            // assert areBlocksTheSameExceptForTheCommitSeals(b',b);
                            // assert m.commitPayload.unsignedPayload.round == b.header.roundNumber;
                            // assert m.commitPayload.unsignedPayload.digest == digest(b'); 
                        
                            // assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor);
                        }   
                    //     else
                    //     {
                    //         lemmaAllNewBlockSentIncItselfThereIsACommitInReceived(s.nodes[node],messagesReceived,s'.nodes[node],messagesSentByTheNodes);
                    //         assert exists cm ::  && cm in s'.nodes[node].nodeState.messagesReceived
                    //                             && cm.Commit?
                    //                             && var uPayload := cm.commitPayload.unsignedPayload;
                    //                             && uPayload.commitSeal == cs
                    //                             && uPayload.round == m.block.header.roundNumber
                    //                             && uPayload.height == m.block.header.height
                    //                              && recoverSignedCommitAuthor(cm.commitPayload) == csAuthor;  


                    //         var cm :|   && cm in s'.nodes[node].nodeState.messagesReceived
                    //                     && cm.Commit?
                    //                     && var uPayload := cm.commitPayload.unsignedPayload;
                    //                     && uPayload.commitSeal == cs
                    //                     && uPayload.round == m.block.header.roundNumber
                    //                     && uPayload.height == m.block.header.height
                    //                     && recoverSignedCommitAuthor(cm.commitPayload) == csAuthor;   



                    //         // lemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s, s');  
                    //         assert isInstrNodeHonest(s', csAuthor);
                    //         assert isInstrNodeHonest(s', node);
                    //         assert recoverSignature(cm) == csAuthor;   

                    //         assert invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s);
                    //         assert invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s');

                    //         lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper5(
                    //             // s,
                    //             s',
                    //             node,
                    //             csAuthor,
                    //             cm
                    //             );                            

                    //         // var scm :=  getSignedPayload(cm);

                    //         // assert scm in  filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].nodeState.messagesReceived), csAuthor);

                    //         // lemmaInvMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodesToNotForAll(
                    //         //     s',
                    //         //     node,
                    //         //     csAuthor,
                    //         //     scm
                    //         // );
                    //         assert getSignedPayload(cm) in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s',csAuthor)); 

                    //         lemmaSignedCommitPayloadInSetOfSignedPayloadsImplyNonSignedIsInSetOfNonSigned(cm, getAllMessagesSentByTheNode(s',csAuthor));

                    //         assert cm in getAllMessagesSentByTheNode(s',csAuthor);    

                    // //         assert getSignedPayload(cm) in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s',csAuthor));    

                    //         lemmaIndInvInstrNodeStateLifterToInstrDSState(s,s');
                    //         assert invInstrNodeStateCommitSentOnlyIfAcceptedProposal(s'.nodes[csAuthor]);
                    //         assert
                    //         exists pm ::    
                    //             && pm in s'.nodes[csAuthor].proposalsAccepted
                    //             &&  var cuPayload := cm.commitPayload.unsignedPayload;
                    //                 var puPayload := pm.proposalPayload.unsignedPayload;
                    //             &&  puPayload.height == cuPayload.height
                    //             &&  puPayload.round == cuPayload.round
                    //             &&  digest(pm.proposedBlock) == cuPayload.digest
                    //             &&  signHash(hashBlockForCommitSeal(pm.proposedBlock), s'.nodes[csAuthor].nodeState.id) == cuPayload.commitSeal;

                    //         assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor);
                    // //         // if cm in fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[csAuthor].messagesSent)
                    // //         // {
                    // //         //     // assert
                    // //         //     // exists b', p ::    
                    // //         //     //     && cm in getAllMessagesSentByTheNode(s', csAuthor)
                    // //         //     //     && p in s'.nodes[csAuthor].proposalsAccepted
                    // //         //     //     && p.proposedBlock == b'
                    // //         //     //     && areBlocksTheSameExceptForTheCommitSeals(b',b)
                    // //         //     //     && cm.commitPayload.unsignedPayload.digest == digest(b');                                 
                    // //         //     assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor);
                    // //         // }   
                    // //         // else
                    // //         // {
                    // //         //     // assert cm in s'.nodes[csAuthor].messagesSentToItself;
                    // //         //     // assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor);
                    // //         // }                     

                    //     }                                                                                          
                    }
                    
                }               
                // assert invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s');
            }
        }
        
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
    ensures liftIndInvInstrNodeStateToInstrDSState(indInvInstrNodeState)(s')
    ensures indInvLemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s')
    ensures invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s')    
    ensures invNoConflictingHonestPrepareMessagesForTheSameRoundAreEverReceivedByHonestNodes(s')  
    ensures invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s')
    ensures invCommitSealsInAdversaryMessagesReceivedAreSubsetOfCommitSealsSent(s')
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
        assert invCommitSealsInAdversaryMessagesReceivedAreSubsetOfCommitSealsSent(s');

        if s != s'
        {
            var node :| (exists messagesSentByTheNodes,
                    messagesReceivedByTheNodes
                    ::
                    InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node));
            
            assert isNodeThatTakesStep(s, s', node);

            var messagesSentByTheNodes, messagesReceivedByTheNodes :|
                    InstrDSNextNodeSingle(s,s',messagesSentByTheNodes,messagesReceivedByTheNodes,node);  

  

            if isInstrNodeHonest(s,node)
            {
                var messagesReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;
                
                assert s.nodes[node].nodeState.id == node;
                     
                forall b, cs, csAuthor |
                    && cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s'))
                    && csAuthor == recoverSignedHashAuthor(hashBlockForCommitSeal(b), cs)
                    && isInstrNodeHonest(s', csAuthor)
                ensures pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor) 
                {
                    // assume pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor);
                    if cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                    {
                        assert isInstrNodeHonest(s, csAuthor);
                        assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s,b,csAuthor);
                        var   cm:QbftMessage, b', p :|  
                            && cm in getAllMessagesSentByTheNode(s, csAuthor)
                            && p in s.nodes[csAuthor].proposalsAccepted
                            && p.Proposal?
                            && p.proposedBlock == b'
                            && areBlocksTheSameExceptForTheCommitSeals(b',b)
                            && cm.Commit?
                            && cm.commitPayload.unsignedPayload.height == b.header.height
                            && cm.commitPayload.unsignedPayload.round == b.header.roundNumber
                            && cm.commitPayload.unsignedPayload.digest == digest(b'); 
                        lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper3(s, s', csAuthor);
                        assert cm in getAllMessagesSentByTheNode(s', csAuthor); 
                        assert p in s'.nodes[csAuthor].proposalsAccepted;                      
                        assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor);
                    }
                    else
                    {
                        var current := s.nodes[node];
                        var next := s'.nodes[node];   
                        var newMessagesReceived := current.nodeState.messagesReceived + messagesReceived;                     
                        var newMessagesSentToItself :=  (next.nodeState.messagesReceived - newMessagesReceived - current.nodeState.messagesReceived);
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

                        // assert cs in getCommitSeals(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)) + 
                        //         newMessagesSentToItself);

                        var allMessagesSentIncToItself  := fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)) + newMessagesSentToItself;

                        assert cs in  getCommitSeals(allMessagesSentIncToItself);

                        var m :| 
                                    && m in allMessagesSentIncToItself
                                    && (
                                        || (
                                            && m.Commit?
                                            && m.commitPayload.unsignedPayload.commitSeal == cs
                                        )
                                        || (
                                            && m.NewBlock?
                                            && cs in m.block.header.commitSeals
                                        )
                                    );   

                        if m.Commit?
                        {
                            assert validInstrState(s.nodes[node]);
                            assert indInvInstrNodeStateTypes(s.nodes[node]);
                            assert InstrNodeNextSingleStep(s.nodes[node],messagesReceived,s'.nodes[node],messagesSentByTheNodes);
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
                        else if m.NewBlock?
                        {
                            assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s,b,csAuthor);
                            assert m.block.header.commitSeals <= getCommitSeals(current.nodeState.messagesReceived);
                            assert current.nodeState.messagesReceived <= allMesssagesSentIncSentToItselfWithoutRecipient(s);
                            assert m.block.header.commitSeals <= getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s));
                            assert cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s));
                            assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor);


                            lemmaAllNewBlockSentIncItselfThereIsACommitInReceived(s.nodes[node],messagesReceived,s'.nodes[node],messagesSentByTheNodes);
                            assert exists cm ::  && cm in s'.nodes[node].nodeState.messagesReceived
                                                && cm.Commit?
                                                && var uPayload := cm.commitPayload.unsignedPayload;
                                                && uPayload.commitSeal == cs
                                                && uPayload.round == m.block.header.roundNumber
                                                && uPayload.height == m.block.header.height
                                                 && recoverSignedCommitAuthor(cm.commitPayload) == csAuthor;  


                            var cm :|   && cm in s'.nodes[node].nodeState.messagesReceived
                                        && cm.Commit?
                                        && var uPayload := cm.commitPayload.unsignedPayload;
                                        && uPayload.commitSeal == cs
                                        && uPayload.round == m.block.header.roundNumber
                                        && uPayload.height == m.block.header.height
                                        && recoverSignedCommitAuthor(cm.commitPayload) == csAuthor;   



                            // lemmaMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s, s');  
                            assert isInstrNodeHonest(s', csAuthor);
                            assert isInstrNodeHonest(s', node);
                            assert recoverSignature(cm) == csAuthor;   

                            assert invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s);
                            assert invMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodes(s');

                            lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper5(
                                // s,
                                s',
                                node,
                                csAuthor,
                                cm
                                );                            

                            // var scm :=  getSignedPayload(cm);

                            // assert scm in  filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].nodeState.messagesReceived), csAuthor);

                            // lemmaInvMessagesReceivedAndSignedByHonestNodesHaveBeenSentByTheHonestNodesToNotForAll(
                            //     s',
                            //     node,
                            //     csAuthor,
                            //     scm
                            // );
                            assert getSignedPayload(cm) in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s',csAuthor)); 

                            lemmaSignedCommitPayloadInSetOfSignedPayloadsImplyNonSignedIsInSetOfNonSigned(cm, getAllMessagesSentByTheNode(s',csAuthor));

                            assert cm in getAllMessagesSentByTheNode(s',csAuthor);    

                    //         assert getSignedPayload(cm) in getSetOfSignedPayloads(getAllMessagesSentByTheNode(s',csAuthor));    

                            lemmaIndInvInstrNodeStateLifterToInstrDSState(s,s');
                            assert invInstrNodeStateCommitSentOnlyIfAcceptedProposal(s'.nodes[csAuthor]);
                            assert
                            exists pm ::    
                                && pm in s'.nodes[csAuthor].proposalsAccepted
                                &&  var cuPayload := cm.commitPayload.unsignedPayload;
                                    var puPayload := pm.proposalPayload.unsignedPayload;
                                &&  puPayload.height == cuPayload.height
                                &&  puPayload.round == cuPayload.round
                                &&  digest(pm.proposedBlock) == cuPayload.digest
                                &&  signHash(hashBlockForCommitSeal(pm.proposedBlock), s'.nodes[csAuthor].nodeState.id) == cuPayload.commitSeal;

                            assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor);
                    //         // if cm in fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[csAuthor].messagesSent)
                    //         // {
                    //         //     // assert
                    //         //     // exists b', p ::    
                    //         //     //     && cm in getAllMessagesSentByTheNode(s', csAuthor)
                    //         //     //     && p in s'.nodes[csAuthor].proposalsAccepted
                    //         //     //     && p.proposedBlock == b'
                    //         //     //     && areBlocksTheSameExceptForTheCommitSeals(b',b)
                    //         //     //     && cm.commitPayload.unsignedPayload.digest == digest(b');                                 
                    //         //     assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor);
                    //         // }   
                    //         // else
                    //         // {
                    //         //     // assert cm in s'.nodes[csAuthor].messagesSentToItself;
                    //         //     // assert pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor);
                    //         // }                     

                        }                                                                                          
                    }
                    
                }               
                assert invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s');
            }
            else
            {
                forall b, cs, csAuthor |
                    && cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s'))
                    && csAuthor == recoverSignedHashAuthor(hashBlockForCommitSeal(b), cs)
                    && isInstrNodeHonest(s', csAuthor)
                ensures pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s',b,csAuthor)
                {

                    lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper0(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node, cs);

                    if cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s))
                    {
                        assert   pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s, b,csAuthor); 
                        
                        var   cm:QbftMessage, b', p :|  
                            && cm in getAllMessagesSentByTheNode(s, csAuthor)
                            && p in s.nodes[csAuthor].proposalsAccepted
                            && p.Proposal?
                            && p.proposedBlock == b'
                            && areBlocksTheSameExceptForTheCommitSeals(b',b)
                            && cm.Commit?
                            && cm.commitPayload.unsignedPayload.height == b.header.height
                            && cm.commitPayload.unsignedPayload.round == b.header.roundNumber
                            && cm.commitPayload.unsignedPayload.digest == digest(b');

                        assert   pThereExistCommitMessageSentByCommitSealSignerBlockAndProposalAcceptedSuchThatBlockIsTheProposalAcceptedBlockIsTheSameExceptForCommitSealsAsTheBlockSuppliedAndCommitMessageHeightRoundAndDigestAreConsistentWithtTheBlock(s', b,csAuthor); 
                    }
                    else
                    {    
                        assert cs in getCommitSeals(allMesssagesSentIncSentToItselfWithoutRecipient(s)) by {
                            assert cs in getCommitSeals(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.environment.allMessagesSent)) by {
                                lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper0(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node, cs);
                                assert cs in getCommitSeals(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)));
                                lemmaInvForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSignerHelper1(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);
                                getCommitSealsTransitivity(s'.adversary.messagesReceived, fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.environment.allMessagesSent), cs);
                                assert cs in getCommitSeals(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.environment.allMessagesSent));
                            }
                            getCommitSealsTransitivity(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.environment.allMessagesSent), allMesssagesSentIncSentToItselfWithoutRecipient(s), cs);
                        }
                        assert false;
                    } 
                }
            }
        }
        else
        {
            assert invForEveryCommitSealsSignedByAnHonestNodeIncludingSentToItselfThereExistsAMatchingCommitMessageSentByTheCommitSealSigner(s');     
        }  
    }  
}