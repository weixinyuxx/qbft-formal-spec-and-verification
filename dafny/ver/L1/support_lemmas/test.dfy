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
include "general_lemmas.dfy"
include "basic_invariants.dfy"
include "instr_node_state_invariants.dfy"
include "networking_invariants.dfy"
include "networking_step_lemmas.dfy"
include "instr_dsstate_networking_common_invariants.dfy"
include "networking_invariants_lemmas.dfy"

module test
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
    import opened L1_InstrNodeStateInvariants
    import opened L1_InstrDSStateNetworkingCommonInvariants
    import opened L1_GeneralLemmas
    import opened L1_NetworkingInvariants
    import opened L1_NetworkingStepLemmas
    import opened L1_NetworkingInvariantsLemmas
    import opened L1_Adversary

 lemma lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(
        s:InstrDSState, 
        s': InstrDSState
    )    
    requires seqToSet(s.configuration.nodes) == s.nodes.Keys
    requires validInstrDSState(s)   
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires liftIndInvInstrNodeStateToInstrDSState(invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived)(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires InstrDSNextSingle(s, s')
    ensures indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s')
    ensures invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s')
    {
        assert invNodesIdMatchesMapKey(s'); 

        lemmaSignedProposal();
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedRoundChange();

        if s != s'
        {
            var node :| (
                    && validInstrDSState(s)
                    && InstrDSNextSingle(s, s')
                    && exists messagesSentByTheNodes, messagesReceivedByTheNodes :: InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node)
                );
            assert isNodeThatTakesStep(s, s', node);
            var messagesSentByTheNodes, messagesReceivedByTheNodes :|  InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);
            // lemmaNodesThatTakesAStepDoesNotChangeMessageSentByOtherNodesThatAreHonest2(s,s',node);
            lemmaGetSetOfSignedPayloads();

   
            if isInstrNodeHonest(s,node)
            {
                var messagesSentByTheNodes, messagesReceivedByTheNodes :|
                    InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);

                var messageReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;

                assert InstrNodeNextSingleStep(s.nodes[node],messageReceived,s'.nodes[node],messagesSentByTheNodes);

                

                // var inQbftMessages, outQbftMessages :|
                //     InstrNodeNextSingleStep(s.nodes[node], inQbftMessages, s'.nodes[node], outQbftMessages);

                // assume forall n | isInstrNodeHonest(s,n) && n != node ::
                //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].nodeState.messagesReceived), n) <=
                //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n);
                // assume forall n | isInstrNodeHonest(s,n) && n != node ::
                //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n) <=
                //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n); 

                lMessagesSentByTheNodesOnHonestStepAreSubsetOfMessagesSentByAllHonestNodesThatDoNotTakeTheStep(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);

                // assume forall n | isInstrNodeHonest(s,n) ::
                //              s.nodes[n].messagesSent <= s.environment.allMessagesSent;
                         


                assert s'.environment.allMessagesSent ==  s.environment.allMessagesSent + multiset(messagesSentByTheNodes);

                assert  allMessagesSentWithoutRecipient(s'.environment) ==
                        allMessagesSentWithoutRecipient(s.environment) + 
                        fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes));

                lemmaGetSetOfSignedPayloadsONSets(
                    allMessagesSentWithoutRecipient(s'.environment),
                    allMessagesSentWithoutRecipient(s.environment),
                    fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))
                );

                assert getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)) ==
                        getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)) + 
                        getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)));

                assert forall n | isInstrNodeHonest(s,n) && n != node ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n) ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) +
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n);

                assert forall n | isInstrNodeHonest(s,n) && n != node ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n) ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)), n);  

                // assert forall n | isInstrNodeHonest(s,n) && n != node ::
                //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) ==
                //     filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)), n);    

                assert forall n | isInstrNodeHonest(s,n) && n != node ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n);     

                assert forall n | isInstrNodeHonest(s,n) && n != node ::
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)), n) ==
                    filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n);                                                          

                // assert forall n | isInstrNodeHonest(s,n) :: invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s,n);
                lemmaInvSetOfMessagesSentAndSignedByAnHonestNodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s,s',node);
                // assert invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s', node);
                // assert forall n | isInstrNodeHonest(s,n) :: invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s',n);
                // assert invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s');
                assert invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s');
            }
            else
            {
                assert invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s') by {
                    lemmaAdversaryNextDoesNotChangeMessagesSentByHonestNodesExcludingSentToItself(s, s');
                    assert invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s);
                    forall n | isInstrNodeHonest(s, n) 
                        ensures  filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n) ==
                            filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)), n)
                    {
                        assert 
                        (
                            && filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) ==
                                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)),n)
                            && filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)),n) ==
                                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)),n) 
                            && filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) ==
                                filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n)
                        );
                    }
                }
            }         

        }
        else
        {
            assert invAdversaryMessagesReceivedHaveBeenSent(s);
            assert invNodesIdMatchesMapKey(s);
            assert invEnvMessagesSentYetToBeReceivedIsASubsetOfAllMessagesSent(s);
            assert invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s');
        }
    }
    lemma transitivity(s: set<QbftMessage>, a: set<QbftMessage>, b: set<QbftMessage>, n: Address)
    requires s == a + b
    ensures filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s),n) == filterSignedPayloadsByAuthor(getSetOfSignedPayloads(a),n) + filterSignedPayloadsByAuthor(getSetOfSignedPayloads(b),n)
    {

    }
    lemma test1(s:InstrDSState, 
        s': InstrDSState)
    requires seqToSet(s.configuration.nodes) == s.nodes.Keys
    requires validInstrDSState(s)   
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires invAllSignedPayloadsSentToItselfByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires liftIndInvInstrNodeStateToInstrDSState(invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived)(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
    requires InstrDSNextSingle(s, s')
    {
        forall n | isInstrNodeHonest(s', n)
            ensures && filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')), n) == filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n) + filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n].messagesSentToItself), n);
        {
            var allMessagesSentToItself := setUnion(set n:Address |
                            && n in s'.nodes
                            && isInstrNodeHonest(s', n)
                        ::
                            s'.nodes[n].messagesSentToItself);
            assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')), n) == filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n) + filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentToItself), n) by
                {
                    transitivity(allMesssagesSentIncSentToItselfWithoutRecipient(s'), allMessagesSentWithoutRecipient(s'.environment), allMessagesSentToItself, n);
                }
            assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentToItself), n) == filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n].messagesSentToItself), n) by
                {
                    var others := setUnion(set node:Address |
                        && node in s'.nodes
                        && isInstrNodeHonest(s', node)
                        && node != n
                    ::
                        s'.nodes[node].messagesSentToItself);
                    assert allMessagesSentToItself == s'.nodes[n].messagesSentToItself + others;
                    transitivity(allMessagesSentToItself, s'.nodes[n].messagesSentToItself, others, n);
                    forall m | m in getSetOfSignedPayloads(others) && recoverSignedPayloadSignature(m) == n
                        ensures m in getSetOfSignedPayloads(s'.nodes[n].messagesSentToItself)
                        {
                            var node :| (
                                && m in getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself)
                                && node in s'.nodes
                                && isInstrNodeHonest(s', node)
                                && node != n
                            );
                            // assert m in getSetOfSignedPayloads(s'.nodes[node].nodeState.messagesReceived);
                            // assert m in getSetOfSignedPayloads(s'.environment.allMessagesSent);

                        }
                }
        }

    }
    lemma test2(s:InstrDSState, 
        s': InstrDSState)
    requires seqToSet(s.configuration.nodes) == s.nodes.Keys
    requires validInstrDSState(s)   
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires invAllSignedPayloadsSentToItselfByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires liftIndInvInstrNodeStateToInstrDSState(invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived)(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
    requires InstrDSNextSingle(s, s')
    {
        forall n | isInstrNodeHonest(s', n)
            ensures filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s', n)), n) == filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)), n) + filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n].messagesSentToItself), n);
            {
            }
    }
    lemma test(s:InstrDSState, 
        s': InstrDSState)
    requires seqToSet(s.configuration.nodes) == s.nodes.Keys
    requires validInstrDSState(s)   
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires invAllSignedPayloadsSentToItselfByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires liftIndInvInstrNodeStateToInstrDSState(invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived)(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
    requires InstrDSNextSingle(s, s')
    {
        forall n | isInstrNodeHonest(s', n)
            ensures filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')), n)
                    == filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s', n)), n)
            {
                assert && filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')), n) == filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n) + filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n].messagesSentToItself), n)
                        && filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s', n)), n) == filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)), n) + filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[n].messagesSentToItself), n);
                        // && filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n) == filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)), n);
                assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n) == filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)), n) by {
                    lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s,s');
                }
            }
    }
    lemma lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItselfd(
        s:InstrDSState, 
        s': InstrDSState
    )    
    requires seqToSet(s.configuration.nodes) == s.nodes.Keys
    requires validInstrDSState(s)   
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires invAllSignedPayloadsSentToItselfByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires liftIndInvInstrNodeStateToInstrDSState(invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived)(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
    requires InstrDSNextSingle(s, s')
    // ensures indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s')
    ensures invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s')
    {
        forall n | isInstrNodeHonest(s, n)
            ensures filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), n)
                    == filterSignedPayloadsByAuthor(getSetOfSignedPayloads(getAllMessagesSentByTheNode(s, n)), n)
            {
                assert filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), n) == filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) + filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[n].messagesSentToItself), n);
                lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s,s');
            }
    }
    // 193s Fixed Inconclusive
    lemma lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(
        s:InstrDSState, 
        s': InstrDSState
    )    
    requires validInstrDSState(s)   
    requires indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s)
    requires invAllSignedPayloadsReceivedByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires invAllSignedPayloadsSentToItselfByAnyHonestNodeAndSignedByAnHonestNodeHaveBeenSentByTheHonestNode(s)
    requires liftIndInvInstrNodeStateToInstrDSState(invInstrNodeStateOutputSignedPayloadsSignedByOthersHaveBeenReceived)(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s)
    requires invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s)
    requires InstrDSNextSingle(s, s')
    // ensures indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s')
    ensures invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s')
    {
        assert invNodesIdMatchesMapKey(s'); 

        lemmaSignedProposal();
        lemmaSignedPrepare();
        lemmaSignedCommit();
        lemmaSignedRoundChange();

        if s != s'
        {
            // var node :| (
            //         && validInstrDSState(s)
            //         && InstrDSNextSingle(s, s')
            //         && exists messagesSentByTheNodes, messagesReceivedByTheNodes :: InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node)
            //     );
            // assert isNodeThatTakesStep(s, s', node);

            // lemmaGetSetOfSignedPayloads();
            // lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkExcludingSentToItself(s, s');

   
            // if isInstrNodeHonest(s,node)
            // {
            //     var messagesSentByTheNodes, messagesReceivedByTheNodes :|
            //         InstrDSNextNodeSingle(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);

            //     var messageReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;

            //     assert InstrNodeNextSingleStep(s.nodes[node],messageReceived,s'.nodes[node],messagesSentByTheNodes);

            //     lMessagesSentByTheNodesOnHonestStepAreSubsetOfMessagesSentByAllHonestNodesThatDoNotTakeTheStep(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);
            //     assert  forall n | isInstrNodeHonest(s,n) && n != node ::
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n) <=
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n); 

            //     assert s'.environment.allMessagesSent ==  s.environment.allMessagesSent + multiset(messagesSentByTheNodes);

            //     assert  allMessagesSentWithoutRecipient(s'.environment) ==
            //             allMessagesSentWithoutRecipient(s.environment) + 
            //             fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes));

            //     lemmaGetSetOfSignedPayloadsONSets(
            //         allMessagesSentWithoutRecipient(s'.environment),
            //         allMessagesSentWithoutRecipient(s.environment),
            //         fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))
            //     );

            //     assert getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)) ==
            //             getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)) + 
            //             getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes)));

            //     assert forall n | isInstrNodeHonest(s,n) && n != node ::
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s'.environment)), n) ==
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n) +
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(messagesSentByTheNodes))), n);

            //     assert forall n | isInstrNodeHonest(s,n) && n != node ::
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.nodes[n].messagesSent)), n) ==
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(fromMultisetQbftMessagesWithRecipientToSetOfMessages(s'.nodes[n].messagesSent)), n);  

            //     lemmaiInvSetOfMessagesSentAndSignedByAnHonestNodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s,s',node);

            //     lMessagesSignedByAnHonestNodeThatDoesNotTakeTheStepInTheMessagesSentToItselfByTheHonestNodeThatTakesTheStepAreSubsetOfTheAllMessagesSentByTheNodeThatDoesNotTakeTheStep(s, s', messagesSentByTheNodes, messagesReceivedByTheNodes, node);
            //     assert forall n | isInstrNodeHonest(s,n) && n != node ::
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s.nodes[node].messagesSentToItself), n) <=
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n);

            //     assert forall n | isInstrNodeHonest(s',n) && n != node ::
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(s'.nodes[node].messagesSentToItself), n) <=
            //         filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMessagesSentWithoutRecipient(s.environment)), n); 

            //     forall n | isInstrNodeHonest(s,n) && n != node
            //     ensures filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s')), n) == filterSignedPayloadsByAuthor(getSetOfSignedPayloads(allMesssagesSentIncSentToItselfWithoutRecipient(s)), n);  
            //     {
            //         lemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItselfHelper3(
            //             s,
            //             s',
            //             messagesSentByTheNodes,
            //             messagesReceivedByTheNodes,
            //             node,
            //             n
            //         );
            //     }

            //     forall n | isInstrNodeHonest(s,n) && n != node
            //     ensures invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s', n);
            //     {
            //         // assume invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s', n);
            //         assert s.nodes[n].messagesSentToItself == s'.nodes[n].messagesSentToItself;    
            //         assert s.nodes[n].messagesSent == s'.nodes[n].messagesSent;    
            //         assert getAllMessagesSentByTheNode(s, n) == getAllMessagesSentByTheNode(s', n);    
            //         assert invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s, n);
            //         assert invSetOfMessagesSignedByANodeInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s', n);                    
            //     }

            //     // assert indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s');
            //     assert invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s');
            // }
            // else
            // {
            //     lemmaAdversaryNextDoesNotChangeMessagesSentByHonestNodesIncludingSentToItself(s, s');
            //     assert messagesSentByHonestNodesIncludingSentToItselfDoNotChange(s, s');
            //     assert indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s');
            //     assert invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s');
            // }         
    assume  invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s')
            assume 
        }
        else
        {
            assert indInvLemmaInvSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetwork(s');
            assert invSetOfMessagesSentAndSignedByHonestNodesInItsSetOfMessagesSentEqualTheSetOfMessagesSignedByTheNodeInTheAllMessagesSentInNetworkIncludingSentToItself(s');
        }
    }    

}