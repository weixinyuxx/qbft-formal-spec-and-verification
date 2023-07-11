include "../dafny/ver/L1/distr_system_spec/distributed_system.dfy"
include "../dafny/ver/common/seqs.dfy"
include "../test/test_helpers.dfy"

module get_commit_seals {
    import opened L1_SpecTypes
    import opened L1_SpecNetwork
    import opened L1_Adversary
    import opened L1_DistributedSystem
    import opened L1_Theorems
    import opened L1_TheoremsDefs
    import opened L1_AuxiliaryFunctionsAndLemmas
    import opened test_helpers
    import opened L1_Spec
    import opened L1_CommonFunctions
    import opened Collections__Seqs
    import opened HelperLemmasSets

    lemma ValidInitialState(state: DSState)
        requires state == s0()
        requires forall blockchain ::validators(blockchain) == [0,1,2,3]
        ensures DSInit(state, config())
    {}
    lemma ValidStep1(state0: DSState, state1: DSState)
        requires state0 == s0()
        requires state1 == s1()
        requires forall blockchain ::validators(blockchain) == [0,1,2,3]
        ensures DSNextNode(state0, state1,  {proposal(1), proposal(2)}, multiset{}, 0);
        ensures DSNext(state0, state1)
    {
        assert validDSState(state0);
        assert AdversaryNext(state0.adversary, {}, state1.adversary, {proposal(1), proposal(2)}) by {
            lemmaSignedProposal();
        }
        assert DSNextNode(state0, state1,  {proposal(1), proposal(2)}, multiset{}, 0);
    }
    lemma ValidStep2(state1: DSState, state2: DSState)
        requires state1 == s1()
        requires state2 == s2()
        requires forall blockchain ::validators(blockchain) == [0,1,2,3]
        ensures DSNextNode(state1, state2, {newBlock(1), newBlock(2)}, multiset{proposal(1), proposal(2)}, 0);
        ensures DSNext(state1, state2)
    {
        assert DSNextNode(state1, state2, {newBlock(1), newBlock(2)}, multiset{proposal(1), proposal(2)}, 0);
    }
    lemma ValidStep3(state2: DSState, state3: DSState)
        requires state2 == s2()
        requires state3 == s3()
        requires forall blockchain ::validators(blockchain) == [0,1,2,3]
        // requires forall blockchain, block :: validateEthereumBlock(blockchain, block)
        // requires forall block, ns, r | block == getNewBlock(ns, r) :: block.header.proposer == ns.id
        // requires forall ns1:NodeState, ns2:NodeState, r:nat | ns1.blockchain == ns2.blockchain :: getNewBlock(ns1, r) == getNewBlock(ns2, r)
        ensures DSNextNode(s2(), s3(), outProposal3() + outPrepare3(), multiset{newBlock(1)}, 1);
        ensures DSNext(state2, state3)
    {
        assert validNewBlockMessage([genesisBlock()], newBlock(1).message) by {
            lemmaSignedHash();
        }
        assert UponNewBlock(currentWithNewMessagesReceived3(), intermediateState3_1(), {});
        assert UponBlockTimeout(intermediateState3_1(), intermediateState3_2(), outProposal3());
        assert proposer(0, [genesisBlock(), newBlock(1).message.block]) == 1;
        assert isValidProposal(proposal3(), intermediateState3_2()) by {
            lemmaSignedProposal();
            assert validateNonPreparedBlock(getNewBlock(intermediateState3_1(), 0), [genesisBlock(), signedBlock(1)], 0) by {
                assume getNewBlock(intermediateState3_1(), 0).header.proposer == 1;
                assume validateEthereumBlock([genesisBlock(), signedBlock(1)], getNewBlock(intermediateState3_1(), 0));
            }
        }
        assert UponProposal(intermediateState3_2(), finalState3(), outPrepare3());
        assert NodeNext(s2().nodes[1], newMessagesReceived3(), s3().nodes[1], outPrepare3() + outProposal3()) by {
            var s:= [currentWithNewMessagesReceived3(), intermediateState3_1(), intermediateState3_2(), finalState3()];
            var o:= [{}, outProposal3(), outPrepare3()];
            forall afterNext, messages | afterNext != finalState3()
                ensures ! (
                    && validNodeState(finalState3())
                    && NodeNextSubStep(finalState3(), afterNext, messages)
                )
            {
                assert !UponNewBlock(finalState3(), afterNext, messages);
                assert !UponBlockTimeout(finalState3(), afterNext, messages) by {
                    assume getNewBlock(finalState3(), 0) == getNewBlock(intermediateState3_1(), 0);
                }
                assert !UponProposal(finalState3(), afterNext, messages);
                assert !UponPrepare(finalState3(), afterNext, messages) by {
                    assert finalState3().messagesReceived == {newBlock(1).message, prepare3(), proposal3()};
                    var p := set m | && m in finalState3().messagesReceived
                                     && m.Prepare?;
                    assert p == {prepare3()};
                    forall QofP | QofP <= validPreparesForHeightRoundAndDigest(
                        finalState3().messagesReceived,
                        2,
                        0,
                        digest(getNewBlock(intermediateState3_1(), 0)),
                        [0,1,2,3]
                    ) ensures |QofP| <= 1
                    {
                        assert QofP <= p;
                        assert |p| == 1;
                        if QofP < p {
                            ThingsIKnowAboutSubset(QofP, p);
                        } else {
                            assert QofP == p;
                            assert |QofP| == |p| == 1;
                        }
                    }
                }
                assert !UponCommit(finalState3(), afterNext, messages);
                assert !UponRoundChange(finalState3(), afterNext, messages);
                assert !UponRoundTimeout(finalState3(), afterNext, messages);
            
            }
        }
        assert DSNextNode(s2(), s3(), outProposal3() + outPrepare3(), multiset{newBlock(1)}, 1);
    }

    lemma ValidStep4(state3: DSState, state4: DSState)
        requires state3 == s3()
        requires state4 == s4()
        requires forall blockchain ::validators(blockchain) == [0,1,2,3]
        ensures DSNextNode(s3(), s4(), outPrepare4(), multiset{newBlock(2), QbftMessageWithRecipient(proposal3(), 2)}, 2);
        ensures DSNext(state3, state4)
    {
        assert validNewBlockMessage([genesisBlock()], newBlock(2).message) by {
            lemmaSignedHash();
        }
        assert UponNewBlock(currentWithNewMessagesReceived4(), intermediateState4(), {});
        assert isValidProposal(proposal3(), intermediateState4()) by {
            lemmaSignedProposal();
            assert validateNonPreparedBlock(getNewBlock(intermediateState3_1(), 0), [genesisBlock(), signedBlock(2)], 0) by {
                assume getNewBlock(intermediateState3_1(), 0).header.proposer == 1;
                assume validateEthereumBlock([genesisBlock(), signedBlock(2)], getNewBlock(intermediateState3_1(), 0));
            }
        }
        assert UponProposal(intermediateState4(), finalState4(), outPrepare4());
        assert NodeNext(s3().nodes[2], newMessagesReceived4(), s4().nodes[2], outPrepare4()) by {
            var s := [currentWithNewMessagesReceived4(), intermediateState4(), finalState4()];
            var o := [{}, outPrepare4()];
            forall afterNext, messages | afterNext != finalState4()
                ensures ! (
                    && validNodeState(finalState4())
                    && NodeNextSubStep(finalState4(), afterNext, messages)
                )
            {
                assert !UponNewBlock(finalState4(), afterNext, messages);
                assert !UponBlockTimeout(finalState4(), afterNext, messages);
                assert !UponProposal(finalState4(), afterNext, messages);
                assert !UponPrepare(finalState4(), afterNext, messages) by 
                {
                    assert finalState4().messagesReceived == {prepare4(), newBlock(2).message, proposal3()};
                    var p := set m | && m in finalState4().messagesReceived
                                     && m.Prepare?;
                    assert p == {prepare4()};
                    forall QofP | QofP <= validPreparesForHeightRoundAndDigest(
                        finalState4().messagesReceived,
                        2,
                        0,
                        digest(getNewBlock(intermediateState3_1(), 0)),
                        [0,1,2,3]
                    ) ensures |QofP| <= 1
                    {
                        assert QofP <= p;
                        assert |p| == 1;
                        if QofP < p {
                            ThingsIKnowAboutSubset(QofP, p);
                        } else {
                            assert QofP == p;
                            assert |QofP| == |p| == 1;
                        }
                    }
                }
                assert !UponCommit(finalState4(), afterNext, messages);
                assert !UponRoundChange(finalState4(), afterNext, messages);
                assert !UponRoundTimeout(finalState4(), afterNext, messages);
            }
        }
        assert DSNextNode(s3(), s4(), outPrepare4(), multiset{newBlock(2), QbftMessageWithRecipient(proposal3(), 2)}, 2);
    }
        
    lemma validStates()
        requires forall blockchain ::validators(blockchain) == [0,1,2,3]
        ensures validDSState(s0())
        ensures validDSState(s1())
        ensures validDSState(s2())
        ensures validDSState(s3())
        ensures validDSState(s4())
    {}

    lemma test()
        requires forall blockchain ::validators(blockchain) == [0,1,2,3]
    {
        var behavior := [s0(), s1(), s2(), s3(), s4()];
        assert |behavior| == 5;
        validStates();
        assert forall i | 0 <= i < |behavior| :: validDSState(behavior[i]);
        ValidStep1(behavior[0], behavior[1]);
        ValidStep2(behavior[1], behavior[2]);
        ValidStep3(behavior[2], behavior[3]);
        ValidStep4(behavior[3], behavior[4]);

        assert forall i | 0 <= i < 4 :: DSNext(behavior[i],behavior[i+1]) by {
            assert DSNext(behavior[0], behavior[1]);
            assert DSNext(behavior[1], behavior[2]);
            assert DSNext(behavior[2], behavior[3]);
            assert DSNext(behavior[3], behavior[4]);
        }

    }

    lemma PseudoLiveness(c:Configuration) returns (behavior: seq<DSState>)
            // requires IsValidConfiguration(c);
            // maybe c can also be included in the return value
            requires c == Configuration([0,1,2,3], genesisBlock(), 1)
            requires forall blockchain ::validators(blockchain) == [0,1,2,3]
            
            ensures |behavior| > 0;
            // ensures DSInit(behavior[0],c);
            ensures (forall i | 0 <= i < |behavior| :: validDSState(behavior[i]))
            ensures (forall i | 0 <= i < |behavior|-1 :: DSNext(behavior[i],behavior[i+1]))
            // There are two honest nodes that have inconsistent blockchains
            // ensures (exists i,j :: 
            //             && isHonest(last(behavior),i) 
            //             && isHonest(last(behavior),j) 
            //             && !consistentBlockchains(last(behavior).nodes[i].blockchain, last(behavior).nodes[j].blockchain))
        {
            behavior := [s0(), s1(), s2(), s3(), s4()];
            assert |behavior| == 5;
            assert DSInit(s0(), c);

            validStates();
            assert forall i | 0 <= i < |behavior| :: validDSState(behavior[i]) by {
                ValidStep1(behavior[0], behavior[1]);
                ValidStep2(behavior[1], behavior[2]);
                ValidStep3(behavior[2], behavior[3]);
                ValidStep4(behavior[3], behavior[4]);
            }

            // initial setup
            assert IsValidConfiguration(c);
            // ValidInitialState(s0());
            

            /// step 1: adversary sends out Proposal messages to itself ///
            ValidStep1(behavior[0], behavior[1]);

            /// step 2: adversary receives Proposal messages and sends NewBlock messages ///
            ValidStep2(behavior[1], behavior[2]);
            
            /// step3: honest node 1 receives NewBlock message 1 and decide, and propose for height 2, and send prepare ///
            ValidStep3(behavior[2], behavior[3]);

            /// step 4: honest node 2 NewBlock message 2 and decide, and send prepare ///
            ValidStep4(behavior[3], behavior[4]);

            assert forall i | 0 <= i < |behavior|-1 :: DSNext(behavior[i],behavior[i+1]) by {
                assert DSNext(behavior[0], behavior[1]);
                assert DSNext(behavior[1], behavior[2]);
                assert DSNext(behavior[2], behavior[3]);
                assert DSNext(behavior[3], behavior[4]);
            }

            // assert !consistentBlockchains(behavior[4].nodes[1].blockchain, behavior[4].nodes[2].blockchain) by {
            //     var rbc1 := fromBlockchainToRawBlockchain(behavior[4].nodes[1].blockchain);
            //     var rbc2 := fromBlockchainToRawBlockchain(behavior[4].nodes[2].blockchain);
            //     assert rbc1[1] != rbc2[1];
            // }


        }
}
    