include "../dafny/ver/L1/distr_system_spec/distributed_system.dfy"
include "test_helpers.dfy"

module test_commit_seals {
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

    lemma test() {
        // Generating DS initial state, where node 0 is the faulty node
        var s := StateGeneratorNoAdversary([genesisBlock()], [genesisBlock()], [genesisBlock()], [genesisBlock()]).(adversary := Adversary({}, {0}));
        assume forall blockchain ::validators(blockchain) == [0,1,2,3] && isUniqueSequence(validators(blockchain));
        // assert DSInit(s, c());

        // adversary send out proposal message with valid quorums of commit seals for two different blocks to itself
        var block1 := Block(BlockHeader(0, 0, {}, 1, 0), "block1", []); // a random block with empty commit seals
        var commitSeals1 := {signHash(hashBlockForCommitSeal(block1), 1), signHash(hashBlockForCommitSeal(block1), 2), signHash(hashBlockForCommitSeal(block1), 3)}; // constructing valid commit seals from a quorum of honest nodes
        var signedBlock1 := block1.(header := block1.header.(commitSeals := commitSeals1)); // put the commit seals into the block

        // constructing a different block using the same steps
        var block2 := Block(BlockHeader(0, 0, {}, 1, 0), "block2", []);
        var commitSeals2 := {signHash(hashBlockForCommitSeal(block2), 1), signHash(hashBlockForCommitSeal(block2), 2), signHash(hashBlockForCommitSeal(block2), 3)};
        var signedBlock2 := block2.(header := block2.header.(commitSeals := commitSeals2));

        lemmaSignedHash(); // saying that the sinature is crash-resistant

        var proposalPayload := signProposal(UnsignedProposal(0,0,0),0); // constructing a random proposal payload signed by itself

        var proposal1 := QbftMessageWithRecipient(Proposal(proposalPayload, signedBlock1, {}, {}), 0); // constructing the message type with itself as the recipient
        var proposal2 := QbftMessageWithRecipient(Proposal(proposalPayload, signedBlock2, {}, {}), 0);
        
        // assert AdversaryNext(s.adversary, {}, s.adversary, {proposal1, proposal2}) by {
        //     lemmaSignedProposal();
        // }

        var s1 := s.(environment := s.environment.(allMessagesSent := s.environment.allMessagesSent + multiset{proposal1, proposal2}, messagesSentYetToBeReceived := s.environment.messagesSentYetToBeReceived + multiset{proposal1, proposal2}));
        // assert DSNextNode(s, s1, {proposal1, proposal2}, multiset{}, 0);

        // adversary receives the proposal message
        // and then construct and send different NewBlock message to two honest nodes with the quorums of commit seals they received
        var newBlock1 := QbftMessageWithRecipient(NewBlock(signedBlock1), 1);
        var newBlock2 := QbftMessageWithRecipient(NewBlock(signedBlock2), 2);

        var adversary2 := s.adversary.(messagesReceived := s.adversary.messagesReceived + {proposal1.message, proposal2.message});
        // assert AdversaryNext(s1.adversary, {proposal1.message, proposal2.message}, adversary2, {newBlock1, newBlock2});

        var s2 := s1.(environment := s1.environment.(allMessagesSent := s1.environment.allMessagesSent + multiset{newBlock1, newBlock2}, messagesSentYetToBeReceived := multiset{newBlock1, newBlock2}), adversary := adversary2);
        // assert DSNextNode(s1, s2, {newBlock1, newBlock2}, multiset{proposal1, proposal2}, 0);

        // honest nodes receive the NewBlock and add to blockchain

        // node 1
        
        
        var currentWithNewMessagesReceived1 := NodeState([genesisBlock()], 0, 1, 1, c(), {newBlock1.message}, None, None, None, 0);
        var b := getNewBlock(currentWithNewMessagesReceived1, 0);
        assume b.header.proposer == proposer(0, [genesisBlock()]);
        assert isProposalJustification({}, {}, {}, 1, 0, b, bl => && bl == b, proposer(0, [genesisBlock()]), [0,1,2,3]);
        assert isReceivedProposalJustification({}, {}, 0, b, currentWithNewMessagesReceived1);
        var roundChanges,
                prepares,
                newRound:nat,
                block
                :|
                    isReceivedProposalJustification(roundChanges, prepares, newRound, block, currentWithNewMessagesReceived1);
        var proposal :=
                Proposal(
                    signProposal(
                        UnsignedProposal(
                            |currentWithNewMessagesReceived1.blockchain|,
                            0,
                            digest(block)),
                        currentWithNewMessagesReceived1.id),
                    block,
                    {},
                    {});
        var outQbftMessages :=
                Multicast(
                    validators(currentWithNewMessagesReceived1.blockchain),
                    proposal
                );
        var next := currentWithNewMessagesReceived1.(
                            messagesReceived := currentWithNewMessagesReceived1.messagesReceived + {proposal}
                        );
        assert outQbftMessages == Multicast(
                    validators(currentWithNewMessagesReceived1.blockchain),
                    proposal
                );
        assert next ==  currentWithNewMessagesReceived1.(
                            round := newRound,
                            proposalAcceptedForCurrentRound := Optional.None,
                            timeLastRoundStart :=
                                if newRound > currentWithNewMessagesReceived1.round then
                                    currentWithNewMessagesReceived1.localTime
                                else
                                    currentWithNewMessagesReceived1.timeLastRoundStart,
                            messagesReceived := currentWithNewMessagesReceived1.messagesReceived + {proposal}
                        );
        assert hasReceivedProposalJustification(currentWithNewMessagesReceived1);
        assert UponRoundChange(currentWithNewMessagesReceived1, next, outQbftMessages);
        var proposalBy1 :=
                Proposal(
                    signProposal(
                        UnsignedProposal(
                            |currentWithNewMessagesReceived1.blockchain|,
                            0,
                            digest(block)),
                        currentWithNewMessagesReceived1.id),
                    block,
                    {},
                    {});
        var out1 := Multicast(
                    validators(currentWithNewMessagesReceived1.blockchain),
                    proposalBy1
                );
        var next1 := currentWithNewMessagesReceived1.(
                            round := 0,
                            proposalAcceptedForCurrentRound := Optional.None,
                            timeLastRoundStart :=
                                if 0 > 0 then
                                    currentWithNewMessagesReceived1.localTime
                                else
                                    currentWithNewMessagesReceived1.timeLastRoundStart,
                            messagesReceived := currentWithNewMessagesReceived1.messagesReceived + {proposalBy1}
                        );
        assert hasReceivedProposalJustification(currentWithNewMessagesReceived1);
        assume forall roundChanges, prepares, newRound, b | isReceivedProposalJustification(roundChanges, prepares, newRound, b, currentWithNewMessagesReceived1) :: roundChanges == {} && prepares == {} && newRound == 0 && b == block;
        assert UponRoundChange(currentWithNewMessagesReceived1, next1, out1);
        assert NodeNextSubStep(currentWithNewMessagesReceived1, next1, out1);

        var n1 := NodeState([genesisBlock(), signedBlock1], 0, 1, 1, c(), {newBlock1.message, proposalBy1}, None, None, None, 1);
        var s3 := s2.(environment := s2.environment.(messagesSentYetToBeReceived := multiset{newBlock2}),
                        nodes := s2.nodes[1 := n1]);
        assert UponNewBlock(next1, n1, {});
        assert NodeNextSubStep(next1, n1, {});

        assert DSNextNode(s2, s3, {}, multiset{newBlock1}, 1) by {
            // assert UponNewBlock(currentWithNewMessagesReceived1, n1, {});
            assert NodeNext(s2.nodes[1], {newBlock1.message}, s3.nodes[1], out1) by {
                var sequence := [currentWithNewMessagesReceived1, next1, s3.nodes[1]];
                var o:seq<set<QbftMessageWithRecipient>> := [out1, {}];
                // assume forall afterNext, messages | afterNext != s3.nodes[1] :: !UponRoundChange(s3.nodes[1], afterNext, messages);
        }
        }

        // node 2
        
        // var n2 := NodeState([genesisBlock(), signedBlock2], 0, 1, 2, c(), {newBlock2.message}, None, None, None, 1);
        // var s4 := s3.(environment := s3.environment.(messagesSentYetToBeReceived := multiset{}),
        //                 nodes := s3.nodes[2 := n2]);
        
        // var currentWithNewMessagesReceived2 := NodeState([genesisBlock()], 0, 1, 2, c(), {newBlock2.message}, None, None, None, 0);

        // assert DSNextNode(s3, s4, {}, multiset{newBlock2}, 2) by {
        //     assert UponNewBlock(currentWithNewMessagesReceived2, n2, {});
        //     assert NodeNextSubStep(currentWithNewMessagesReceived2, s4.nodes[2], {});
        //     assert NodeNext(s3.nodes[2], {newBlock2.message}, s4.nodes[2], {}) by {
        //         var sequence := [currentWithNewMessagesReceived2, s4.nodes[2]];
        //         var o:seq<set<QbftMessageWithRecipient>> := [{}];
        //         assert forall afterNext, messages | afterNext != s4.nodes[2] :: !UponBlockTimeout(s4.nodes[2], afterNext, messages);
        //         assert forall afterNext, messages | afterNext != s4.nodes[2] :: !UponPrepare(s4.nodes[2], afterNext, messages);
        //         assert forall afterNext, messages | afterNext != s4.nodes[2] :: !UponCommit(s4.nodes[2], afterNext, messages);
        //         assert forall afterNext, messages | afterNext != s4.nodes[2] :: !UponRoundTimeout(s4.nodes[2], afterNext, messages);
        //         assert forall afterNext, messages | afterNext != s4.nodes[2] :: !UponProposal(s4.nodes[2], afterNext, messages);
        //         assert forall afterNext, messages | afterNext != s4.nodes[2] :: !UponNewBlock(s4.nodes[2], afterNext, messages);
        //         assert !(forall afterNext, messages | afterNext != s4.nodes[2] :: !UponRoundChange(s4.nodes[2], afterNext, messages));
                
        //     }
        // }

        // // check consistency property on the trace
        // assert !consistentBlockchains(s4.nodes[1].blockchain, s4.nodes[2].blockchain) by {
        //     var rbc1 := fromBlockchainToRawBlockchain(s4.nodes[1].blockchain);
        //     var rbc2 := fromBlockchainToRawBlockchain(s4.nodes[2].blockchain);
        //     assert rbc1[1] != rbc2[1];
        // }
    }
}