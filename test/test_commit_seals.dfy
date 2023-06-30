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
        // DS initial state, where node 0 is the faulty node
        var s := StateGeneratorNoAdversary([genesisBlock()], [genesisBlock()], [genesisBlock()], [genesisBlock()]).(adversary := Adversary({}, {0}));
        assume isUniqueSequence(validators([genesisBlock()]))
        && seqToSet(validators([genesisBlock()])) <= seqToSet(c().nodes);
        assume validators([genesisBlock()]) == [0,1,2,3];
        assert DSInit(s, c());

        // adversary send out proposal message with valid quorums of commit seals for two blocks
        var block1 := Block(BlockHeader(0, 0, {}, 1, 0), "block1", []);
        var commitSeals1:set<Signature> := set i | i in {1,2,3} :: signHash(hashBlockForCommitSeal(block1), i);
        lemmaSignedHash();
        // assert signHash(hashBlockForCommitSeal(block1), 1) in commitSeals1;
        // assert signHash(hashBlockForCommitSeal(block1), 2) in commitSeals1;
        // assert signHash(hashBlockForCommitSeal(block1), 3) in commitSeals1;
        // assert signHash(hashBlockForCommitSeal(block1), 1) != signHash(hashBlockForCommitSeal(block1), 2);
        // assert signHash(hashBlockForCommitSeal(block1), 2) != signHash(hashBlockForCommitSeal(block1), 3);
        // assert signHash(hashBlockForCommitSeal(block1), 1) != signHash(hashBlockForCommitSeal(block1), 3);

        assume |commitSeals1| == 3;
        var signedBlock1 := block1.(header := block1.header.(commitSeals := commitSeals1));

        var block2 := Block(BlockHeader(0, 0, {}, 1, 0), "block2", []);
        var commitSeals2:set<Signature> := set i | i in {1,2,3} :: signHash(hashBlockForCommitSeal(block2), i);
        lemmaSignedHash();
        assume |commitSeals2| == 3;
        var signedBlock2 := block2.(header := block2.header.(commitSeals := commitSeals2));

        var proposalPayload := signProposal(UnsignedProposal(0,0,0),0);

        var proposal1 := QbftMessageWithRecipient(Proposal(proposalPayload, signedBlock1, {}, {}), 0);
        var proposal2 := QbftMessageWithRecipient(Proposal(proposalPayload, signedBlock2, {}, {}), 0);
        
        lemmaSignedProposal();
        assert AdversaryNext(s.adversary, {}, s.adversary, {proposal1, proposal2});

        var s1 := s.(environment := s.environment.(allMessagesSent := s.environment.allMessagesSent + multiset{proposal1, proposal2}, messagesSentYetToBeReceived := s.environment.messagesSentYetToBeReceived + multiset{proposal1, proposal2}));
        assert DSNextNode(s, s1, {proposal1, proposal2}, multiset{}, 0);

        // adversary receive the proposal message
        // adversary construct and send different NewBlock message to two honest nodes with the commit seals they received
        var newBlock1 := QbftMessageWithRecipient(NewBlock(signedBlock1), 1);
        var newBlock2 := QbftMessageWithRecipient(NewBlock(signedBlock2), 2);

        var adversary2 := s.adversary.(messagesReceived := s.adversary.messagesReceived + {proposal1.message, proposal2.message});
        assert AdversaryNext(s1.adversary, {proposal1.message, proposal2.message}, adversary2, {newBlock1, newBlock2});

        var s2 := s1.(environment := s1.environment.(allMessagesSent := s1.environment.allMessagesSent + multiset{newBlock1, newBlock2}, messagesSentYetToBeReceived := multiset{newBlock1, newBlock2}), adversary := adversary2);
        assert DSNextNode(s1, s2, {newBlock1, newBlock2}, multiset{proposal1, proposal2}, 0);

        // honest nodes receive the NewBlock and add to blockchain

        // node 1
        var n1 := NodeState([genesisBlock(), signedBlock1], 0, 1, 1, c(), {newBlock1.message}, None, None, None, 1);
        var s3 := s2.(environment := s2.environment.(messagesSentYetToBeReceived := multiset{newBlock2}),
                        nodes := s2.nodes[1 := n1]);
        // assert ValidNewBlock([genesisBlock()], signedBlock1);
        // assert validNewBlockMessage([genesisBlock()], newBlock1.message);
        
        var currentWithNewMessagesReceived1 := NodeState([genesisBlock()], 0, 1, 1, c(), {newBlock1.message}, None, None, None, 0);
        // assert currentWithNewMessagesReceived1 == s2.nodes[1].(
        //     messagesReceived := s2.nodes[1].messagesReceived + {newBlock1.message},
        //     localTime := 1
        // );
        assert UponNewBlock(currentWithNewMessagesReceived1, n1, {});
        assert NodeNextSubStep(currentWithNewMessagesReceived1, s3.nodes[1], {});
        
        assert NodeNext(s2.nodes[1], {newBlock1.message}, s3.nodes[1], {}) by {
            var sequence := [currentWithNewMessagesReceived1, s3.nodes[1]];
            var o:seq<set<QbftMessageWithRecipient>> := [{}];
        }
        assert DSNextNode(s2, s3, {}, multiset{newBlock1}, 1);

        // node 2
        
        var n2 := NodeState([genesisBlock(), signedBlock2], 0, 1, 2, c(), {newBlock2.message}, None, None, None, 1);
        var s4 := s3.(environment := s3.environment.(messagesSentYetToBeReceived := multiset{}),
                        nodes := s3.nodes[2 := n2]);
        assert ValidNewBlock([genesisBlock()], signedBlock2);
        assert validNewBlockMessage([genesisBlock()], newBlock2.message);
        
        var currentWithNewMessagesReceived2 := NodeState([genesisBlock()], 0, 1, 2, c(), {newBlock2.message}, None, None, None, 0);
        // assert currentWithNewMessagesReceived1 == s2.nodes[1].(
        //     messagesReceived := s2.nodes[1].messagesReceived + {newBlock1.message},
        //     localTime := 1
        // );
        assert UponNewBlock(currentWithNewMessagesReceived2, n2, {});
        assert NodeNextSubStep(currentWithNewMessagesReceived2, s4.nodes[2], {});
        
        assert NodeNext(s3.nodes[2], {newBlock2.message}, s4.nodes[2], {}) by {
            var sequence := [currentWithNewMessagesReceived2, s4.nodes[2]];
            var o:seq<set<QbftMessageWithRecipient>> := [{}];
        }
        assume |validators([genesisBlock(), signedBlock1])| > 0;
        assume |validators([genesisBlock(), signedBlock2])| > 0;

        assert DSNextNode(s3, s4, {}, multiset{newBlock2}, 2);
        // check consistency property on the trace
        var rbc1 := fromBlockchainToRawBlockchain(s4.nodes[1].blockchain);
        var rbc2 := fromBlockchainToRawBlockchain(s4.nodes[2].blockchain);
        assert rbc1[1] != rbc2[1];
        assert !consistentBlockchains(s4.nodes[1].blockchain, s4.nodes[2].blockchain);
    }
}