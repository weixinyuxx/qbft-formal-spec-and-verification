include "../dafny/ver/L1/distr_system_spec/distributed_system.dfy"
include "test_helpers.dfy"

module test_nonempty_commit_seal {
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
        var s0 := StateGeneratorNoAdversary([genesisBlock()], [genesisBlock()], [genesisBlock()], [genesisBlock()]);
        assume isUniqueSequence(validators([genesisBlock()]))
        && seqToSet(validators([genesisBlock()])) <= seqToSet(c().nodes);
        assume |validators([genesisBlock()])| > 0;
        assert DSInit(s0, c());
        assume proposer(0,[genesisBlock()]) == 0;
        var n0 := NodeState([genesisBlock()], 0, 0, 0, c(), {}, None, None, None, 0);
        var n0' := n0.(
            localTime := 1
        );
        var block := getNewBlock(n0', 0);
        var proposal :=
                Proposal(
                    signProposal(
                        UnsignedProposal(
                            |n0'.blockchain|,
                            0,
                            digest(block)),
                        n0'.id),
                    block,
                    {},
                    {});
        var outQbftMessages := Multicast(
                    validators(n0'.blockchain),
                    proposal
                );
        var n1 := n0.(
                            messagesReceived := n0.messagesReceived + {proposal},
                            localTime := 1
                        );
        
        assert UponBlockTimeout(n0', n1, outQbftMessages);

        var env1 := Network([0,1,2,3], multiset(outQbftMessages), 0, multiset(outQbftMessages));
        var s1 := s0.(environment := env1, nodes := s0.nodes[0 := n1]);
        assert validDSState(s0);
        assert DSNext(s0, s1) by {
            var s := [n0', n1];
            var o := [outQbftMessages];
            assert |s| >= 2;
            assert |o| == |s| - 1;
            assert outQbftMessages == setUnionOnSeq(o);
            assert NodeNextSubStep(n0', n1, outQbftMessages);
            assert validNodeState(n1);

            // assert (forall afterNext, messages | afterNext != n1 :: 
            //     !(
            //         // && validNodeState(s[|s|-1])
            //         && NodeNextSubStep(n1, afterNext, messages)
            //     )
            // );
            assert NodeNext(n0, {}, n1, outQbftMessages);
            assert DSNextNode(s0, s1, outQbftMessages, multiset{}, 0);
        }
        
    }
}