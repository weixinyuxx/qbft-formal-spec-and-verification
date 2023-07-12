include "../dafny/ver/L1/distr_system_spec/distributed_system.dfy"
include "../dafny/spec/L1/node_auxiliary_functions.dfy"
include "test_helpers.dfy"

module test_impl {
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

    lemma getNewBlockCanGetValidCommitSeals()
    {
        assume forall blockchain ::validators(blockchain) == [0,1,2,3];
        var block1 := Block(BlockHeader(0, 0, {}, 1, 0), 1, []); // a random block with empty commit seals
        var commitSeals1 := {signHash(hashBlockForCommitSeal(block1), 1), signHash(hashBlockForCommitSeal(block1), 2), signHash(hashBlockForCommitSeal(block1), 3)}; // constructing valid commit seals from a quorum of honest nodes
        var signedBlock1 := block1.(header := block1.header.(commitSeals := commitSeals1)); // put the commit seals into the block

        var n0 := NodeState([genesisBlock()], 0, 0, 0, c(), {}, None, None, None, 0);
        // assert getNewBlock(n0, 0) != signedBlock1;
    }

    lemma testNewBlock(){
        // Generating DS initial state, where node 0 is the faulty node
        var s := StateGeneratorNoAdversary([genesisBlock()], [genesisBlock()], [genesisBlock()], [genesisBlock()]).(adversary := Adversary({}, {0}));
        assume forall blockchain ::validators(blockchain) == [0,1,2,3] && isUniqueSequence(validators(blockchain));
        assert DSInit(s, c());

        // 
        var block1 := Block(BlockHeader(0, 0, {}, 1, 0), 1, []); // a random block with empty commit seals
        var commitSeals1 := {signHash(hashBlockForCommitSeal(block1), 1), signHash(hashBlockForCommitSeal(block1), 2), signHash(hashBlockForCommitSeal(block1), 3)}; // constructing valid commit seals from a quorum of honest nodes
        var signedBlock1 := block1.(header := block1.header.(commitSeals := commitSeals1)); // put the commit seals into the block

    }
}
