include "../dafny/ver/L1/theorems.dfy"

module test_consistency_correctness {
    import opened L1_SpecTypes
    import opened L1_SpecNetwork
    import opened L1_Adversary
    import opened L1_DistributedSystem
    import opened L1_Theorems
    import opened L1_TheoremsDefs
    import opened L1_AuxiliaryFunctionsAndLemmas
    import opened L1_AuxFunctionsProof
    import opened EETraceDefs
    import opened L1_TraceInstrumentedLemmas
    import opened L1_TraceGeneralLemmas    

    // break into finer grains
    lemma test_consistency_correctness_1(t:Trace)
        // one empty blockchain
        requires t(0).nodes.Keys - t(0).adversary.byz == {0,1,2}
        requires |t(0).nodes[0].blockchain| == 1
        requires |t(0).nodes[1].blockchain| == 1
        requires fromBlockToRawBlock(t(0).nodes[0].blockchain[0]) != fromBlockToRawBlock(t(0).nodes[1].blockchain[0])
        ensures !consistency(t)
    {
        var rbc1 := fromBlockchainToRawBlockchain(t(0).nodes[0].blockchain);
        var rbc2 := fromBlockchainToRawBlockchain(t(0).nodes[1].blockchain);
        assert rbc1[0] != rbc2[0];

        // assert !consistentBlockchains(t(0).nodes[0].blockchain, t(0).nodes[1].blockchain);
    }

    lemma test_consistency_correctness_2(t:Trace)
        requires t(0).nodes.Keys - t(0).adversary.byz == {0,1,2}
        requires |t(0).nodes[0].blockchain| == 2
        requires |t(0).nodes[1].blockchain| == 2
        requires fromBlockToRawBlock(t(0).nodes[0].blockchain[0]) == fromBlockToRawBlock(t(0).nodes[1].blockchain[0])
        requires fromBlockToRawBlock(t(0).nodes[0].blockchain[1]) != fromBlockToRawBlock(t(0).nodes[1].blockchain[1])
        ensures !consistency(t)
    {
        var rbc1 := fromBlockchainToRawBlockchain(t(0).nodes[0].blockchain);
        var rbc2 := fromBlockchainToRawBlockchain(t(0).nodes[1].blockchain);
        assert rbc1[1] != rbc2[1];
    }

    lemma test_consistency_correctness_3(t:Trace)
        requires t(0).nodes.Keys - t(0).adversary.byz == {0,1,2}
        requires |t(0).nodes[0].blockchain| == 3
        requires |t(0).nodes[1].blockchain| == 3
        requires fromBlockToRawBlock(t(0).nodes[0].blockchain[0]) != fromBlockToRawBlock(t(0).nodes[1].blockchain[0])
        requires fromBlockToRawBlock(t(0).nodes[0].blockchain[1]) == fromBlockToRawBlock(t(0).nodes[1].blockchain[1])
        ensures !consistency(t)
    {
        var rbc1 := fromBlockchainToRawBlockchain(t(0).nodes[0].blockchain);
        var rbc2 := fromBlockchainToRawBlockchain(t(0).nodes[1].blockchain);
        assert rbc1[0] != rbc2[0];
    }

    lemma test_consistency_correctness_4(t:Trace)
        requires t(0).nodes.Keys - t(0).adversary.byz == {0,1,2}
        requires |t(0).nodes[0].blockchain| == 5
        requires |t(0).nodes[1].blockchain| == 7
        requires exists i:nat | i < 5 :: fromBlockToRawBlock(t(0).nodes[0].blockchain[i]) != fromBlockToRawBlock(t(0).nodes[1].blockchain[i])
        ensures !consistency(t)
    {
        var i:nat :| i < 5 && fromBlockToRawBlock(t(0).nodes[0].blockchain[i]) != fromBlockToRawBlock(t(0).nodes[1].blockchain[i]);
        var rbc1 := fromBlockchainToRawBlockchain(t(0).nodes[0].blockchain);
        var rbc2 := fromBlockchainToRawBlockchain(t(0).nodes[1].blockchain);
        assert rbc1[i] != rbc2[i];
    }

    lemma test_consistency_correctness_non_constant_t(t:Trace)
        requires exists i:nat :: 
            && t(i).nodes.Keys - t(i).adversary.byz == {0,1,2}
            && |t(i).nodes[0].blockchain| == 1
            && |t(i).nodes[1].blockchain| == 1
            && fromBlockToRawBlock(t(i).nodes[0].blockchain[0]) != fromBlockToRawBlock(t(i).nodes[1].blockchain[0])
        ensures !consistency(t)
    {
        var i :| && t(i).nodes.Keys - t(i).adversary.byz == {0,1,2}
                && |t(i).nodes[0].blockchain| == 1
                && |t(i).nodes[1].blockchain| == 1
                && fromBlockToRawBlock(t(i).nodes[0].blockchain[0]) != fromBlockToRawBlock(t(i).nodes[1].blockchain[0]);
        var rbc1 := fromBlockchainToRawBlockchain(t(i).nodes[0].blockchain);
        var rbc2 := fromBlockchainToRawBlockchain(t(i).nodes[1].blockchain);
        assert rbc1[0] != rbc2[0];
    }

    lemma test_consistency_correctness_two_nodes(t:Trace)
        requires t(0).nodes.Keys - t(0).adversary.byz == {0,1}
        requires |t(0).nodes[0].blockchain| == 1
        requires |t(0).nodes[1].blockchain| == 1
        requires fromBlockToRawBlock(t(0).nodes[0].blockchain[0]) != fromBlockToRawBlock(t(0).nodes[1].blockchain[0])
        ensures !consistency(t)
    {
        var rbc1 := fromBlockchainToRawBlockchain(t(0).nodes[0].blockchain);
        var rbc2 := fromBlockchainToRawBlockchain(t(0).nodes[1].blockchain);
        assert rbc1[0] != rbc2[0];
    }

    lemma test_consistency_correctness_more_nodes(t:Trace)
        requires t(0).nodes.Keys - t(0).adversary.byz >= {0,1,2}
        requires |t(0).nodes[2].blockchain| == 1
        requires |t(0).nodes[1].blockchain| == 1
        requires fromBlockToRawBlock(t(0).nodes[2].blockchain[0]) != fromBlockToRawBlock(t(0).nodes[1].blockchain[0])
        ensures !consistency(t)
    {
        var rbc1 := fromBlockchainToRawBlockchain(t(0).nodes[2].blockchain);
        var rbc2 := fromBlockchainToRawBlockchain(t(0).nodes[1].blockchain);
        assert rbc1[0] != rbc2[0];
    }
}