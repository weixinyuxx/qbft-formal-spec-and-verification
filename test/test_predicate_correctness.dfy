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

    lemma test_consistency_correctness_1(t:Trace)
        // one empty blockchain
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys - t(0).adversary.byz == {0,1,2}
        requires |t(0).nodes[0].blockchain| == 1
        requires |t(0).nodes[1].blockchain| == 1
        requires fromBlockToRawBlock(t(0).nodes[0].blockchain[0]) != fromBlockToRawBlock(t(0).nodes[1].blockchain[0])
        ensures !consistency(t)
    {
        var rbc1 := fromBlockchainToRawBlockchain(t(0).nodes[0].blockchain);
        var rbc2 := fromBlockchainToRawBlockchain(t(0).nodes[1].blockchain);
        assert rbc1[0] != rbc2[0];
    }

    lemma test_consistency_correctness_2(t:Trace)
        requires forall i, j :: t(i) == t(j)
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
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys - t(0).adversary.byz == {0,1,2}
        requires |t(0).nodes[0].blockchain| == 5
        requires |t(0).nodes[1].blockchain| == 7
        requires fromBlockToRawBlock(t(0).nodes[0].blockchain[3]) != fromBlockToRawBlock(t(0).nodes[1].blockchain[3])
        ensures !consistency(t)
    {
        var rbc1 := fromBlockchainToRawBlockchain(t(0).nodes[0].blockchain);
        var rbc2 := fromBlockchainToRawBlockchain(t(0).nodes[1].blockchain);
        assert rbc1[3] != rbc2[3];
    }
}