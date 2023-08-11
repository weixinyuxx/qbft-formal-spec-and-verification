include "../dafny/ver/L1/theorems.dfy"

module test_consistency_provability {
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


    lemma test_consistency_provability_1(t:Trace)
        // three empty blockchains
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys - t(0).adversary.byz == {0,1,2}
        requires t(0).nodes[0].blockchain == []
        requires t(0).nodes[1].blockchain == []
        requires t(0).nodes[2].blockchain == []
        ensures consistency(t)
    {}

    lemma test_consistency_provability_2(t:Trace)
        // two empty blockchains
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys - t(0).adversary.byz == {0,1,2}
        requires t(0).nodes[1].blockchain == []
        requires t(0).nodes[2].blockchain == []
        ensures consistency(t)
    {}

    lemma test_consistency_provability_3(t:Trace)
        // one empty blockchain
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys == {0,1,2}
        requires t(0).adversary.byz == {}
        requires t(0).nodes[1].blockchain <= t(0).nodes[0].blockchain || t(0).nodes[0].blockchain <= t(0).nodes[1].blockchain
        requires t(0).nodes[2].blockchain == []
        ensures consistency(t)
    {}

    lemma test_consistency_provability_4(t:Trace)
        // one empty blockchain
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys == {0,1,2}
        requires t(0).adversary.byz == {}
        requires |t(0).nodes[0].blockchain| == 1
        requires |t(0).nodes[1].blockchain| > 1
        requires t(0).nodes[1].blockchain[0] == t(0).nodes[0].blockchain[0]
        requires t(0).nodes[2].blockchain == []
        ensures consistency(t)
    {}

    lemma test_consistency_provability_5(t:Trace)
        // one empty blockchain
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys == {0,1,2}
        requires t(0).adversary.byz == {}
        requires t(0).nodes[1].blockchain == t(0).nodes[0].blockchain
        requires t(0).nodes[2].blockchain == []
        ensures consistency(t)
    {}

    lemma test_consistency_provability_6(t:Trace)
        // one empty blockchain
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys == {0,1,2}
        requires t(0).adversary.byz == {}
        requires |t(0).nodes[0].blockchain| == 3
        requires |t(0).nodes[1].blockchain| >= 3
        requires t(0).nodes[1].blockchain[0] == t(0).nodes[0].blockchain[0]
        requires t(0).nodes[1].blockchain[1] == t(0).nodes[0].blockchain[1]
        requires t(0).nodes[1].blockchain[2] == t(0).nodes[0].blockchain[2]
        requires t(0).nodes[2].blockchain == []
        ensures consistency(t)
    {}

    lemma test_consistency_provability_7(t:Trace)
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys == {0,1,2}
        requires t(0).adversary.byz == {}
        requires t(0).nodes[0].blockchain == t(0).nodes[1].blockchain == t(0).nodes[2].blockchain
        ensures consistency(t)
    {}

    lemma test_consistency_provability_8(t:Trace)
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys == {0,1,2}
        requires t(0).adversary.byz == {}
        requires |t(0).nodes[0].blockchain| == 1
        requires |t(0).nodes[1].blockchain| > 1
        requires t(0).nodes[1].blockchain[0] == t(0).nodes[0].blockchain[0]
        requires t(0).nodes[1].blockchain == t(0).nodes[2].blockchain
        ensures consistency(t)
    {}

    lemma test_consistency_provability_9(t:Trace)
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys == {0,1,2}
        requires t(0).adversary.byz == {}
        requires |t(0).nodes[0].blockchain| == 1
        requires |t(0).nodes[1].blockchain| == 3
        requires t(0).nodes[1].blockchain[0] == t(0).nodes[0].blockchain[0]
        requires |t(0).nodes[2].blockchain| == 5
        requires t(0).nodes[1].blockchain[0] == t(0).nodes[2].blockchain[0]
        requires t(0).nodes[1].blockchain[1] == t(0).nodes[2].blockchain[1]
        requires t(0).nodes[1].blockchain[2] == t(0).nodes[2].blockchain[2]
        ensures consistency(t)
    {}
}