include "../dafny/ver/L1/theorems.dfy"

/*
// mutant 1: makes all provability tests fail
predicate consistency(t: Trace)
    {
        forall i,n1,n2 
        |
                    && n1 in t(i).nodes.Keys
                    && n2 in t(i).nodes.Keys
                    // && isHonest(t(i),n1)
                    // && isHonest(t(i),n2)
                ::
                consistentBlockchains(t(i).nodes[n1].blockchain, t(i).nodes[n2].blockchain)
    } 
*/

/*
// mutant 2: makes two provability tests fail
predicate consistentBlockchains(bc1:Blockchain, bc2:Blockchain)
    {
        || bc1 <= bc2
        || bc2 <= bc1
            // var rbc1 := fromBlockchainToRawBlockchain(bc1);
            // var rbc2 := fromBlockchainToRawBlockchain(bc2);
            // || rbc1 <= rbc2
            // || rbc2 <= rbc1 
    }     
*/

/*
// mutant 3: makes one correctness test fail
predicate consistentBlockchains(bc1:Blockchain, bc2:Blockchain)
    {
        forall i:nat | 0 < i < |bc1| && i < |bc2| ::fromBlockToRawBlock(bc1[i]) == fromBlockToRawBlock(bc2[i])
            // var rbc1 := fromBlockchainToRawBlockchain(bc1);
            // var rbc2 := fromBlockchainToRawBlockchain(bc2);
            // || rbc1 <= rbc2
            // || rbc2 <= rbc1
    } 

*/

/*
// mutant 4: wrong variable substitution (n2 -> n1)
predicate consistency(t: Trace)
    {
        forall i,n1,n2 |
                    // && n1 in t(i).nodes.Keys
                    // && n2 in t(i).nodes.Keys
                    && isHonest(t(i),n1)
                    && isHonest(t(i),n2)
                ::
                consistentBlockchains(t(i).nodes[n1].blockchain, t(i).nodes[n1].blockchain)
    }  
*/

/*
// mutant 5: || -> &&
predicate consistentBlockchains(bc1:Blockchain, bc2:Blockchain)
    {
        // || bc1 <= bc2
        // || bc2 <= bc1
        // forall i:nat | 0 < i < |bc1| && i < |bc2| ::fromBlockToRawBlock(bc1[i]) == fromBlockToRawBlock(bc2[i])
            var rbc1 := fromBlockchainToRawBlockchain(bc1);
            var rbc2 := fromBlockchainToRawBlockchain(bc2);
            && rbc1 <= rbc2
            && rbc2 <= rbc1
    }     

*/

/* 
// mutant 6: <= -> <
predicate consistentBlockchains(bc1:Blockchain, bc2:Blockchain)
    {
        // || bc1 <= bc2
        // || bc2 <= bc1
        // forall i:nat | 0 < i < |bc1| && i < |bc2| ::fromBlockToRawBlock(bc1[i]) == fromBlockToRawBlock(bc2[i])
            var rbc1 := fromBlockchainToRawBlockchain(bc1);
            var rbc2 := fromBlockchainToRawBlockchain(bc2);
            || rbc1 < rbc2
            || rbc2 < rbc1
    }     
*/
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
        requires t(0).nodes.Keys - t(0).adversary.byz == {0,1,2}
        requires fromBlockchainToRawBlockchain(t(0).nodes[1].blockchain) <= fromBlockchainToRawBlockchain(t(0).nodes[0].blockchain) || fromBlockchainToRawBlockchain(t(0).nodes[0].blockchain) <= fromBlockchainToRawBlockchain(t(0).nodes[1].blockchain)
        requires t(0).nodes[2].blockchain == []
        ensures consistency(t)
    {}

    lemma test_consistency_provability_4(t:Trace)
        // one empty blockchain
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys - t(0).adversary.byz == {0,1,2}
        requires |t(0).nodes[0].blockchain| == 1
        requires |t(0).nodes[1].blockchain| > 1
        requires fromBlockToRawBlock(t(0).nodes[1].blockchain[0]) == fromBlockToRawBlock(t(0).nodes[0].blockchain[0])
        requires t(0).nodes[2].blockchain == []
        ensures consistency(t)
    {}

    lemma test_consistency_provability_5(t:Trace)
        // one empty blockchain
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys - t(0).adversary.byz == {0,1,2}
        requires fromBlockchainToRawBlockchain(t(0).nodes[1].blockchain) == fromBlockchainToRawBlockchain(t(0).nodes[0].blockchain)
        requires t(0).nodes[2].blockchain == []
        ensures consistency(t)
    {
        forall i:nat | i < |t(0).nodes[1].blockchain| 
            ensures fromBlockToRawBlock(t(0).nodes[1].blockchain[i]) == fromBlockToRawBlock(t(0).nodes[0].blockchain[i]) 
        {
            assert fromBlockchainToRawBlockchain(t(0).nodes[1].blockchain)[i] == fromBlockchainToRawBlockchain(t(0).nodes[0].blockchain)[i];
        }
    }

    lemma test_consistency_provability_6(t:Trace)
        // one empty blockchain
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys - t(0).adversary.byz == {0,1,2}
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
        requires t(0).nodes.Keys - t(0).adversary.byz == {0,1,2}
        requires t(0).nodes[0].blockchain == t(0).nodes[1].blockchain == t(0).nodes[2].blockchain
        ensures consistency(t)
    {}

    lemma test_consistency_provability_8(t:Trace)
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys - t(0).adversary.byz == {0,1,2}
        requires |t(0).nodes[0].blockchain| == 1
        requires |t(0).nodes[1].blockchain| > 1
        requires t(0).nodes[1].blockchain[0] == t(0).nodes[0].blockchain[0]
        requires t(0).nodes[1].blockchain == t(0).nodes[2].blockchain
        ensures consistency(t)
    {}

    lemma test_consistency_provability_9(t:Trace)
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys - t(0).adversary.byz == {0,1,2}
        requires |t(0).nodes[0].blockchain| > 1
        requires |t(0).nodes[1].blockchain| == 1
        requires t(0).nodes[1].blockchain[0] == t(0).nodes[0].blockchain[0]
        requires t(0).nodes[1].blockchain == t(0).nodes[2].blockchain
        ensures consistency(t)
    {}

    lemma test_consistency_provability_10(t:Trace)
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys - t(0).adversary.byz == {0,1,2}
        requires |t(0).nodes[0].blockchain| == 1
        requires |t(0).nodes[1].blockchain| == 3
        requires t(0).nodes[1].blockchain[0] == t(0).nodes[0].blockchain[0]
        requires |t(0).nodes[2].blockchain| == 5
        requires t(0).nodes[1].blockchain[0] == t(0).nodes[2].blockchain[0]
        requires t(0).nodes[1].blockchain[1] == t(0).nodes[2].blockchain[1]
        requires t(0).nodes[1].blockchain[2] == t(0).nodes[2].blockchain[2]
        ensures consistency(t)
    {}

    lemma test_consistency_provability_non_const_t(t:Trace)
        requires forall i | i > 1 :: t(i) == t(1)
        requires t(1).nodes.Keys - t(1).adversary.byz == {0,1,2}
        requires t(1).nodes[0].blockchain == []
        requires t(1).nodes[1].blockchain == []
        requires t(0).nodes.Keys - t(0).adversary.byz == {0,1,2}
        requires t(0).nodes[1].blockchain <= t(0).nodes[0].blockchain || t(0).nodes[0].blockchain <= t(0).nodes[1].blockchain
        requires t(0).nodes[2].blockchain == []
        ensures consistency(t)
    {}

    lemma test_consistency_provability_no_node(t:Trace)
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys - t(0).adversary.byz == {}
        ensures consistency(t)
    {}

    lemma test_consistency_provability_one_node(t:Trace)
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys - t(0).adversary.byz == {0}
        ensures consistency(t)
    {}

    lemma test_consistency_provability_one_node'(t:Trace)
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys - t(0).adversary.byz == {5}
        ensures consistency(t)
    {}

    lemma test_consistency_provability_two_nodes(t:Trace)
        requires forall i, j :: t(i) == t(j)
        requires t(0).nodes.Keys - t(0).adversary.byz == {0,1}
        requires t(0).nodes[1].blockchain <= t(0).nodes[0].blockchain || t(0).nodes[0].blockchain <= t(0).nodes[1].blockchain
        ensures consistency(t)
    {}


}