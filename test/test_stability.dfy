include "test_consistency.dfy"

module test_stability {
    import opened test_consistency
    import opened L1_SpecTypes
    import opened L1_SpecNetwork
    import opened L1_Adversary
    import opened L1_DistributedSystem
    import opened L1_Theorems
    import opened L1_TheoremsDefs
    import opened L1_AuxiliaryFunctionsAndLemmas

    function tNormalCase1(i:nat): DSState
    // from empty
    {
        if i == 0 then tEmpty(0)
        else tBlockchain1(0)
    }

    function tNormalCase2(i:nat): DSState
    {
        if i == 0 then tPartialEmpty2(0)
        else tPartialEmpty1(0)
    }

    function tNormalCase3(i:nat): DSState
    {
        if i == 0 then tOnlyGenesis2(0)
        else if i == 1 then tOnlyGenesis1(0)
        else tAllSame1(0)
    }

    function tNormalCase4(i:nat): DSState
    {
        if i == 0 then tOnlyGenesis2(0)
        else if i == 1 then tOnlyGenesis1(0)
        else tLong(0)
    }

    function tNormalCase5(i:nat): DSState
    {
        if i == 0 then tOnlyGenesis2(0)
        else if i == 1 then tOnlyGenesis1(0)
        else tAverage(0)
    }

    lemma testNormalCase() {
        assert consistency(tNormalCase1);
        assert consistency(tNormalCase2);
        assert consistency(tNormalCase3);
        assert consistency(tNormalCase4);
        assert consistency(tNormalCase5);
    }


}