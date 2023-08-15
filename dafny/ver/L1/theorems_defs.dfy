include "../../spec/L1/types.dfy"
include "distr_system_spec/common_functions.dfy"


module L1_TheoremsDefs {

    import opened L1_SpecTypes
    import opened L1_AuxiliaryFunctionsAndLemmas

    predicate consistentBlockchains(bc1:Blockchain, bc2:Blockchain)
    {
        // || bc1 <= bc2
        // || bc2 <= bc1
        // forall i:nat | 0 < i < |bc1| && i < |bc2| ::fromBlockToRawBlock(bc1[i]) == fromBlockToRawBlock(bc2[i])
            var rbc1 := fromBlockchainToRawBlockchain(bc1);
            var rbc2 := fromBlockchainToRawBlockchain(bc2);
            || rbc1 <= rbc2
            || rbc2 <= rbc1
    }     
}