include "../dafny/ver/L1/theorems.dfy"


module test_helpers {
import opened L1_SpecTypes
import opened L1_SpecNetwork
import opened L1_Adversary
import opened L1_DistributedSystem
import opened L1_Theorems
import opened L1_TheoremsDefs
import opened L1_AuxiliaryFunctionsAndLemmas

// proposer 0,1,2,3
function b1(): Block
{
    var b1 := Block(BlockHeader(0,0,{0},0,0), "the first proposal", ["trans1s"]);
    b1
}
function b2(): Block
{
    var b2 := Block(BlockHeader(1,1,{0},1,3), "the second proposal", ["trans2s", "dummy transactions"]);
    b2
}
function b3(): Block
{
    var b3 := Block(BlockHeader(2,2,{0},2,5), "the third proposal", ["trans3s"]);
    b3
}
function genesisBlock(): Block
{
    var header := BlockHeader(1, 0, {}, 0, 0);
    Block(header, "", [])
}
function c(): Configuration
{
    Configuration([0,1,2,3], genesisBlock(), 0)
}
function BasicState(): DSState
{
    var env := Network([0,1,2,3], multiset{}, 0, multiset{});
    var config := c();
    DSState(config, env, map[], Adversary({}, {}))
}
function StateGeneratorNoAdversary(blockchain0: Blockchain, blockchain1: Blockchain, blockchain2: Blockchain, blockchain3: Blockchain): DSState
{
    var n0 := NodeState(blockchain0, 0, 0, 0, c(), {}, None, None, None, 0);
    var n1 := NodeState(blockchain1, 0, 0, 1, c(), {}, None, None, None, 0);
    var n2 := NodeState(blockchain2, 0, 0, 2, c(), {}, None, None, None, 0);
    var n3 := NodeState(blockchain3, 0, 0, 3, c(), {}, None, None, None, 0);

    var nodes := map[0 := n0, 1 := n1, 2 := n2, 3:= n3];
    BasicState().(nodes := nodes)
}

}
