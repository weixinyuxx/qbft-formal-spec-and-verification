include "../dafny/ver/L1/theorems.dfy"

module test_consistency {
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
        var b1 := Block(BlockHeader(0,0,{0},0,0), 1, ["trans1s"]);
        b1
    }
    function b2(): Block
    {
        var b2 := Block(BlockHeader(1,1,{0},1,3), 2, ["trans2s", "dummy transactions"]);
        b2
    }
    function b3(): Block
    {
        var b3 := Block(BlockHeader(2,2,{0},2,5), 3, ["trans3s"]);
        b3
    }
    function genesisBlock(): Block
    {
        var header := BlockHeader(1, 0, {}, 0, 0);
        Block(header, 0, [])
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


    ///// normal case /////
    function tBlockchain1(i:nat): DSState
    // normal case
    {
        var blockchain1 := [b1()];
        var blockchain2 := [b1(),b2()];
        var blockchain3 := [b1(),b2(),b3()];
        var blockchain4 := [b1(),b2()];
        StateGeneratorNoAdversary(blockchain1, blockchain2, blockchain3, blockchain4)
    }

    function tEmpty(i:nat): DSState
    // all empty
    {
        StateGeneratorNoAdversary([], [], [], [])
    }

    function tPartialEmpty1(i:nat): DSState
    // partially empty
    {
        StateGeneratorNoAdversary([b1(), b2(), b3()], [b1()], [], [])
    }


    function tPartialEmpty2(i:nat): DSState
    {
        StateGeneratorNoAdversary([b1()], [], [], [])
    }

    function tOnlyGenesis1(i:nat): DSState
    {
        StateGeneratorNoAdversary([genesisBlock()], [genesisBlock()], [genesisBlock()], [genesisBlock()])
    }
    
    function tOnlyGenesis2(i:nat): DSState
    {
        StateGeneratorNoAdversary([genesisBlock()], [genesisBlock()], [], [])
    }

    function tNoGenesis(i:nat): DSState
    // is it ok to have no genesis block
    {
        var blockchain := [b1(), b1(), b2(), b3()];
        StateGeneratorNoAdversary(blockchain, blockchain, [], blockchain)
    }

    function tAllSame1(i:nat): DSState
    {
        var blockchain := [genesisBlock(), b1(), b2(), b3()];
        StateGeneratorNoAdversary(blockchain, blockchain, blockchain, blockchain)
    }

    function tAllSame2(i:nat): DSState
    {
        var blockchain := [b1()];
        StateGeneratorNoAdversary(blockchain, blockchain, blockchain, blockchain)
    }

    function tLong(i:nat): DSState
    {
        var blockchain1 := [genesisBlock(), b1(), b2(), b3(), b1(), b2(), b3()];
        var blockchain2 := [genesisBlock(), b1()];
        var blockchain3 := [genesisBlock(), b1(), b2(), b3()];
        var blockchain4 := [genesisBlock()];
        StateGeneratorNoAdversary(blockchain1, blockchain2, blockchain3, blockchain4)
    }

    function tAverage(i:nat): DSState
    {
        var blockchain1 := [genesisBlock(), b1(), b2()];
        var blockchain2 := [genesisBlock(), b1()];
        var blockchain3 := [genesisBlock(), b1(), b2(), b3()];
        var blockchain4 := [genesisBlock(), b1(), b2()];
        StateGeneratorNoAdversary(blockchain1, blockchain2, blockchain3, blockchain4)
    }


    /// adversary exists ///// (but are limited to one)
    function tAdv1(i:nat): DSState
    // benign adversary
    {
        var blockchain1 := [genesisBlock(), b1(), b2()];
        var blockchain2 := [genesisBlock(), b1()];
        var blockchain3 := [genesisBlock(), b1(), b2(), b3()];
        var blockchain4 := [genesisBlock(), b1(), b2()];
        StateGeneratorNoAdversary(blockchain1, blockchain2, blockchain3, blockchain4).(adversary := Adversary({}, {3}))
    }

    function tAdv2(i:nat): DSState
    {
        var blockchain1 := [genesisBlock(), b1(), b3(), b2()];
        var blockchain2 := [genesisBlock(), b1()];
        var blockchain3 := [genesisBlock(), b1(), b2(), b3()];
        var blockchain4 := [genesisBlock(), b1(), b2()];
        StateGeneratorNoAdversary(blockchain1, blockchain2, blockchain3, blockchain4).(adversary := Adversary({}, {0}))
    }

    function tAdv3(i:nat): DSState
    {
        var blockchain1 := [genesisBlock(), b1(), b1()];
        var blockchain2 := [genesisBlock(), b1()];
        var blockchain3 := [genesisBlock(), b1(), b2(), b3()];
        var blockchain4 := [genesisBlock(), b1(), b2()];
        StateGeneratorNoAdversary(blockchain1, blockchain2, blockchain3, blockchain4).(adversary := Adversary({}, {0}))
    }

    function tAdv4(i:nat): DSState
    {
        var blockchain1 := [genesisBlock(), b1(), b3()];
        var blockchain2 := [genesisBlock(), b1()];
        var blockchain3 := [genesisBlock(), b1(), b2()];
        var blockchain4 := [genesisBlock(), b1(), b2()];
        StateGeneratorNoAdversary(blockchain1, blockchain2, blockchain3, blockchain4).(adversary := Adversary({}, {0}))
    }

    function tAdv5(i:nat): DSState
    {
        var blockchain1 := [b1(), b3(), b2()];
        var blockchain2 := [genesisBlock(), b1()];
        var blockchain3 := [genesisBlock(), b1(), b2(), b3()];
        var blockchain4 := [genesisBlock(), b1(), b2()];
        StateGeneratorNoAdversary(blockchain1, blockchain2, blockchain3, blockchain4).(adversary := Adversary({}, {0}))
    }


    ///// Invalid cases /////
    function tInvalid1(i:nat): DSState
    // benign adversary
    {
        var blockchain1 := [genesisBlock(), b1(), b2()];
        var blockchain2 := [genesisBlock(), b3()];
        var blockchain3 := [genesisBlock(), b1(), b2(), b3()];
        var blockchain4 := [genesisBlock(), b1(), b2()];
        StateGeneratorNoAdversary(blockchain1, blockchain2, blockchain3, blockchain4)
    }

    function tInvalid2(i:nat): DSState
    {
        var blockchain1 := [genesisBlock(), b1(), b3(), b2()];
        var blockchain2 := [genesisBlock(), b1()];
        var blockchain3 := [genesisBlock(), b1(), b2(), b3()];
        var blockchain4 := [genesisBlock(), b1(), b2()];
        StateGeneratorNoAdversary(blockchain1, blockchain2, blockchain3, blockchain4)
    }

    function tInvalid3(i:nat): DSState
    {
        var blockchain1 := [genesisBlock(), b1(), b1()];
        var blockchain2 := [genesisBlock(), b1()];
        var blockchain3 := [genesisBlock(), b1(), b2(), b3()];
        var blockchain4 := [genesisBlock(), b1(), b2()];
        StateGeneratorNoAdversary(blockchain1, blockchain2, blockchain3, blockchain4)
    }

    function tInvalid4(i:nat): DSState
    {
        var blockchain1 := [genesisBlock(), b1(), b3()];
        var blockchain2 := [genesisBlock(), b1()];
        var blockchain3 := [genesisBlock(), b1(), b2()];
        var blockchain4 := [genesisBlock(), b1(), b2()];
        StateGeneratorNoAdversary(blockchain1, blockchain2, blockchain3, blockchain4)
    }

    function tInvalid5(i:nat): DSState
    {
        var blockchain1 := [b1(), b3(), b2()];
        var blockchain2 := [genesisBlock(), b1()];
        var blockchain3 := [genesisBlock(), b1(), b2(), b3()];
        var blockchain4 := [genesisBlock(), b1(), b2()];
        StateGeneratorNoAdversary(blockchain1, blockchain2, blockchain3, blockchain4)
    }



    ///// Other states ///// --- 
    function tInvalidConfig1(i:nat): DSState
    {
        var header := BlockHeader(5, 10, {0, 1}, 10, 10);
        var randomBlock := Block(header, 324, ["transaction1", "transaction2"]);
        var c := Configuration([], randomBlock, 10000);
        tBlockchain1(0).(configuration := c)
    }

    function tInvalidConfig2(i:nat): DSState
    {
        var header := BlockHeader(1, 0, {}, 0, 0);
        var randomBlock := Block(header, 324, []);
        var c := Configuration([1,3,4,2], randomBlock, 10000);
        tBlockchain1(0).(configuration := c)
    }

    function tInvalidEnv1(i:nat): DSState
    { 
        tBlockchain1(0).(environment := Network([], multiset{QbftMessageWithRecipient(Prepare(SignedPrepare(UnsignedPrepare(10,0,0),0)),0)}, 10086, multiset{QbftMessageWithRecipient(Prepare(SignedPrepare(UnsignedPrepare(10,0,0),0)),0)}))
    }

    function tInvalidEnv2(i:nat): DSState
    {
        tBlockchain1(0).(environment := Network([10,9,8,7], multiset{}, 10086, multiset{}))
    }

    function tInvalidEnv3(i:nat): DSState
    {
        tBlockchain1(0).(environment := Network([1,3,4,2], multiset{}, 10086, multiset{}))
    }
    
    

    ///// other settings /////
    function tBlockchain4(i:nat): DSState
    // a different block which is adversary
    {
        var header := BlockHeader(1, 0, {}, 0, 0);
        var genesisBlock := Block(header, 0, []);
        var c := Configuration([0,1,2,3], genesisBlock, 0);
        var env := Network([0,1,2], multiset{}, 0, multiset{});

        var b1 := Block(BlockHeader(0,0,{0},0,0), 1, ["trans1s"]);
        var b2 := Block(BlockHeader(1,1,{0},1,3), 2, ["trans2s"]);
        var b3 := Block(BlockHeader(2,2,{0},2,5), 3, ["trans3s"]);
        
        var blockchain1 := [b1];
        var blockchain2 := [b1,b2];
        var blockchain3 := [b1,b2,b3];
        var blockchain4 := [genesisBlock];

        var n0 := NodeState(blockchain1, 0, 0, 0, c, {}, None, Optional(genesisBlock), None, 0);
        var n1 := NodeState(blockchain2, 0, 10, 5, c, {}, None, None, Optional(0), 0);
        var n2 := NodeState(blockchain3, 20, 0, 10, c, {}, None, None, None, 2);
        var n3 := NodeState(blockchain4, 0, 0, 15, c, {Prepare(SignedPrepare(UnsignedPrepare(10,0,0),0))}, None, None, None, 0);

        var nodes := map[0 := n0, 1 := n1, 2 := n2, 3:= n3];
        var adv := Adversary({}, {3});
        var ds := DSState(c, env, nodes, adv);
        ds
    }
    lemma testBlockChain4() {
        assert consistency(tBlockchain4);
    }

    function tBlockchain5(i:nat): DSState
    // all valid blockchain start with genesisBlock
    {
        var header := BlockHeader(1, 0, {}, 0, 0);
        var genesisBlock := Block(header, 0, []);
        var c := Configuration([0,1,2,3], genesisBlock, 0);
        var env := Network([0,1,2], multiset{}, 0, multiset{});

        var b1 := Block(BlockHeader(0,0,{0},0,0), 1, ["trans1s"]);
        var b2 := Block(BlockHeader(1,1,{0},1,3), 2, ["trans2s"]);
        var b3 := Block(BlockHeader(2,2,{0},2,5), 3, ["trans3s"]);
        
        var blockchain1 := [genesisBlock,b1];
        var blockchain2 := [genesisBlock,b1,b2];
        var blockchain3 := [genesisBlock,b1,b2,b3];
        var blockchain4 := [genesisBlock];

        var n0 := NodeState(blockchain1, 0, 0, 0, c, {}, None, None, None, 0);
        var n1 := NodeState(blockchain2, 0, 0, 0, c, {}, None, None, None, 0);
        var n2 := NodeState(blockchain3, 0, 0, 0, c, {}, None, None, None, 0);
        var n3 := NodeState(blockchain4, 0, 0, 0, c, {}, None, None, None, 0);

        var nodes := map[0 := n0, 1 := n1, 2 := n2, 3:= n3];
        var adv := Adversary({}, {3});
        var ds := DSState(c, env, nodes, adv);
        ds
    }
    lemma testBlockChain5() {
        assert consistency(tBlockchain5);
    }

    function tBlockchain6(i:nat): DSState
    // all valid blockchain start with genesisBlock
    {
        var header := BlockHeader(1, 0, {}, 0, 0);
        var genesisBlock := Block(header, 0, []);
        var c := Configuration([0,1,2,3], genesisBlock, 0);
        var env := Network([0,1,2], multiset{}, 0, multiset{});

        var b1 := Block(BlockHeader(0,0,{0},0,0), 1, ["trans1s"]);
        var b2 := Block(BlockHeader(1,1,{0},1,3), 2, ["trans2s"]);
        var b3 := Block(BlockHeader(2,2,{0},2,5), 3, ["trans3s"]);
        
        var blockchain1 := [genesisBlock,b1];
        var blockchain2 := [genesisBlock,b1,b2];
        var blockchain3 := [genesisBlock,b1,b2,b3];
        var blockchain4 := [genesisBlock];

        var n0 := NodeState(blockchain1, 0, 0, 0, c, {}, None, None, None, 0);
        var n1 := NodeState(blockchain2, 0, 0, 0, c, {}, None, None, None, 0);
        var n2 := NodeState(blockchain3, 0, 0, 0, c, {}, None, None, None, 0);
        var n3 := NodeState(blockchain4, 0, 0, 0, c, {}, None, None, None, 0);

        var nodes := map[0 := n0, 1 := n1, 2 := n2, 3:= n3];
        var adv := Adversary({}, {3});
        var ds := DSState(c, env, nodes, adv);
        ds
    }
    lemma testBlockChain6() {
        assert consistency(tBlockchain6);
    }

    
    
    function t1(i:nat): DSState
    {
        var h0 := BlockHeader(1, 0, {}, 0, 0);
        var c := Configuration([0,1,2], Block(h0, 0, []), 0);
        var env := Network([0,1,2], multiset{}, 0, multiset{});

        var n0 := NodeState([], 0, 0, 0, c, {}, None, None, None, 0);
        var nodes := map[0 := n0, 1 := n0.(id := 1), 2 := n0.(id := 2)];
        var adv := Adversary({}, {});
        var ds := DSState(c, env, nodes, adv);
        ds
    }
    lemma test1() {
        assert consistency(t1);
    }


    function t2(i:nat): DSState
    {
        var header := BlockHeader(1, 0, {}, 0, 0);
        var c := Configuration([1,2,3], Block(header, 0, []), 0);
        var env := Network([0,1,2], multiset{}, 0, multiset{});
        var adv := Adversary({}, {});

        var b1 := Block(header, 5, ["trans1"]);
        var b2 := Block(header, 6, ["trans2"]);

    
        var n0 := NodeState([b1, b2], 0, 0, 0, c, {}, None, None, None, 0);
        var nodes := map[0 := n0, 1 := n0.(blockchain := [b1]), 2 := n0];

        DSState(c, env, nodes, adv)
    }
    lemma test2() {
        assert consistency(t2);
    }


    function t3(i:nat): DSState
    {
        var header := BlockHeader(1, 0, {}, 0, 0);
        var c := Configuration([1], Block(header, 0, []), 0);
        var env := Network([0,1,2], multiset{}, 0, multiset{});
        var adv := Adversary({}, {});

        var b1 := Block(header, 5, ["trans1"]);
        var b2 := Block(header, 6, ["trans2"]);

    
        var n0 := NodeState([b1, b2], 0, 0, 0, c, {}, None, None, None, 0);
        var nodes := map[0 := n0, 1 := n0.(blockchain := [b1]), 2 := n0.(blockchain := [b2])];

        DSState(c, env, nodes, adv)
    }
    lemma test3() {
        var b1 := t3(0).nodes[1].blockchain;
        var b2 := t3(0).nodes[2].blockchain;

        var rbc1 := fromBlockchainToRawBlockchain(b1);
        var rbc2 := fromBlockchainToRawBlockchain(b2);

        assert !(rbc2[0] in rbc1);

        assert !consistentBlockchains(b1, b2);

        assert !consistency(t3);
    }

    ///// tests /////

    lemma testBlockChain1() {
        assert consistency(tBlockchain1);
    }

    lemma testEmpty() {
        assert consistency(tEmpty);
    }

    lemma testPartialEmpty() {
        assert consistency(tPartialEmpty1);
        assert consistency(tPartialEmpty2);
    }

    lemma testOnlyGenesis() {
        assert consistency(tOnlyGenesis1);
        assert consistency(tOnlyGenesis2);
    }

    lemma testNoGenesis() {
        assert consistency(tNoGenesis);
    }

    lemma testAllSame() {
        assert consistency(tAllSame1);
        assert consistency(tAllSame2);
    }

    lemma testLong() {
        assert consistency(tLong);
    }

    lemma testAverage() {
        assert consistency(tAverage);
    }

    lemma testAdv() {
        assert consistency(tAdv1);
        assert consistency(tAdv2);
        assert consistency(tAdv3);
        assert consistency(tAdv4);
        assert consistency(tAdv5);
    }

    lemma testInvalid1() {
        var b0 := tInvalid1(0).nodes[0].blockchain;
        var b1 := tInvalid1(0).nodes[1].blockchain;

        var rbc0 := fromBlockchainToRawBlockchain(b0);
        var rbc1 := fromBlockchainToRawBlockchain(b1);

        assert !(rbc1[1] in rbc0);

        assert !consistentBlockchains(b0, b1);
        assert !consistency(tInvalid1);
    }

    lemma testInvlalid2() {
        var b0 := tInvalid2(0).nodes[0].blockchain;
        var b1 := tInvalid2(0).nodes[2].blockchain;

        var rbc0 := fromBlockchainToRawBlockchain(b0);
        var rbc1 := fromBlockchainToRawBlockchain(b1);

        assert (rbc0[2] != rbc1[2]);

        assert !consistency(tInvalid2);
    }

    lemma testInvlalid3() {
        var b0 := tInvalid3(0).nodes[0].blockchain;
        var b1 := tInvalid3(0).nodes[3].blockchain;

        var rbc0 := fromBlockchainToRawBlockchain(b0);
        var rbc1 := fromBlockchainToRawBlockchain(b1);

        // there exists a contradiction -- an existence problem
        assert (rbc0[2] != rbc1[2]);
        assert !consistency(tInvalid3);
    }

    lemma testInvlalid4() {
        var b0 := tInvalid4(0).nodes[0].blockchain;
        var b1 := tInvalid4(0).nodes[2].blockchain;

        var rbc0 := fromBlockchainToRawBlockchain(b0);
        var rbc1 := fromBlockchainToRawBlockchain(b1);

        assert rbc0[2] != rbc1[2];

        assert !consistency(tInvalid4);
    }

    lemma testInvlalid5() {
        var b0 := tInvalid5(0).nodes[0].blockchain;
        var b1 := tInvalid5(0).nodes[1].blockchain;

        var rbc0 := fromBlockchainToRawBlockchain(b0);
        var rbc1 := fromBlockchainToRawBlockchain(b1);

        assert rbc0[0] != rbc1[0];

        assert !consistency(tInvalid5);
    }

    lemma testInvalidConfig1() {
        assert consistency(tInvalidConfig1);
        assert consistency(tInvalidConfig2);
        assert consistency(tInvalidEnv1);
        assert consistency(tInvalidEnv2);
        assert consistency(tInvalidEnv3);
    }
}
