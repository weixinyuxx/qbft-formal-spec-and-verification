include "../dafny/ver/L1/distr_system_spec/distributed_system.dfy"
include "test_helpers.dfy"

include "../dafny/ver/L1/distr_system_spec/adversary.dfy"

module test_change_adv {
    import opened L1_SpecTypes
    import opened L1_SpecNetwork
    import opened L1_AuxiliaryFunctionsAndLemmas
    import opened L1_Spec
    import opened L1_Adversary
    import opened L1_CommonFunctions
    import opened L1_DistributedSystem
    import opened test_helpers


    predicate DSNextNode'(
        s : DSState,
        s': DSState,
        messagesSentByTheNodes: set<QbftMessageWithRecipient>,
        messagesReceivedByTheNodes: multiset<QbftMessageWithRecipient>,
        node: Address
    )
    // this is the modified DSNextNode predicate which allows adversary nodes' state to change arbitrarily
    // except that the messagesReceived should not change (actually should not change in a way that decipher the cryptographic signatures)

    // however, to the extent of observability of the adversary states, this should be considered together with messages they can send
    // One can also argue that the state of adversary is frozen from correct nodes' perspective and thus never change.
    requires validDSState(s)
    {
        && NetworkNext(s.environment,s'.environment,messagesSentByTheNodes,messagesReceivedByTheNodes)
        && (forall mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.recipient == node)
        && var messageReceived := set mr:QbftMessageWithRecipient | mr in messagesReceivedByTheNodes :: mr.message;
        && node in s.nodes
        && s'.nodes.Keys == s.nodes.Keys
        && (
            if isHonest(s,node) then
                && s'.nodes == s.nodes[node := s'.nodes[node]]
                && s'.adversary == s.adversary
                && NodeNext(s.nodes[node],messageReceived,s'.nodes[node],messagesSentByTheNodes)
            else
                && (forall a:Address | isHonest(s, a) :: s.nodes[a] == s'.nodes[a])
                && (forall a:Address | a in s.nodes.Keys :: s.nodes[a].messagesReceived == s'.nodes[a].messagesReceived)
                && AdversaryNext(s.configuration,s.adversary,messageReceived,s'.adversary,messagesSentByTheNodes)
        )
        && s'.configuration == s.configuration
    }

    lemma test_spec()
    {
        var s := StateGeneratorNoAdversary([genesisBlock()], [genesisBlock()], [genesisBlock()], [genesisBlock()]).(adversary := Adversary({}, {0}));
        var s' := s.(nodes := s.nodes[0 := NodeState([genesisBlock()], 0, 1, 0, c(), {}, None, None, None, 0)]); // time of the adv advances by 1

        assume |validators([genesisBlock()])| > 0;

        assert !DSNextNode(s, s', {}, multiset{}, 0);

        assert DSNextNode'(s, s', {}, multiset{}, 0);
    }
    
}

// is the protocol correct in this sense


module test_send_adv {
    import opened L1_SpecTypes
    import opened L1_SpecNetwork
    import opened L1_AuxiliaryFunctionsAndLemmas
    import opened L1_CommonFunctions
    import opened L1_Adversary
    import opened test_helpers


    ///// Prepare /////
    lemma test_prepare() 
    {
        var a := Adversary({}, {0});
        var inQbftMessages:set<QbftMessage> := {};

        // make up a random prepare message with incorrect signature
        var message := QbftMessageWithRecipient(Prepare(SignedPrepare(UnsignedPrepare(0,0,0),0)),1);
        var outQbftMessages := {message}; 
        assume !(recoverSignature(message.message) in {0,1,2,3});

        // the original spec is not allowing this kind of behavior
        assert !AdversaryNext(a, inQbftMessages, a, outQbftMessages);

        // the modified spec is allowing the this behavior now
        var c := Configuration([0,1,2,3], genesisBlock(), 0);
        assert AdversaryNext'(c, a, inQbftMessages, a, outQbftMessages);
    }

    ///// Commit /////
    lemma test_commit()
    {
        var a := Adversary({}, {0});
        var inQbftMessages:set<QbftMessage> := {};

        // make up a random commit message with incorrect signature and commit seal
        var message := QbftMessageWithRecipient(Commit(SignedCommit(UnsignedCommit(0,0,0,0),0)),1);
        var outQbftMessages := {message};
        assume !(recoverSignature(message.message) in {0,1,2,3});
        var cs := message.message.commitPayload.unsignedPayload.commitSeal;
        assume (forall b :: !(recoverSignedHashAuthor(hashBlockForCommitSeal(b), cs) in {0,1,2,3}));

        assert !AdversaryNext(a, inQbftMessages, a, outQbftMessages);

        var c := Configuration([0,1,2,3], genesisBlock(), 0);
        assert AdversaryNext'(c, a, inQbftMessages, a, outQbftMessages);
    }

    ///// New Block /////
    lemma test_newBLock()
    {
        var a := Adversary({}, {0});
        var inQbftMessages:set<QbftMessage> := {};

        // make up a random new block with incorrect commit seals
        var block := Block(BlockHeader(0,0,{0},0,0), "body", ["transaction"]);
        var message := QbftMessageWithRecipient(NewBlock(block),1);
        var outQbftMessages := {message};

        assume !(recoverSignedHashAuthor(hashBlockForCommitSeal(block),0) in {0,1,2,3});

        assert !AdversaryNext(a, inQbftMessages, a, outQbftMessages);

        var c := Configuration([0,1,2,3], genesisBlock(), 0);
        assert AdversaryNext'(c, a, inQbftMessages, a, outQbftMessages);
    }

    ///// Round Change /////
    lemma test_roundChange()
    {
        var a := Adversary({}, {0});
        var roundChange := signRoundChange(UnsignedRoundChange(0,0,None,None),0);

        var inQbftMessages:set<QbftMessage> := {RoundChange(roundChange, None, {})};

        // make up a round change message with correct commit seals by a functioning node for a block
        var block := Block(BlockHeader(0,0,{},0,0), "body", ["transaction"]);
        var commitedBlock := block.(header := block.header.(commitSeals := {signHash(hashBlockForCommitSeal(block), 1)}));

        var message := QbftMessageWithRecipient(RoundChange(roundChange, Optional(commitedBlock), {}), 1);
        var outQbftMessages := {message};

        // commit seal is signed by a functioning node

        // the original spec allows adversary to send a round change message with a block commit sealed by a functioning node
        assert AdversaryNext(a, inQbftMessages, a.(messagesReceived := a.messagesReceived + inQbftMessages), outQbftMessages);

        // the modified spec doew not allow this behavior
        var c := Configuration([0,1,2,3], genesisBlock(), 0);
        assert !AdversaryNext'(c, a, inQbftMessages, a, outQbftMessages);
    }

    predicate AdvPrepare(preparePayload: SignedPrepare, c: Configuration, messagesReceived: set<QbftMessage>, a: Adversary) {
        || preparePayload in signedPreparePayloads(messagesReceived)
        || !(recoverSignedPrepareAuthor(preparePayload) in seqToSet(c.nodes) - a.byz)
    }

    predicate AdvBlock(b: Block, c: Configuration, messagesReceived: set<QbftMessage>, a: Adversary) {
        forall cs | cs in b.header.commitSeals ::
            || (cs in getCommitSeals(messagesReceived))
            || !(recoverSignedHashAuthor(hashBlockForCommitSeal(b),cs) in seqToSet(c.nodes) - a.byz)
    }

    predicate AdvRoundChange(m: SignedRoundChange, c: Configuration, messagesReceived: set<QbftMessage>, a: Adversary) {
        || m in signedRoundChangePayloads(messagesReceived)
        || !(recoverSignedRoundChangeAuthor(m) in seqToSet(c.nodes) - a.byz) 
    }


    predicate AdversaryNext'(
        c: Configuration,
        a: Adversary, 
        inQbftMessages: set<QbftMessage>, 
        a': Adversary,
        outQbftMessages: set<QbftMessageWithRecipient>
        )
    {
        var messagesReceived := a.messagesReceived + inQbftMessages;

        && a' == a.(messagesReceived := messagesReceived)
        && (forall m | m in outQbftMessages ::
                        || m.message in messagesReceived
                        || (
                            && m.message.Proposal?
                            && (
                                || m.message.proposalPayload in signedProposalPayloads(messagesReceived)
                                // actually it should be forall blocks
                                || !(recoverSignedProposalAuthor(m.message.proposalPayload) in seqToSet(c.nodes) - a.byz)
                            )
                            && AdvBlock(m.message.proposedBlock, c, messagesReceived, a)
                            && (forall m' | m' in m.message.proposalJustification ::
                                AdvRoundChange(m', c, messagesReceived, a)
                            )
                            && (forall m' | m' in m.message.roundChangeJustification ::
                                AdvPrepare(m', c, messagesReceived, a)
                            )
                        )
                        || (
                            && m.message.RoundChange?
                            && AdvRoundChange(m.message.roundChangePayload, c, messagesReceived, a)
                            && (
                                || m.message.proposedBlockForNextRound.None?
                                || AdvBlock(m.message.proposedBlockForNextRound.value, c, messagesReceived, a)
                            )               
                            && (forall m' | m' in m.message.roundChangeJustification ::
                                    AdvPrepare(m', c, messagesReceived, a)
                            )
                        ) 
                        || (
                            && m.message.Prepare?
                            && AdvPrepare(m.message.preparePayload, c, messagesReceived, a)
                        )
                        || (
                            && m.message.Commit?
                            && !(recoverSignature(m.message) in seqToSet(c.nodes) - a.byz)
                            &&  var uPayload := m.message.commitPayload.unsignedPayload;
                                var cs := uPayload.commitSeal;
                            && (
                                || (cs in getCommitSeals(messagesReceived))
                                || (forall b :: !(recoverSignedHashAuthor(hashBlockForCommitSeal(b), cs) in seqToSet(c.nodes) - a.byz))
                                // not sure whether this is implementable (by public key cryptography)
                            )
                        )                                        
                        || (
                            && m.message.NewBlock?
                            && AdvBlock(m.message.block, c, messagesReceived, a)
                        )
        )
    }    
}