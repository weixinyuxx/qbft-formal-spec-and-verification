include "../ver/L1/distr_system_spec/adversary.dfy"
include "../ver/L1/distr_system_spec/distributed_system.dfy"
include "../ver/L1/theorems.dfy"
include "../spec/L1/types.dfy"

// this counterexample verifies with the original spec, without any modification
// this reveals that the adversary is specified weaker than expected
module test_getCommitSeals
{
    import opened L1_Adversary
    import opened L1_SpecTypes
    import opened L1_SpecNetwork
    import opened L1_AuxiliaryFunctionsAndLemmas
    import opened L1_CommonFunctions
    import opened L1_DistributedSystem
    import opened L1_Theorems
    import opened L1_TheoremsDefs
    import opened L1_Spec

    function getSignedBlock():Block {
        var block1 := Block(BlockHeader(0, 0, {}, 1, 0), 1, []); // a random block with empty commit seals
        var commitSeals1 := {signHash(hashBlockForCommitSeal(block1), 1)}; // constructing valid commit seals from a quorum of honest nodes
        block1.(header := block1.header.(commitSeals := commitSeals1))
    }

    function addCommitSeal():Block {
        var block1 := Block(BlockHeader(0, 0, {}, 1, 0), 1, []);
        var commitSeals2 := {signHash(hashBlockForCommitSeal(block1), 1), signHash(hashBlockForCommitSeal(block1), 2)};
        block1.(header := block1.header.(commitSeals := commitSeals2))
    }

    function getProposalWithCommitSeal(): QbftMessage {
        var signedBlock1 := getSignedBlock();
        var proposalPayload := signProposal(UnsignedProposal(0,0,0),0); // constructing a random proposal payload signed by itself

        Proposal(proposalPayload, signedBlock1, {}, {})
    }

    function getNewBlockMessageFromProposal(): QbftMessageWithRecipient {
        QbftMessageWithRecipient(NewBlock(getSignedBlock()), 1)
    }

    
    // an adversary tries to extract a commitSeal from a proposal it received
    // and send this commitSeal in a new block message
    // this behavior should be allowed, but AdversaryNext() thinks this is an invalid behavior
    lemma getCommitSealsCounterexample(
        a:Adversary, 
        inQbftMessages: set<QbftMessage>, 
        a': Adversary,
        outQbftMessages: set<QbftMessageWithRecipient>
        )
        requires a.byz == {0}
        requires inQbftMessages == {getProposalWithCommitSeal()}
        requires outQbftMessages == {getNewBlockMessageFromProposal()}
        requires a.messagesReceived == {}
        requires a' == a.(messagesReceived := a.messagesReceived + inQbftMessages)
        ensures !AdversaryNext(a, inQbftMessages, a', outQbftMessages)
    {
        var m :| m in outQbftMessages;
        assert m == getNewBlockMessageFromProposal();
        var block1 := Block(BlockHeader(0, 0, {}, 1, 0), 1, []);
        var cs := signHash(hashBlockForCommitSeal(block1), 1);
        assert cs in m.message.block.header.commitSeals;

        var min :| min in inQbftMessages;
        assert a'.messagesReceived == {min};
        assert cs !in getCommitSeals(a'.messagesReceived);
        lemmaSignedHash();
        assert recoverSignedHashAuthor(hashBlockForCommitSeal(m.message.block),cs) != 0;
    }


    // adversary id 0 with empty message log receives a proposal with a commit seal signed by node 1
    // it then sends the same proposal, except that it adds a commit seal correctly signed by node 2
    // this behavior should never happen, because adversary should not be able to forge commit seals signed by node 2
    // but AdversaryNext() thinks that this is a valid behavior
    // an adversary should never be able to forge commit seals
    lemma sendCommitSealsCounterexample(
        a:Adversary, 
        inQbftMessages: set<QbftMessage>, 
        a': Adversary,
        outQbftMessages: set<QbftMessageWithRecipient>
        )
        requires a.byz == {0}
        requires a.messagesReceived == {}
        requires a' == a.(messagesReceived := a.messagesReceived + inQbftMessages)
        requires inQbftMessages == {getProposalWithCommitSeal()}
        requires outQbftMessages == {QbftMessageWithRecipient(getProposalWithCommitSeal().(proposedBlock := addCommitSeal()),1)}
        ensures AdversaryNext(a, inQbftMessages, a', outQbftMessages)
    {
    }

    // a block with non-empty commit seals can still be valid output of getNewBlock() function
    // because it satisfies the postcondition
    // this is not a desired behavior
    lemma getNewBlockCounterexample(
        nodeState:NodeState,
        round:nat,
        block:Block
    )
        requires |nodeState.blockchain| == 1
        requires block.header.height == 1
        requires block.header.roundNumber == round == 1
        requires |validators(nodeState.blockchain + [block])| > 0
        requires block.header.commitSeals != {}
        ensures block.header.roundNumber == round
            && |validators(nodeState.blockchain + [block])| > 0
            && block.header.height == |nodeState.blockchain|
    {}

}
