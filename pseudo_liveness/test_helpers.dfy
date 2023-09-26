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
function config(): Configuration
{
    Configuration([0,1,2,3], genesisBlock(), 1)
}
function env(): Network
{
    // nodes, messagesSentYetToBeReceived, time, allMessagesSent
    Network([0,1,2,3], multiset{}, 0, multiset{})
}
function adv(): Adversary
{
    Adversary({}, {0})
}
function s0(): DSState
{
    DSState(config(), env(), map[
                // blockchain, round, localTime, id, configuration, messagesReceived, proposalAcceptedForCurrentRound, lastPreparedBlock, lastPreparedRound, timeLastRoundStart
                0 := NodeState([genesisBlock()], 0, 0, 0, config(), {}, None, None, None, 0),
                1 := NodeState([genesisBlock()], 0, 0, 1, config(), {}, None, None, None, 0),
                2 := NodeState([genesisBlock()], 0, 0, 2, config(), {}, None, None, None, 0),
                3 := NodeState([genesisBlock()], 0, 0, 3, config(), {}, None, None, None, 0)
            ], adv())
}
function signedBlock(i:nat): Block
{
    // proposer, roundNumber, commitSeals, height, timestamp
    var block1 := Block(BlockHeader(0, 0, {}, 1, 0), i, []); // a random block with empty commit seals
    var commitSeals1 := {signHash(hashBlockForCommitSeal(block1), 1), signHash(hashBlockForCommitSeal(block1), 2), signHash(hashBlockForCommitSeal(block1), 3)}; // constructing valid commit seals from a quorum of honest nodes
    block1.(header := block1.header.(commitSeals := commitSeals1)) // put the commit seals into the block
}
function proposalPayload(i:nat): SignedProposal
{
    signProposal(UnsignedProposal(0,0,digest(signedBlock(i))),0)
}
function proposal(content:nat): QbftMessageWithRecipient
{
    QbftMessageWithRecipient(Proposal(proposalPayload(content), signedBlock(content), {}, {}), 0)
}
function proposalPayloadFor1(): SignedProposal
{
    var block := Block(BlockHeader(0, 0, {}, 1, 0), 0, []);
    signProposal(UnsignedProposal(1, 0, digest(block)), 0)
}
function proposalFor1(dest:nat): QbftMessageWithRecipient
{
    QbftMessageWithRecipient(Proposal(proposalPayloadFor1(), Block(BlockHeader(0, 0, {}, 1, 0), 0, []), {}, {}), dest)
}
function s1(): DSState
{
    var env1 := Network([0,1,2,3], multiset{proposal(1), proposal(2)}, 0, multiset{proposal(1), proposal(2)});
    s0().(environment := env1)
}
function adv2(): Adversary
{
    Adversary({proposal(1).message, proposal(2).message}, {0})
}
function newBlock(i: nat): QbftMessageWithRecipient
{
    QbftMessageWithRecipient(NewBlock(signedBlock(i)), i)
}
function env2(): Network
{
    Network([0,1,2,3], multiset{newBlock(1), newBlock(2)}, 0, s1().environment.allMessagesSent + multiset{newBlock(1), newBlock(2)})
}
function s2(): DSState
{
    s1().(environment := env2(), adversary := adv2())
}

function newMessagesReceived3(): set<QbftMessage>
{
    {newBlock(1).message}
}
function currentWithNewMessagesReceived3(): NodeState
{
    var current := s2().nodes[1];
    current.(
                messagesReceived := newMessagesReceived3(),
                localTime := current.localTime + 1
            )
}
function intermediateState3_1(): NodeState
{
    currentWithNewMessagesReceived3().(
        blockchain := [genesisBlock(), signedBlock(1)],
        timeLastRoundStart := 1
    )
}
function proposal3(): QbftMessage
{
    var block := getNewBlock(intermediateState3_1(), 0);
    Proposal(
        signProposal(
            UnsignedProposal(
                2,
                0,
                digest(block)),
            1),
        block,
        {},
        {})
}
function outProposal3(): set<QbftMessageWithRecipient>
{
    Multicast(
        [0,1,2,3],
        proposal3()
    )
}
function intermediateState3_2(): NodeState
{
    intermediateState3_1().(
        messagesReceived := intermediateState3_1().messagesReceived + {proposal3()}
    )
}
function prepare3(): QbftMessage
{
    Prepare(
            signPrepare(
                UnsignedPrepare(
                    2,
                    0,
                    digest(getNewBlock(intermediateState3_1(), 0))),
                1
                )
        )
}
function finalState3(): NodeState
{
    intermediateState3_2().(
        proposalAcceptedForCurrentRound := Optional(proposal3()),
        messagesReceived := intermediateState3_2().messagesReceived + {prepare3()}
    )
}
function outPrepare3(): set<QbftMessageWithRecipient>
{
    Multicast(
        [0,1,2,3],
        prepare3()
    )
}
function env3(): Network
{
    Network([0,1,2,3], 
        multiset{newBlock(2)} + multiset(outPrepare3()) + multiset(outProposal3()), 
        0, 
        env2().allMessagesSent + multiset(outPrepare3()) + multiset(outProposal3()))
}
function s3(): DSState
{
    s2().(
        environment := env3(),
        nodes := s2().nodes[1 := finalState3()]
    )
}
function newMessagesReceived4(): set<QbftMessage>
{
    {newBlock(2).message, proposal3()}
}
function currentWithNewMessagesReceived4(): NodeState
{
    var current := s3().nodes[2];
    current.(
                messagesReceived := newMessagesReceived4(),
                localTime := current.localTime + 1
            )
}
function intermediateState4(): NodeState
{
    currentWithNewMessagesReceived4().(
        blockchain := [genesisBlock(), signedBlock(2)],
        timeLastRoundStart := 1
    )
}
function prepare4(): QbftMessage
{
    Prepare(
        signPrepare(
            UnsignedPrepare(
                2,
                0,
                digest(getNewBlock(intermediateState3_1(), 0))),
            2
            )
        )
}
function finalState4(): NodeState
{
    intermediateState4().(
        proposalAcceptedForCurrentRound := Optional(proposal3()),
        messagesReceived := intermediateState4().messagesReceived + {prepare4()}
    )
}
function outPrepare4(): set<QbftMessageWithRecipient>
{
    Multicast(
        [0,1,2,3],
        prepare4()
    )
}

function env4(): Network
{
    Network([0,1,2,3], 
        env3().messagesSentYetToBeReceived - multiset{newBlock(2), QbftMessageWithRecipient(proposal3(), 2)} + multiset(outPrepare4()),
        // multiset(outPrepare3()) + multiset{QbftMessageWithRecipient(proposal3(), 0), QbftMessageWithRecipient(proposal3(), 1), QbftMessageWithRecipient(proposal3(), 3)} + multiset(outPrepare4()), 
        0,
        env3().allMessagesSent + multiset(outPrepare4()))
}
function s4(): DSState
{
    s3().(
        environment := env4(),
        nodes := s3().nodes[2 := finalState4()]
    )
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
lemma test()
        requires forall blockchain ::validators(blockchain) == [0,1,2,3]
    {
        var behavior := [s0(), s1(), s2(), s3(), s4()];
        assert |behavior| == 5;
        assert forall i | 0 <= i < |behavior| :: validDSState(behavior[i]);

        assert forall i | 0 <= i < 4 :: DSNext(behavior[i],behavior[i+1]) by {
            
            assume DSNext(behavior[0], behavior[1]);
            assume DSNext(behavior[1], behavior[2]);
            assume DSNext(behavior[2], behavior[3]);
            assume DSNext(behavior[3], behavior[4]);
        }

    }

}

