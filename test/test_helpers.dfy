include "../dafny/ver/L1/theorems.dfy"


module test_helpers {
import opened L1_SpecTypes
import opened L1_SpecNetwork
import opened L1_Adversary
import opened L1_DistributedSystem
import opened L1_Theorems
import opened L1_TheoremsDefs
import opened L1_AuxiliaryFunctionsAndLemmas

function genesisBlock(): Block
{
    var header := BlockHeader(1, 0, {}, 0, 0);
    Block(header, 0, [])
}

function config(): Configuration
{
    Configuration([0,1,2,3], genesisBlock(), 0)
}
function env(): Network
{
    // nodes, messagesSentYetToBeReceived, time, allMessagesSent
    Network([0,1,2,3], multiset{}, 0, multiset{})
}
function adv(): Adversary
{
    Adversary({}, {1})
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
function proposal(i:nat): QbftMessageWithRecipient
{
    QbftMessageWithRecipient(Proposal(proposalPayload(i), signedBlock(i), {}, {}), 0)
}
function currentWithNewMessagesReceived1(): NodeState
{
    NodeState([genesisBlock()], 0, 1, 0, config(), {}, None, None, None, 0)
}
function outProposal1(i:nat): set<QbftMessageWithRecipient>
{
    Multicast(
            [0,1,2,3],
            proposal(i).message
        )
}
function intermediateState1_1(): NodeState
{
    currentWithNewMessagesReceived1().(
        messagesReceived := {proposal(1).message}
    )
}
function intermediateState1_2(): NodeState
{
    intermediateState1_1().(
        messagesReceived := intermediateState1_1().messagesReceived + {proposal(2).message}
    )
}
function prepare1(): QbftMessage
{
    Prepare(
            signPrepare(
                UnsignedPrepare(
                    1,
                    0,
                    digest(signedBlock(1))),
                0
                )
        )
}
function outPrepare1(): set<QbftMessageWithRecipient>
{
    Multicast(
                [0,1,2,3],
                prepare1()
            )
}
function finalState1(): NodeState
{
    intermediateState1_2().(
        proposalAcceptedForCurrentRound := Optional(proposal(1).message),
        messagesReceived := intermediateState1_2().messagesReceived + {prepare1()}
    )
}
function env1(): Network
{
    Network(
        [0,1,2,3],
        multiset(outProposal1(1) + outProposal1(2) + outPrepare1()),
        0,
        multiset(outProposal1(1) + outProposal1(2) + outPrepare1())
    )
}
function s1(): DSState
{
    DSState(
        config(),
        env1(),
        s0().nodes[0 := finalState1()],
        adv()
    )
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
}