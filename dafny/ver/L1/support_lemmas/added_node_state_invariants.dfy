include "instr_node_state_invariants.dfy"
// include "networking_invariants.dfy"

module L1_AddedNodeStateInvariants
{
    import opened L1_SpecTypes
    import opened L1_SpecNetwork
    import opened L1_AuxiliaryFunctionsAndLemmas
    import opened L1_CommonFunctions
    import opened L1_Spec
    import opened HelperLemmasSets
    import opened L1_DistributedSystem
    import opened L1_InstrumentedSpecs
    import opened L1_Axioms
    import opened L1_AuxFunctionsProof
    import opened L1_AuxBasicInvariantsProof
    import opened L1_InstrNodeStateInvariants

    lemma lemmaNodeNextSubstepIfLastPreparedIsChangedThenUponPrepareStep(
       current:NodeState, 
        next:NodeState,
        outQbftMessages: set<QbftMessageWithRecipient>
    )
    requires validNodeState(current)
    requires NodeNextSubStep(current, next, outQbftMessages)
    requires current.lastPreparedBlock != next.lastPreparedBlock
    requires next.lastPreparedBlock.Optional?
    ensures UponPrepare(current, next, outQbftMessages)
    {
    }
    lemma lemmaNodeNextSubstepIfRoundChangeSentThenUponRoundStep(
       current:NodeState, 
        next:NodeState,
        outQbftMessages: set<QbftMessageWithRecipient>
    )
    requires validNodeState(current)
    requires NodeNextSubStep(current, next, outQbftMessages)
    requires exists m | m in fromMultisetQbftMessagesWithRecipientToSetOfMessages(multiset(outQbftMessages)) + next.messagesReceived - current.messagesReceived :: m.RoundChange?
    ensures UponRoundTimeout(current, next, outQbftMessages) || UponRoundChange(current, next, outQbftMessages)
    {
    }
    lemma lemmaIndInvLastPreparedBlockHasEmptyCommitSeals
    (
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>  
    )
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    requires indInvInstrNodeStateAllProposalsAcceptedAreValid(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)
    requires validInstrState(current) && current.nodeState.lastPreparedBlock.Optional? ==> current.nodeState.lastPreparedBlock.value.header.commitSeals == {}
    ensures indInvInstrNodeStateTypes(next)
    ensures validInstrState(next) && next.nodeState.lastPreparedBlock.Optional? ==>next.nodeState.lastPreparedBlock.value.header.commitSeals == {}
    {
        // assert validNodeState(current.nodeState);
        // assert NodeNextSingleStep(current.nodeState, inQbftMessages, next.nodeState, outQbftMessages);
        // var newMessagesReceived := current.nodeState.messagesReceived + inQbftMessages;
        // var newTime :|
        //     var currentWithNewMessagesReceived :=
        //         current.nodeState.(
        //             messagesReceived := newMessagesReceived,
        //             localTime := newTime
        //         );
        //     NodeNextSubStep(currentWithNewMessagesReceived, next.nodeState, outQbftMessages);
        // var currentWithNewMessagesReceived :=
        //         current.nodeState.(
        //             messagesReceived := newMessagesReceived,
        //             localTime := newTime
        //         );
        // if (currentWithNewMessagesReceived.lastPreparedBlock != next.nodeState.lastPreparedBlock) {
        //     if (next.nodeState.lastPreparedBlock.Optional?) {
        //         assert NodeNextSubStep(currentWithNewMessagesReceived, next.nodeState, outQbftMessages);
        //         lemmaNodeNextSubstepIfLastPreparedIsChangedThenUponPrepareStep(currentWithNewMessagesReceived, next.nodeState, outQbftMessages);
        //         assert next.nodeState.lastPreparedBlock == Optional(current.nodeState.proposalAcceptedForCurrentRound.value.proposedBlock);
        //     }
        // }
        
    }
    predicate invInstrNodeStateIfRoundChangeSentThenEmptyCommitSeals(
        s:InstrNodeState
    )
    {
        var messagesSent := fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.messagesSent) + s.messagesSentToItself;
        forall m |
                    && m in messagesSent
                    && m.RoundChange?
                ::
                m.proposedBlockForNextRound.Optional? ==> m.proposedBlockForNextRound.value.header.commitSeals == {}
    }
    lemma lemmaIndInvIfRoundChangeSentThenEmptyCommitSeals(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>  
    )
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    requires invInstrNodeStateIfRoundChangeSentThenEmptyCommitSeals(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)
    requires validInstrState(current) && current.nodeState.lastPreparedBlock.Optional? ==> current.nodeState.lastPreparedBlock.value.header.commitSeals == {}
    ensures indInvInstrNodeStateTypes(next)
    ensures invInstrNodeStateIfRoundChangeSentThenEmptyCommitSeals(next)
    {
    }
    
    predicate invInstrNodeStateIfProposalSentThenEmptyCommitSeals(
        s:InstrNodeState
    )
    {
        var messagesSent := fromMultisetQbftMessagesWithRecipientToSetOfMessages(s.messagesSent) + s.messagesSentToItself;
        forall m |
                    && m in messagesSent
                    && m.Proposal?
                ::
                m.proposedBlock.header.commitSeals == {}
    }
    lemma lemmaIndInvIfProposalSentThenEmptyCommitSeals(
        current:InstrNodeState, 
        inQbftMessages: set<QbftMessage>, 
        next:InstrNodeState,
        outQbftMessages: set<QbftMessageWithRecipient>  
    )
    requires validInstrState(current)
    requires indInvInstrNodeStateTypes(current)
    requires invInstrNodeStateIfProposalSentThenEmptyCommitSeals(current)
    requires InstrNodeNextSingleStep(current, inQbftMessages, next, outQbftMessages)
    ensures indInvInstrNodeStateTypes(next)
    ensures invInstrNodeStateIfProposalSentThenEmptyCommitSeals(next)
    {
    }
    predicate invProposalSentByHonestNodeHasEmptyCommitSeals(s:InstrDSState)
    {
        forall n | isInstrNodeHonest(s, n)
            :: invInstrNodeStateIfProposalSentThenEmptyCommitSeals(s.nodes[n])
    }
    predicate invRoundChangeSentByHonestNodeHasEmptyCommitSeals(s:InstrDSState)
    {
        forall n | isInstrNodeHonest(s, n)
            :: invInstrNodeStateIfRoundChangeSentThenEmptyCommitSeals(s.nodes[n])
    }
    predicate invLastPreparedBlockHasEmptyCommitSeals(s:InstrDSState)
    {
        forall n | isInstrNodeHonest(s, n)
            :: s.nodes[n].nodeState.lastPreparedBlock.Optional? ==>s.nodes[n].nodeState.lastPreparedBlock.value.header.commitSeals == {}
    }
    predicate invProposalEmpty(s:InstrDSState)
    {
        forall n | isInstrNodeHonest(s, n)
            ::  var opt := s.nodes[n].nodeState.proposalAcceptedForCurrentRound;
            opt.Optional? ==> opt.value.Proposal? && opt.value.proposedBlock.header.commitSeals == {}
    }



}