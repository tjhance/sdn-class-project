include "../Types.i.dfy"
include "../Refinement.i.dfy"
include "../Service.i.dfy"
include "../DistributedSystem.i.dfy"
include "../RefinementLemmas.i.dfy"

module Refinement_Proof_InitNewMaster {
  import opened Types_i
  import opened Refinement_i
  import opened Service_i
  import opened DistributedSystem_i
  import opened RefinementLemmas_i

  predicate conditions(rs: RState, rs': RState, event: Event)
  {
    rstate_valid(rs)

    && LEnvironment_Next(rs.environment, rs'.environment)
    && rs.environment.nextStep.LEnvStepHostIos?
    && rs.endpoint_logger == rs'.endpoint_logger
    && rs.initControllerState == rs'.initControllerState
    && rs.environment.nextStep.actor in rs.switches
    && rs.environment.nextStep.actor in rs'.switches
    && Node_SwitchEvent(
                rs.switches[rs.environment.nextStep.actor],
                rs'.switches[rs.environment.nextStep.actor],
                event,
                rs.environment.nextStep.ios)
    && rs.controllers == rs'.controllers
    && rs.logger == rs'.logger
    && rs'.switches == rs.switches[
        rs.environment.nextStep.actor := rs'.switches[rs.environment.nextStep.actor]]
  }

  lemma lemma_refines_Logger_InitNewMaster(rs: RState, rs': RState, event: Event)
  requires conditions(rs, rs', event)

  ensures rstate_valid(rs')
  ensures Service_NextNewEvent(refinement(rs), refinement(rs'))
  {
    lemma_packets_are_valid(rs, rs', event);
    lemma_log_is_valid(rs, rs', event);
    lemma_accepted_commands_are_valid(rs, rs', event);
    lemma_switches_valid(rs, rs', event);

    lemma_outstanding_commands_eq(rs, rs');
    lemma_multiset_adds_one(rs, rs', event);
  }

  lemma {:axiom} lemma_packets_are_valid(rs: RState, rs': RState, event: Event)
  requires conditions(rs, rs', event)
  ensures packets_are_valid(rs')
  /*
  {
    packet_validation_preservation(rs, rs', event);
    lemma_packets_are_valid_no_sending(rs, rs');
  }
  */

  lemma {:axiom} packet_validation_preservation(rs: RState, rs': RState, event: Event)
  requires conditions(rs, rs', event)
  ensures packet_validation_preserved(rs, rs')
  /*
  {
    forall p : LPacket<EndPoint, RavanaMessage>
    ensures 
        is_valid_message(rs, p.src, p.dst, p.msg) ==>
        is_valid_message(rs', p.src, p.dst, p.msg)
    {
      if (is_valid_message(rs, p.src, p.dst, p.msg)) {
        match p.msg
          case EventMessage(event: Event, event_id: int) => {
            assert is_valid_EventMessage(rs', p.src, p.dst, p.msg);
          }
          case EventAck(event_ack_id: int) => {
            assert is_valid_EventAck(rs', p.src, p.dst, p.msg);
          }
          case CommandMessage(command: Command, command_id: int) => {
            assert is_valid_CommandMessage(rs', p.src, p.dst, p.msg);
          }
          case CommandAck(command_ack_id: int) => {
            assert is_valid_CommandAck(rs', p.src, p.dst, p.msg);
          }
          case InitNewMaster(leader_id: int) => {
            assert is_valid_InitNewMaster(rs', p.src, p.dst, p.msg);
          }
          case NewMaster(master_id: int) => {
            assert is_valid_NewMaster(rs', p.src, p.dst, p.msg);
          }
          case NewMasterAck => {
            assert is_valid_NewMasterAck(rs', p.src, p.dst, p.msg);
          }
          case LogMessage(log_entry: LogEntry) => {
            lemma_log_entry_valid(rs, rs', event, p.msg.log_entry);
            assert is_valid_LogMessage(rs', p.src, p.dst, p.msg);
          }
          case LogBroadcastMessage(full_log: seq<LogEntry>) => {
            assert is_valid_LogBroadcastMessage(rs', p.src, p.dst, p.msg);
          }
      }
    }
    reveal_packet_validation_preserved();
  }
  */

  lemma {:axiom} lemma_log_is_valid(rs: RState, rs': RState, event: Event)
  requires conditions(rs, rs', event)
  ensures log_is_valid(rs'.switches, rs'.logger.log)
  /*
  {
    reveal_log_is_valid();
    forall entry | entry in rs.logger.log
    ensures is_valid_log_entry(rs'.switches, entry)
    {
      lemma_log_entry_valid(rs, rs', event, entry);
    }
  }
  */

  lemma {:axiom} lemma_log_entry_valid(rs: RState, rs': RState, event: Event, entry: LogEntry)
  requires conditions(rs, rs', event)
  requires is_valid_log_entry(rs.switches, entry)
  ensures is_valid_log_entry(rs'.switches, entry)
  /*
  {
    if (entry.LMRecv?) {
      assert entry.switch in rs.switches;
      assert entry.switch in rs'.switches;

      assert entry.event_id in rs.switches[entry.switch].bufferedEvents;
      assert entry.event_id in rs'.switches[entry.switch].bufferedEvents;

      lemma_bufferedEvents_equal(rs, rs', event, entry.switch, entry.event_id);
    }
  }
  */

  lemma {:axiom} lemma_bufferedEvents_equal(rs: RState, rs': RState,
      event: Event, switch: EndPoint, event_id: int)
  requires conditions(rs, rs', event)
  requires switch in rs.switches
  requires event_id in rs.switches[switch].bufferedEvents
  ensures rs.switches[switch].bufferedEvents[event_id]
       == rs'.switches[switch].bufferedEvents[event_id];
  /*
  {
    if (switch == rs.environment.nextStep.actor) {
      lemma_event_ids_not_equal(rs, switch, event_id);
      assert event_id != rs.switches[switch].event_id;
      assert rs'.switches[switch].bufferedEvents[event_id]
          == (
              (rs.switches[switch].bufferedEvents[
                  rs.switches[switch].event_id := event])[event_id]
             )
          == rs.switches[switch].bufferedEvents[event_id];
    } else {
      assert rs.switches[switch].bufferedEvents[event_id]
          == rs'.switches[switch].bufferedEvents[event_id];
    }
  }
  */

  lemma {:axiom} lemma_event_ids_not_equal(rs: RState, switch: EndPoint, id: int)
  requires rstate_valid(rs)
  requires switch in rs.switches
  requires id in rs.switches[switch].bufferedEvents
  ensures id != rs.switches[switch].event_id
  /*
  {
    reveal_switches_valid();
  }
  */

  lemma {:axiom} lemma_accepted_commands_are_valid(rs: RState, rs': RState, event: Event)
  requires conditions(rs, rs', event)
  ensures accepted_commands_are_valid(rs'.initControllerState,
        rs'.switches, rs'.logger.log)
  /*
  {
    lemma_accepted_commands_are_valid_if_received_command_ids_unchanged(rs, rs');
  }
  */

  lemma {:axiom} lemma_multiset_adds_one(rs: RState, rs': RState, event: Event)
  requires conditions(rs, rs', event)
  requires rstate_valid(rs')
  ensures multiset_adds_one(refinement(rs).outstandingEvents,
                            refinement(rs').outstandingEvents)
  /*
  {
    lemma_outstandingEventsSet(rs, rs', event);
    lemma_outstandingEventsSet_not_contained(rs, rs', event);
    set_diff_impl_multiset_adds_one(
        refinement_outstandingEventsSet(rs.switches, rs.logger.log),
        refinement_outstandingEventsSet(rs'.switches, rs'.logger.log),
        (rs.environment.nextStep.actor,
               rs.switches[rs.environment.nextStep.actor].event_id),
        SwitchEvent(rs.environment.nextStep.actor, event));
  }
  */

  lemma {:axiom} lemma_outstandingEventsSet(rs: RState, rs': RState, event: Event)
  requires conditions(rs, rs', event)
  requires rstate_valid(rs')
  ensures refinement_outstandingEventsSet(rs'.switches, rs'.logger.log)
       == refinement_outstandingEventsSet(rs.switches, rs.logger.log)
          + {((rs.environment.nextStep.actor,
               rs.switches[rs.environment.nextStep.actor].event_id),
                SwitchEvent(rs.environment.nextStep.actor, event))}
  /*
  {
    lemma_new_event_id_not_in_log(rs, rs', event);
    assert
          (forall entry :: entry in rs.logger.log ==>
              !(entry.LMRecv? && entry.event_id == rs.switches[rs.environment.nextStep.actor].event_id && entry.switch == rs.environment.nextStep.actor));

    assert (
       forall switch :: forall eid :: 
          (switch == rs.environment.nextStep.actor && eid == 
                rs.switches[rs.environment.nextStep.actor].event_id) ==>

          switch in rs'.switches &&
          eid in rs'.switches[switch].bufferedEvents &&
          (forall entry :: entry in rs.logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))

    );

    lemma_every_switch_eid_matches(rs, rs', event);
    assert (
        forall switch :: forall eid ::
            (switch in rs.switches &&
            eid in rs.switches[switch].bufferedEvents) ==>
            (rs.switches[switch].bufferedEvents[eid] ==
            rs'.switches[switch].bufferedEvents[eid])
        );

    assert refinement_outstandingEventsSet(rs'.switches, rs'.logger.log)
      == (set
        switch : EndPoint, eid : int | (
          switch in rs'.switches &&
          eid in rs'.switches[switch].bufferedEvents &&
          (forall entry :: entry in rs'.logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs'.switches[switch].bufferedEvents[eid]))
         )
      == (set
        switch : EndPoint, eid : int | (
          switch in rs'.switches &&
          eid in rs'.switches[switch].bufferedEvents &&
          (forall entry :: entry in rs.logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs'.switches[switch].bufferedEvents[eid]))
         )
      == (set
        switch : EndPoint, eid : int | (
          switch in rs'.switches &&
          eid in rs'.switches[switch].bufferedEvents &&

          ((switch in rs.switches &&
          eid in rs.switches[switch].bufferedEvents)
          || (switch == rs.environment.nextStep.actor && eid == 
                rs.switches[rs.environment.nextStep.actor].event_id)
          ) &&
          (forall entry :: entry in rs.logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs'.switches[switch].bufferedEvents[eid]))
        )
      == (set
        switch : EndPoint, eid : int | (
          switch in rs'.switches &&
          eid in rs'.switches[switch].bufferedEvents &&

          (switch in rs.switches &&
          eid in rs.switches[switch].bufferedEvents)
           &&
          (forall entry :: entry in rs.logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs'.switches[switch].bufferedEvents[eid]))
        ) + (set
        switch : EndPoint, eid : int | (
          switch in rs'.switches &&
          eid in rs'.switches[switch].bufferedEvents &&

          (switch == rs.environment.nextStep.actor && eid == 
                rs.switches[rs.environment.nextStep.actor].event_id)
          &&
          (forall entry :: entry in rs.logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs'.switches[switch].bufferedEvents[eid]))
       )
      == (set
        switch : EndPoint, eid : int | (
          (switch in rs.switches &&
          eid in rs.switches[switch].bufferedEvents)
           &&
          (forall entry :: entry in rs.logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs'.switches[switch].bufferedEvents[eid]))
        ) + (set
        switch : EndPoint, eid : int | (
          switch in rs'.switches &&
          eid in rs'.switches[switch].bufferedEvents &&

          (switch == rs.environment.nextStep.actor && eid == 
                rs.switches[rs.environment.nextStep.actor].event_id)
          &&
          (forall entry :: entry in rs.logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs'.switches[switch].bufferedEvents[eid]))
       )
      == (set
        switch : EndPoint, eid : int | (
          (switch in rs.switches &&
          eid in rs.switches[switch].bufferedEvents)
           &&
          (forall entry :: entry in rs.logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.switches[switch].bufferedEvents[eid]))
        ) + (set
        switch : EndPoint, eid : int | (
          switch in rs'.switches &&
          eid in rs'.switches[switch].bufferedEvents &&

          (switch == rs.environment.nextStep.actor && eid == 
                rs.switches[rs.environment.nextStep.actor].event_id)
          &&
          (forall entry :: entry in rs.logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs'.switches[switch].bufferedEvents[eid]))
       )

      == refinement_outstandingEventsSet(rs.switches, rs.logger.log)
        + (set
        switch : EndPoint, eid : int | (
          switch in rs'.switches &&
          eid in rs'.switches[switch].bufferedEvents &&

          (switch == rs.environment.nextStep.actor && eid == 
                rs.switches[rs.environment.nextStep.actor].event_id)
          &&
          (forall entry :: entry in rs.logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs'.switches[switch].bufferedEvents[eid]))
       )
      == refinement_outstandingEventsSet(rs.switches, rs.logger.log)
          + {((rs.environment.nextStep.actor,
               rs.switches[rs.environment.nextStep.actor].event_id),
                SwitchEvent(rs.environment.nextStep.actor, event))};
  }
  */

  lemma {:axiom} lemma_new_event_id_not_in_log(rs: RState, rs': RState, event: Event)
  requires conditions(rs, rs', event)
  requires rstate_valid(rs')
  ensures (forall entry :: entry in rs.logger.log ==>
              !(entry.LMRecv? && entry.event_id == rs.switches[rs.environment.nextStep.actor].event_id && entry.switch == rs.environment.nextStep.actor))
  /*
  {
    forall entry | entry in rs.logger.log
    ensures !(entry.LMRecv? && entry.event_id == rs.switches[rs.environment.nextStep.actor].event_id && entry.switch == rs.environment.nextStep.actor)
    {
      if ((entry.LMRecv? &&
           entry.event_id == rs.switches[rs.environment.nextStep.actor].event_id &&
           entry.switch == rs.environment.nextStep.actor)) {
        reveal_log_is_valid();
        assert is_valid_log_entry(rs.switches, entry);
        assert entry.event_id in rs.switches[entry.switch].bufferedEvents;
        assert rs.switches[rs.environment.nextStep.actor].event_id in
               rs.switches[entry.switch].bufferedEvents;
        
        reveal_switches_valid();
        assert switch_valid(rs.switches[rs.environment.nextStep.actor]);

        assert rs.switches[rs.environment.nextStep.actor].event_id < 
                rs.switches[rs.environment.nextStep.actor].event_id;

        assert false;
      }
    }
  }
  */

  lemma {:axiom} lemma_every_switch_eid_matches(rs: RState, rs': RState, event: Event)
  requires conditions(rs, rs', event)
  requires rstate_valid(rs')
  ensures (
        forall switch :: forall eid ::
            (switch in rs.switches &&
            eid in rs.switches[switch].bufferedEvents) ==>
            (rs.switches[switch].bufferedEvents[eid] ==
            rs'.switches[switch].bufferedEvents[eid])
        )
  /*
  {
    forall switch | switch in rs.switches
    ensures (forall eid :: 
            eid in rs.switches[switch].bufferedEvents ==>
            (rs.switches[switch].bufferedEvents[eid] ==
            rs'.switches[switch].bufferedEvents[eid]))
    {
      forall eid | eid in rs.switches[switch].bufferedEvents
      ensures rs.switches[switch].bufferedEvents[eid] ==
              rs'.switches[switch].bufferedEvents[eid]
      {
        lemma_bufferedEvents_equal(rs, rs', event, switch, eid);
      }
    }
  }
  */

  lemma {:axiom} lemma_outstandingEventsSet_not_contained(rs: RState, rs': RState, event: Event)
  requires conditions(rs, rs', event)
  requires rstate_valid(rs')
  ensures !(
        ((rs.environment.nextStep.actor,
               rs.switches[rs.environment.nextStep.actor].event_id),
          SwitchEvent(rs.environment.nextStep.actor, event)
        )
       in refinement_outstandingEventsSet(rs.switches, rs.logger.log)
    )
  /*
  {
    if (((rs.environment.nextStep.actor,
               rs.switches[rs.environment.nextStep.actor].event_id),
          SwitchEvent(rs.environment.nextStep.actor, event)
        )
       in refinement_outstandingEventsSet(rs.switches, rs.logger.log))
    {
       assert rs.switches[rs.environment.nextStep.actor].event_id in rs.switches[rs.environment.nextStep.actor].bufferedEvents;
       lemma_event_ids_not_equal(rs, rs.environment.nextStep.actor, 
          rs.switches[rs.environment.nextStep.actor].event_id);
       assert false;
    }
  }
  */

  lemma lemma_switches_valid(rs: RState, rs': RState, event: Event)
  requires conditions(rs, rs', event)
  ensures switches_valid(rs'.switches)
  {
    reveal_switches_valid();
    forall ep | ep in rs'.switches
    ensures switch_valid(rs'.switches[ep])
    {
      assert ep in rs.switches;
      assert switch_valid(rs.switches[ep]);
    }
  }


}
