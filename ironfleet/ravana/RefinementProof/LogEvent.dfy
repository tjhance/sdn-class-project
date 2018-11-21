include "../Types.i.dfy"
include "../Refinement.i.dfy"
include "../Service.i.dfy"
include "../DistributedSystem.i.dfy"
include "../RefinementLemmas.i.dfy"

module Refinement_Proof_LogEvent_i {
  import opened Types_i
  import opened Refinement_i
  import opened Service_i
  import opened DistributedSystem_i
  import opened RefinementLemmas_i

  lemma lemma_refines_LoggerLogEvent(rs: RState, rs': RState)
  requires rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor == rs'.endpoint_logger
  requires Node_LoggerLogEvent(
              rs.server_logger, rs'.server_logger, rs.environment.nextStep.ios)
  requires rs.server_controllers == rs'.server_controllers
  requires rs.server_switches == rs'.server_switches

  ensures rstate_valid(rs')
  ensures Service_NextApplyEvent(refinement(rs), refinement(rs'))
       || refinement(rs) == refinement(rs')
          
  {
    packet_validation_preservation(rs, rs');
    lemma_packets_are_valid_no_sending(rs, rs');

    lemma_accepted_commands_are_valid(rs, rs');
    lemma_log_is_valid(rs, rs');

    var s := refinement(rs);
    var s' := refinement(rs');

    assert rs.environment.nextStep.ios[0].LIoOpReceive?;
    assert rs.environment.nextStep.ios[0].r.msg.LogMessage?;
    lemma_received_packet_is_valid(rs, rs.environment.nextStep.ios[0].r);
    var log_entry := rs.environment.nextStep.ios[0].r.msg.log_entry;

    if (log_entry.LMRecv?) {
      var switch_event := SwitchEvent(log_entry.switch, log_entry.event);

      assert s.switchStates == s'.switchStates;

      lemma_refines_LoggerLogEvent_multiset(rs, rs', log_entry);

      assert multiset_adds_one(s'.outstandingEvents, s.outstandingEvents);
      var event := added_obj(s'.outstandingEvents, s.outstandingEvents);
      assert event == switch_event;

      var cas := controllerTransition(s.controllerState, switch_event.switch,
          switch_event.event);
      var cs' := cas.0;
      var singleCommands := cas.1;

      assert s'.controllerState == cs';

      lemma_outstandingCommands(rs, rs', singleCommands, log_entry, switch_event);
      assert s'.outstandingCommands == s.outstandingCommands + seq_to_multiset(singleCommands);

      assert Service_NextApplyEvent(refinement(rs), refinement(rs'));
    } else {
      assert refinement_switchStates(rs.server_switches)
          == refinement_switchStates(rs'.server_switches);

      assert refinement_controllerState(rs.server_logger.log, rs.initControllerState)
          == refinement_controllerState(rs'.server_logger.log, rs'.initControllerState);

      assert refinement_outstandingCommands(rs.server_logger.log, rs.initControllerState, rs.server_switches)
          == refinement_outstandingCommands(rs'.server_logger.log, rs'.initControllerState, rs'.server_switches);

      lemma_lmproc_outstandingEventsSet_matches(rs, rs', log_entry);

      assert refinement_outstandingEvents(rs.server_switches, rs.server_logger.log)
          == refinement_outstandingEvents(rs'.server_switches, rs'.server_logger.log);

      assert s == s';
    }
  }

  lemma
  lemma_log_is_valid(rs: RState, rs': RState)
  requires rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor == rs'.endpoint_logger
  requires Node_LoggerLogEvent(
              rs.server_logger, rs'.server_logger, rs.environment.nextStep.ios)
  requires rs.server_controllers == rs'.server_controllers
  requires rs.server_switches == rs'.server_switches
  ensures log_is_valid(rs'.server_switches, rs'.server_logger.log)
  {
    reveal_log_is_valid();

    assert rs.environment.nextStep.ios[0].LIoOpReceive?;
    assert rs.environment.nextStep.ios[0].r.msg.LogMessage?;
    lemma_received_packet_is_valid(rs, rs.environment.nextStep.ios[0].r);
    var log_entry := rs.environment.nextStep.ios[0].r.msg.log_entry;
    assert rs.server_logger.log + [log_entry] == rs'.server_logger.log;

    assert is_valid_log_entry(rs.server_switches, log_entry);
    assert forall entry :: entry in rs.server_logger.log ==>
        is_valid_log_entry(rs.server_switches, entry);
    assert forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
        is_valid_log_entry(rs.server_switches, entry);
    assert forall entry :: entry in rs'.server_logger.log ==>
        is_valid_log_entry(rs.server_switches, entry);
    assert forall entry :: entry in rs'.server_logger.log ==>
        is_valid_log_entry(rs'.server_switches, entry);
  }

  lemma {:axiom}
  lemma_accepted_commands_are_valid(rs: RState, rs': RState)
  requires rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor == rs'.endpoint_logger
  requires Node_LoggerLogEvent(
              rs.server_logger, rs'.server_logger, rs.environment.nextStep.ios)
  requires rs.server_controllers == rs'.server_controllers
  requires rs.server_switches == rs'.server_switches
  ensures accepted_commands_are_valid(rs'.initControllerState,
        rs'.server_switches, rs'.server_logger.log)
  /*
  {
    reveal_accepted_commands_are_valid();

    var all_commands := controller_state_looking_forward(
                rs.server_logger.log, rs.initControllerState).commands;
    var all_commands' := controller_state_looking_forward(
                rs'.server_logger.log, rs'.initControllerState).commands;

    all_commands_grows(rs, rs', all_commands, all_commands');
  }
  */

  lemma {:axiom}
  all_commands_grows(rs: RState, rs': RState, commands: seq<SingleCommand>,
          commands': seq<SingleCommand>)
  requires rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor == rs'.endpoint_logger
  requires Node_LoggerLogEvent(
              rs.server_logger, rs'.server_logger, rs.environment.nextStep.ios)
  requires rs.server_controllers == rs'.server_controllers
  requires rs.server_switches == rs'.server_switches

  requires commands == controller_state_looking_forward(
                rs.server_logger.log, rs.initControllerState).commands
  requires commands' == controller_state_looking_forward(
                rs'.server_logger.log, rs'.initControllerState).commands

  ensures |commands| <= |commands'|
  ensures commands == commands'[0 .. |commands| ]
  /*
  {
    assert rs.environment.nextStep.ios[0].LIoOpReceive?;
    assert rs.environment.nextStep.ios[0].r.msg.LogMessage?;
    lemma_received_packet_is_valid(rs, rs.environment.nextStep.ios[0].r);
    var log_entry := rs.environment.nextStep.ios[0].r.msg.log_entry;
    assert rs.server_logger.log + [log_entry] == rs'.server_logger.log;
    
    if (log_entry.LMProc?) {
    } else {
      var sac1 := controller_state_looking_forward(rs.server_logger.log, rs.initControllerState);
      var commands'' := controllerTransition(sac1.controllerState,
          log_entry.switch, log_entry.event).1;

      assert commands' == sac1.commands + commands'';
      assert sac1.commands == commands;
    }  
  }
  */

  lemma {:axiom}
  lemma_lmproc_outstandingEventsSet_matches(rs: RState, rs': RState, log_entry: LogEntry)
  requires rs'.server_switches == rs.server_switches
  requires rs'.server_logger.log == rs.server_logger.log + [log_entry]
  requires log_entry.LMProc?
  ensures refinement_outstandingEventsSet(rs.server_switches, rs.server_logger.log)
       == refinement_outstandingEventsSet(rs'.server_switches, rs'.server_logger.log)
  /*
  {
    forall switch | switch in rs.server_switches
    ensures forall eid :: eid in rs.server_switches[switch].bufferedEvents ==> (
         (forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
            !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
         == (forall entry :: entry in (rs.server_logger.log) ==>
            !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
       )
    {
      forall eid | eid in rs.server_switches[switch].bufferedEvents
      ensures (forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
            !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
         == (forall entry :: entry in (rs.server_logger.log) ==>
            !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
      {
      }
    }

    assert refinement_outstandingEventsSet(rs'.server_switches, rs'.server_logger.log)
        == (
          set
            switch : EndPoint, eid : int | (
              switch in rs'.server_switches &&
              eid in rs'.server_switches[switch].bufferedEvents &&
              (forall entry :: entry in rs'.server_logger.log ==>
                  !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
            ) ::
              ((switch, eid), SwitchEvent(switch, rs'.server_switches[switch].bufferedEvents[eid]))
          )
        == (
          set
            switch : EndPoint, eid : int | (
              switch in rs.server_switches &&
              eid in rs.server_switches[switch].bufferedEvents &&
              (forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
                  !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
            ) ::
              ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
          )
        == (
          set
            switch : EndPoint, eid : int | (
              switch in rs.server_switches &&
              eid in rs.server_switches[switch].bufferedEvents &&
              (forall entry :: entry in (rs.server_logger.log) ==>
                  !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
            ) ::
              ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
          )
        == refinement_outstandingEventsSet(rs'.server_switches, rs'.server_logger.log);
  }
  */

  lemma {:axiom}
  lemma_outstandingCommands(rs: RState, rs': RState, singleCommands: seq<SingleCommand>,
      log_entry: LogEntry, event: SwitchEvent)
  requires rstate_valid(rs)
  requires rstate_valid(rs')

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor == rs'.endpoint_logger
  requires Node_LoggerLogEvent(
              rs.server_logger, rs'.server_logger, rs.environment.nextStep.ios)
  requires rs.server_controllers == rs'.server_controllers
  requires rs.server_switches == rs'.server_switches

  requires rs.environment.nextStep.ios[0].r.msg.log_entry == log_entry
  requires log_entry.LMRecv?
  requires singleCommands ==
      controllerTransition(refinement(rs).controllerState, event.switch, event.event).1

  requires event == SwitchEvent(log_entry.switch, log_entry.event)

  ensures refinement(rs').outstandingCommands ==
      refinement(rs).outstandingCommands + seq_to_multiset(singleCommands)
  {
    var log_entry := rs.environment.nextStep.ios[0].r.msg.log_entry;

    assert controller_state_looking_forward(rs.server_logger.log, rs.initControllerState).controllerState
        == refinement(rs).controllerState;

    assert singleCommands ==
          controllerTransition(
              controller_state_looking_forward(rs.server_logger.log, rs.initControllerState).controllerState,
              event.switch, event.event).1;

    var fwdOutstandingCommands1 :=
          controller_state_looking_forward(
              rs.server_logger.log,
              rs.initControllerState).commands;

    assert rs'.server_logger.log == rs.server_logger.log + [log_entry];
    assert rs'.initControllerState == rs.initControllerState;

    var fwdOutstandingCommands2 :=
          controller_state_looking_forward(
              rs'.server_logger.log,
              rs'.initControllerState).commands;
    assert fwdOutstandingCommands2 ==
          controller_state_looking_forward(
              rs.server_logger.log + [log_entry],
              rs.initControllerState).commands
     ==
          controller_state_looking_forward(
              rs.server_logger.log,
              rs.initControllerState).commands +
          controllerTransition(
              controller_state_looking_forward(rs.server_logger.log, rs.initControllerState).controllerState,
              event.switch, event.event).1
      ==
          controller_state_looking_forward(
              rs.server_logger.log,
              rs.initControllerState).commands + singleCommands;

      lemma_command_ids_bounded(rs);
      lemma_filter_out_accepted_commands_plus_nonaccepted(rs,
          controller_state_looking_forward(rs.server_logger.log, rs.initControllerState).commands,
          singleCommands);

      assert refinement(rs').outstandingCommands
          == filter_out_accepted_commands(fwdOutstandingCommands2, rs.server_switches)
          == filter_out_accepted_commands(
              controller_state_looking_forward(rs.server_logger.log, rs.initControllerState).commands + singleCommands, rs.server_switches)
          == filter_out_accepted_commands(
              controller_state_looking_forward(rs.server_logger.log, rs.initControllerState).commands, rs.server_switches) + seq_to_multiset(singleCommands)
          == refinement(rs).outstandingCommands + seq_to_multiset(singleCommands);
  }

  lemma {:axiom} lemma_command_ids_bounded(rs: RState)
  requires rstate_valid(rs)
  ensures forall switch :: switch in rs.server_switches ==>
          forall command_id :: command_id in rs.server_switches[switch].received_command_ids ==>
          command_id <
            |controller_state_looking_forward(
                rs.server_logger.log, rs.initControllerState).commands|
  /*
  {
    reveal_accepted_commands_are_valid(); 
  }
  */

  lemma {:axiom} lemma_filter_out_accepted_commands_plus_nonaccepted(
      rs: RState,
      a: seq<SingleCommand>, b: seq<SingleCommand>)
  requires forall switch :: switch in rs.server_switches ==>
           forall command_id :: command_id in rs.server_switches[switch].received_command_ids ==>
           command_id < |a|
  ensures filter_out_accepted_commands(a + b, rs.server_switches) == 
          filter_out_accepted_commands(a, rs.server_switches) + seq_to_multiset(b)
  /*
  {
    reveal_seq_to_multiset();
    if (|b| == 0) {
      assert b == [];
      assert a + b == a;
      assert seq_to_multiset<SingleCommand>([]) == multiset{};
      assert 
          filter_out_accepted_commands(a + b, rs.server_switches) == 
          filter_out_accepted_commands(a, rs.server_switches) == 
          filter_out_accepted_commands(a, rs.server_switches) + multiset{} == 
          filter_out_accepted_commands(a, rs.server_switches) + seq_to_multiset(b);
    } else {
      lemma_filter_out_accepted_commands_plus_nonaccepted(rs, a, b[0 .. |b| - 1]);
      var command := b[|b| - 1];
      if (command.switch in rs.server_switches &&
           ((|a| + |b| - 1) in rs.server_switches[command.switch].received_command_ids)) {
        assert (|a| + |b| - 1) < |a|;
        assert false;
      }
      assert seq_to_multiset(b) == seq_to_multiset(b[0..|b|-1]) + multiset{b[|b|-1]};

      assert b[|b| - 1] == (a+b)[|a| + |b| - 1];
      assert (a + b)[0 .. |a + b| - 1] == a + b[0 .. |b| - 1];

      assert filter_out_accepted_commands(a + b, rs.server_switches)
          == filter_out_accepted_commands((a + b)[0 .. |a + b| - 1], rs.server_switches) +
                (
                  if !(
                      command.switch in rs.server_switches &&
                      (|a + b| - 1) in
                        rs.server_switches[command.switch].received_command_ids)
                  then multiset{(a + b)[|a+b|-1]} else multiset{}
                )
          == filter_out_accepted_commands((a + b)[0 .. |a + b| - 1], rs.server_switches) +
              multiset{(a + b)[|a+b|-1]}
          == filter_out_accepted_commands(a + b[0 .. |b| - 1], rs.server_switches) +
              multiset{command}
          == filter_out_accepted_commands(a, rs.server_switches) +
             seq_to_multiset(b[0 .. |b| - 1]) + multiset{command}
          == filter_out_accepted_commands(a, rs.server_switches) + seq_to_multiset(b);
    }
  }
  */

  lemma {:axiom} packet_validation_preservation(rs: RState, rs': RState)
  requires rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor == rs'.endpoint_logger
  requires Node_LoggerLogEvent(
              rs.server_logger, rs'.server_logger, rs.environment.nextStep.ios)
  requires rs.server_controllers == rs'.server_controllers
  requires rs.server_switches == rs'.server_switches
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
          }
          case EventAck(event_ack_id: int) => {
          }
          case CommandMessage(command: Command, command_id: int) => {
          }
          case CommandAck(command_ack_id: int) => {
          }
          case InitNewMaster(leader_id: int) => {
          }
          case NewMaster(master_id: int) => {
          }
          case NewMasterAck => {
          }
          case LogMessage(log_entry: LogEntry) => {
          }
          case LogBroadcastMessage(full_log: seq<LogEntry>) => {
          }
      }
    }
    reveal_packet_validation_preserved();
  }
  */

  lemma
  {:axiom}
  lemma_refines_LoggerLogEvent_multiset(rs: RState, rs': RState, log_entry: LogEntry)
  requires rstate_valid(rs)
  requires rstate_valid(rs')
  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor == rs'.endpoint_logger
  requires Node_LoggerLogEvent(
              rs.server_logger, rs'.server_logger, rs.environment.nextStep.ios)
  requires rs.server_controllers == rs'.server_controllers
  requires rs.server_switches == rs'.server_switches

  requires rs.environment.nextStep.ios[0].LIoOpReceive?;
  requires rs.environment.nextStep.ios[0].r.msg.LogMessage?;
  requires rs.environment.nextStep.ios[0].r.msg.log_entry == log_entry
  requires log_entry.LMRecv?
  requires is_valid_LogMessage(rs,
      rs.environment.nextStep.ios[0].r.src,
      rs.environment.nextStep.ios[0].r.dst,
      rs.environment.nextStep.ios[0].r.msg)

  ensures multiset_adds_one(refinement(rs').outstandingEvents, refinement(rs).outstandingEvents);
  ensures SwitchEvent(log_entry.switch, log_entry.event)
          == added_obj(refinement(rs').outstandingEvents, refinement(rs).outstandingEvents)
  /*
  {
      lemma_refines_LoggerLogEvent_multiset_helper1(rs, rs', log_entry);
      lemma_refines_LoggerLogEvent_multiset_helper2(rs, rs', log_entry);

      lemma_refines_LoggerLogEvent_outstandingEvents(
          refinement_outstandingEventsSet(rs'.server_switches, rs'.server_logger.log),
          refinement_outstandingEventsSet(rs.server_switches, rs.server_logger.log),
          (log_entry.switch, log_entry.event_id),
          SwitchEvent(log_entry.switch, log_entry.event));
  }
  */

  lemma
  {:axiom}
      lemma_refines_LoggerLogEvent_multiset_helper1
      (rs: RState, rs': RState, log_entry: LogEntry)
  requires rstate_valid(rs)
  requires rstate_valid(rs')
  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor == rs'.endpoint_logger
  requires Node_LoggerLogEvent(
              rs.server_logger, rs'.server_logger, rs.environment.nextStep.ios)
  requires rs.server_controllers == rs'.server_controllers
  requires rs.server_switches == rs'.server_switches

  requires rs.environment.nextStep.ios[0].LIoOpReceive?;
  requires rs.environment.nextStep.ios[0].r.msg.LogMessage?;
  requires rs.environment.nextStep.ios[0].r.msg.log_entry == log_entry
  requires log_entry.LMRecv?
  requires is_valid_LogMessage(rs,
      rs.environment.nextStep.ios[0].r.src,
      rs.environment.nextStep.ios[0].r.dst,
      rs.environment.nextStep.ios[0].r.msg)
  ensures (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      ) - (
      set
        switch : EndPoint, eid : int | (
          switch in rs'.server_switches &&
          eid in rs'.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs'.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs'.server_switches[switch].bufferedEvents[eid]))
      ) ==
      { ((log_entry.switch, log_entry.event_id),
             SwitchEvent(log_entry.switch, log_entry.event)) }
  /*
  {
    reveal_log_is_valid();

    assert rs'.server_logger.log == rs.server_logger.log + [log_entry];
    assert rs.server_switches == rs'.server_switches;

    assert log_entry.switch in rs.server_switches;
    assert log_entry.event_id in rs.server_switches[log_entry.switch].bufferedEvents;
    assert rs.server_switches[log_entry.switch].bufferedEvents[log_entry.event_id]
        == log_entry.event;

    assert log_is_valid(rs.server_switches, rs.server_logger.log);
    assert forall entry :: entry in rs.server_logger.log ==>
                    is_valid_log_entry(rs.server_switches, entry);

    forall entry | entry in rs.server_logger.log
      ensures !(entry.LMRecv? && entry.event_id == log_entry.event_id &&
                entry.switch == log_entry.switch);
    {
      assert is_valid_log_entry(rs.server_switches, entry);
    }

    assert (forall entry :: entry in rs.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == log_entry.event_id &&
                  entry.switch == log_entry.switch));

    assert 
      (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      ) - (
      set
        switch : EndPoint, eid : int | (
          switch in rs'.server_switches &&
          eid in rs'.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs'.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs'.server_switches[switch].bufferedEvents[eid]))
      )
      ==
      (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      ) - (
      set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs'.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      )
      ==
      (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
          && !(
            switch in rs.server_switches &&
            eid in rs.server_switches[switch].bufferedEvents &&
            (forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
                !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
          )
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      )
      ==
      (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
          && !(
            (forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
                !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
          )
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      )
      ==
      (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
          && (log_entry.LMRecv? && log_entry.event_id == eid && log_entry.switch == switch)
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      )
      ==
      { ((log_entry.switch, log_entry.event_id),
             SwitchEvent(log_entry.switch,
             rs.server_switches[log_entry.switch].bufferedEvents[log_entry.event_id])) }
      ==
      { ((log_entry.switch, log_entry.event_id),
             SwitchEvent(log_entry.switch, log_entry.event)) }
      ;

      assert (forall switch : EndPoint :: forall eid : int :: (
            switch in rs.server_switches &&
            eid in rs.server_switches[switch].bufferedEvents &&
            (forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
                !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
          ) ==> (
            switch in rs.server_switches &&
            eid in rs.server_switches[switch].bufferedEvents &&
            (forall entry :: entry in rs.server_logger.log ==>
                !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
          )
        );

      assert (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      ) >= (
      set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      );
      
      assert (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      )
      ==
      (
      set
        switch : EndPoint, eid : int | (
          switch in rs'.server_switches &&
          eid in rs'.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs'.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs'.server_switches[switch].bufferedEvents[eid]))
      );

  }
  */

  lemma
  {:axiom}
      lemma_refines_LoggerLogEvent_multiset_helper2
      (rs: RState, rs': RState, log_entry: LogEntry)
  requires rstate_valid(rs)
  requires rstate_valid(rs')
  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor == rs'.endpoint_logger
  requires Node_LoggerLogEvent(
              rs.server_logger, rs'.server_logger, rs.environment.nextStep.ios)
  requires rs.server_controllers == rs'.server_controllers
  requires rs.server_switches == rs'.server_switches

  requires rs.environment.nextStep.ios[0].LIoOpReceive?;
  requires rs.environment.nextStep.ios[0].r.msg.LogMessage?;
  requires rs.environment.nextStep.ios[0].r.msg.log_entry == log_entry
  requires log_entry.LMRecv?
  requires is_valid_LogMessage(rs,
      rs.environment.nextStep.ios[0].r.src,
      rs.environment.nextStep.ios[0].r.dst,
      rs.environment.nextStep.ios[0].r.msg)
  ensures (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      ) >= (
      set
        switch : EndPoint, eid : int | (
          switch in rs'.server_switches &&
          eid in rs'.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs'.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs'.server_switches[switch].bufferedEvents[eid]))
      )
      /*
  {
      assert (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      ) >= (
      set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      );
      
      assert (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      )
      ==
      (
      set
        switch : EndPoint, eid : int | (
          switch in rs'.server_switches &&
          eid in rs'.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs'.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs'.server_switches[switch].bufferedEvents[eid]))
      );
  }
  */

  lemma {:axiom} lemma_refines_LoggerLogEvent_outstandingEvents<A,B>
        (s : set<(A,B)>, s' : set<(A,B)>, key : A, t : B)
  requires s' >= s
  requires s' - s == {(key, t)}
  ensures multiset_adds_one(set_to_multiset(s), set_to_multiset(s'))
  ensures added_obj(set_to_multiset(s), set_to_multiset(s')) == t
  /*
  {
    if (|s| == 0) {
      assert set_to_multiset(s) == multiset{};
      assert set_to_multiset(s') == multiset{t};
      var y :| y in set_to_multiset(s') - set_to_multiset(s);
      assert y == added_obj(set_to_multiset(s), set_to_multiset(s'));
      assert set_to_multiset(s') - set_to_multiset(s) == multiset{t};
      assert y == t;
    } else {
      var y :| y in s;
      assert y in s';
      lemma_refines_LoggerLogEvent_outstandingEvents(s - {y}, s' - {y}, key, t);
      assert set_to_multiset(s) == set_to_multiset(s - {y}) + multiset{y.1};
      assert set_to_multiset(s') == set_to_multiset(s' - {y}) + multiset{y.1};

      assert |set_to_multiset(s') - set_to_multiset(s)| ==
              |(set_to_multiset(s' - {y}) + multiset{t}) - 
              (set_to_multiset(s - {y}) + multiset{t})|
          == |set_to_multiset(s' - {y}) - set_to_multiset(s - {y})|
          == 1;
      
      assert |set_to_multiset(s')| - |set_to_multiset(s)| ==
              |set_to_multiset(s' - {y}) + multiset{t}| - 
              |set_to_multiset(s - {y}) + multiset{t}|
        ==
              |set_to_multiset(s' - {y})| + |multiset{t}| - 
              (|set_to_multiset(s - {y})| + |multiset{t}|)
        ==
              |set_to_multiset(s' - {y})| - |set_to_multiset(s - {y})|
        == 1; 
      
      assert added_obj(set_to_multiset(s - {y}), set_to_multiset(s' - {y})) == t;

      assert t in ((set_to_multiset(s' - {y})) - set_to_multiset(s - {y}));

      assert set_to_multiset(s - {y}) == set_to_multiset(s) - multiset{y.1};
      assert set_to_multiset(s' - {y}) == set_to_multiset(s') - multiset{y.1};

      assert ((set_to_multiset(s' - {y})) - set_to_multiset(s - {y}))
        == (set_to_multiset(s') - multiset{y.1}) - (set_to_multiset(s) - multiset{y.1})
        == set_to_multiset(s') - set_to_multiset(s);

      assert t in set_to_multiset(s') - set_to_multiset(s);

      assert t in ((set_to_multiset(s')) - set_to_multiset(s));

      assert forall t' :: t' in (set_to_multiset(s') - set_to_multiset(s)) ==> t' == t;

      var z :| z in (set_to_multiset(s') - set_to_multiset(s));
      assert z == t;
      assert z == added_obj(set_to_multiset(s), set_to_multiset(s'));
    }
  }
  */

}
