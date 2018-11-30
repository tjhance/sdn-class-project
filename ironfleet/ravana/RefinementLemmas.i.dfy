include "Types.i.dfy"
include "Refinement.i.dfy"
include "Service.i.dfy"
include "DistributedSystem.i.dfy"
include "../src/Dafny/Distributed/Common/Framework/Environment.s.dfy"

module RefinementLemmas_i {
  import opened Types_i
  import opened Refinement_i
  import opened Service_i
  import opened DistributedSystem_i
  import opened Environment_s

  predicate {:opaque} packet_validation_preserved(rs: RState, rs': RState)
  {
    forall p : LPacket<EndPoint, RavanaMessage>
             :: is_valid_message(rs, p.src, p.dst, p.msg) ==>
                is_valid_message(rs', p.src, p.dst, p.msg)
  }

  lemma lemma_packets_are_valid_no_sending(rs: RState, rs': RState)
  requires rstate_valid(rs)
  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires packet_validation_preserved(rs, rs')
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires forall io :: io in rs.environment.nextStep.ios ==> !io.LIoOpSend?
  ensures packets_are_valid(rs')
  {
      assert rs'.environment.sentPackets == rs.environment.sentPackets +
          (set io | io in rs.environment.nextStep.ios && io.LIoOpSend? :: io.s);

      assert rs'.environment.sentPackets == rs.environment.sentPackets;

      reveal_packets_are_valid();
      assert packets_are_valid(rs);
      assert forall p :: p in rs.environment.sentPackets ==> is_valid_message(rs, p.src, p.dst, p.msg);

      forall p | p in rs'.environment.sentPackets
        ensures is_valid_message(rs', p.src, p.dst, p.msg)
      {
        assert p in rs.environment.sentPackets;
        assert is_valid_message(rs, p.src, p.dst, p.msg);
        reveal_packet_validation_preserved();
      }
  }

  lemma
  {:fuel is_valid_message,0,0}
  lemma_received_packet_is_valid(
      rs: RState, rs': RState,
      packet: LPacket<EndPoint, RavanaMessage>)
  requires rstate_valid(rs)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires |rs.environment.nextStep.ios| >= 1
  requires rs.environment.nextStep.ios[0].LIoOpReceive?
  requires packet == rs.environment.nextStep.ios[0].r
  ensures is_valid_message(rs, packet.src, packet.dst, packet.msg)
  {
    assert packets_are_valid(rs);
    assert packet in rs.environment.sentPackets;
    reveal_packets_are_valid();
  }

  lemma lemma_packets_are_valid_sending_1(rs: RState, rs': RState)
  requires rstate_valid(rs)
  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires packet_validation_preserved(rs, rs')
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires |rs.environment.nextStep.ios| == 1
  requires rs.environment.nextStep.ios[0].LIoOpSend?
  requires is_valid_message(rs', 
      rs.environment.nextStep.ios[0].s.src,
      rs.environment.nextStep.ios[0].s.dst,
      rs.environment.nextStep.ios[0].s.msg)
  ensures packets_are_valid(rs')
  {
      assert rs'.environment.sentPackets == rs.environment.sentPackets +
          (set io | io in rs.environment.nextStep.ios && io.LIoOpSend? :: io.s);

      assert rs'.environment.sentPackets == rs.environment.sentPackets +
          { rs.environment.nextStep.ios[0].s };

      reveal_packets_are_valid();
      assert packets_are_valid(rs);
      assert forall p :: p in rs.environment.sentPackets ==> is_valid_message(rs, p.src, p.dst, p.msg);

      forall p | p in rs'.environment.sentPackets
        ensures is_valid_message(rs', p.src, p.dst, p.msg)
      {
        if (p == rs.environment.nextStep.ios[0].s) {
        } else {
          assert p in rs.environment.sentPackets;
          assert is_valid_message(rs, p.src, p.dst, p.msg);
          reveal_packet_validation_preserved();
        }
      }
  }

  lemma lemma_packets_are_valid_send_and_recv(rs: RState, rs': RState)
  requires rstate_valid(rs)
  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires packet_validation_preserved(rs, rs')
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires |rs.environment.nextStep.ios| == 2
  requires ! rs.environment.nextStep.ios[0].LIoOpSend?
  requires rs.environment.nextStep.ios[1].LIoOpSend?
  requires is_valid_message(rs', 
      rs.environment.nextStep.ios[1].s.src,
      rs.environment.nextStep.ios[1].s.dst,
      rs.environment.nextStep.ios[1].s.msg)
  ensures packets_are_valid(rs')
  {
      assert rs'.environment.sentPackets == rs.environment.sentPackets +
          (set io | io in rs.environment.nextStep.ios && io.LIoOpSend? :: io.s);

      assert rs'.environment.sentPackets == rs.environment.sentPackets +
          { rs.environment.nextStep.ios[1].s };

      reveal_packets_are_valid();
      assert packets_are_valid(rs);
      assert forall p :: p in rs.environment.sentPackets ==> is_valid_message(rs, p.src, p.dst, p.msg);

      forall p | p in rs'.environment.sentPackets
        ensures is_valid_message(rs', p.src, p.dst, p.msg)
      {
        if (p == rs.environment.nextStep.ios[1].s) {
        } else {
          assert p in rs.environment.sentPackets;
          assert is_valid_message(rs, p.src, p.dst, p.msg);
          reveal_packet_validation_preserved();
        }
      }
  }

  lemma lemma_outstanding_commands_eq(rs: RState, rs': RState)
  requires  rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor in rs.switches
  requires rs.environment.nextStep.actor in rs'.switches
  requires rs.switches[rs.environment.nextStep.actor].received_command_ids ==
           rs'.switches[rs.environment.nextStep.actor].received_command_ids
  requires rs.controllers == rs'.controllers
  requires rs.logger == rs'.logger
  requires rs'.switches == rs.switches[
        rs.environment.nextStep.actor := rs'.switches[rs.environment.nextStep.actor]]

  ensures refinement_outstandingCommands(rs.logger.log, rs.initControllerState,
          rs.switches) ==
          refinement_outstandingCommands(rs'.logger.log, rs'.initControllerState,
          rs'.switches)
  {
    var fwdOutstandingCommands := 
        controller_state_looking_forward(rs.logger.log, rs.initControllerState).commands;
    lemma_filter_out_accepted_commands_eq(rs, rs', fwdOutstandingCommands);
  }

  lemma lemma_filter_out_accepted_commands_eq(rs: RState, rs': RState, commands: seq<SingleCommand>)
  requires  rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor in rs.switches
  requires rs.environment.nextStep.actor in rs'.switches
  requires rs.switches[rs.environment.nextStep.actor].received_command_ids ==
           rs'.switches[rs.environment.nextStep.actor].received_command_ids
  requires rs.controllers == rs'.controllers
  requires rs.logger == rs'.logger
  requires rs'.switches == rs.switches[
        rs.environment.nextStep.actor := rs'.switches[rs.environment.nextStep.actor]]

  ensures filter_out_accepted_commands(commands, rs.switches)
       == filter_out_accepted_commands(commands, rs'.switches)
  {
    if (|commands| > 0) {
      lemma_filter_out_accepted_commands_eq(rs, rs', commands[0 .. |commands| - 1]);
    }
  }

  lemma
  lemma_accepted_commands_are_valid_if_received_command_ids_unchanged
  (rs: RState, rs': RState)
  requires  rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor in rs.switches
  requires rs.environment.nextStep.actor in rs'.switches
  requires rs.switches[rs.environment.nextStep.actor].received_command_ids ==
           rs'.switches[rs.environment.nextStep.actor].received_command_ids
  requires rs.controllers == rs'.controllers
  requires rs.logger == rs'.logger
  requires rs'.switches == rs.switches[
        rs.environment.nextStep.actor := rs'.switches[rs.environment.nextStep.actor]]

  ensures accepted_commands_are_valid(rs'.initControllerState,
        rs'.switches, rs'.logger.log)
  {
    reveal_accepted_commands_are_valid();
  }

  lemma lemma_outstanding_events_eq(rs: RState, rs': RState)
  requires  rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor in rs.switches
  requires rs.environment.nextStep.actor in rs'.switches
  requires rs.switches[rs.environment.nextStep.actor].bufferedEvents ==
           rs'.switches[rs.environment.nextStep.actor].bufferedEvents
  requires rs.controllers == rs'.controllers
  requires rs.logger == rs'.logger
  requires rs'.switches == rs.switches[
        rs.environment.nextStep.actor := rs'.switches[rs.environment.nextStep.actor]]

  ensures refinement_outstandingEvents(rs.switches, rs.logger.log)
       == refinement_outstandingEvents(rs'.switches, rs'.logger.log)
  {
    lemma_outstanding_events_set_eq(rs, rs');
  }

  lemma lemma_outstanding_events_set_eq(rs: RState, rs': RState)
  requires  rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor in rs.switches
  requires rs.environment.nextStep.actor in rs'.switches
  requires rs.switches[rs.environment.nextStep.actor].bufferedEvents ==
           rs'.switches[rs.environment.nextStep.actor].bufferedEvents
  requires rs.controllers == rs'.controllers
  requires rs.logger == rs'.logger
  requires rs'.switches == rs.switches[
        rs.environment.nextStep.actor := rs'.switches[rs.environment.nextStep.actor]]

  ensures refinement_outstandingEventsSet(rs.switches, rs.logger.log)
       == refinement_outstandingEventsSet(rs'.switches, rs'.logger.log)
  {
  }

  lemma lemma_controllers_recved_events_valid_if_recved_events_unchanged(
      rs: RState, rs': RState)
  requires rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor in rs.controllers
  requires rs.environment.nextStep.actor in rs'.controllers
  requires rs.controllers[rs.environment.nextStep.actor].recved_events ==
           rs'.controllers[rs.environment.nextStep.actor].recved_events
  requires rs.switches == rs'.switches
  requires rs.logger == rs'.logger
  requires rs'.controllers == rs.controllers[
        rs.environment.nextStep.actor := rs'.controllers[rs.environment.nextStep.actor]]
  ensures controllers_recved_events_valid(
      rs'.switches,
      rs'.controllers)
  {
    reveal_controllers_recved_events_valid();
  }

  lemma
  lemma_controllers_log_valid_if_log_copy_unchanged(
      rs: RState, rs': RState)
  requires rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor in rs.controllers
  requires rs.environment.nextStep.actor in rs'.controllers
  requires rs.controllers[rs.environment.nextStep.actor].log_copy ==
           rs'.controllers[rs.environment.nextStep.actor].log_copy
  requires rs.switches == rs'.switches
  requires rs.logger == rs'.logger
  requires rs'.controllers == rs.controllers[
        rs.environment.nextStep.actor := rs'.controllers[rs.environment.nextStep.actor]]
  ensures controllers_log_valid(
      rs'.logger.log,
      rs'.controllers)
  {
    reveal_controllers_log_valid();
  }

  lemma
  lemma_controllers_state_correct_if_controller_stuff_unchanged(
      rs: RState, rs': RState)
  requires rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor in rs.controllers
  requires rs.environment.nextStep.actor in rs'.controllers

  requires is_prefix(
              rs.controllers[rs.environment.nextStep.actor].log_copy,
              rs'.controllers[rs.environment.nextStep.actor].log_copy
            )
  requires rs.controllers[rs.environment.nextStep.actor].buffered_commands ==
           rs'.controllers[rs.environment.nextStep.actor].buffered_commands

  requires rs.controllers[rs.environment.nextStep.actor].idx ==
           rs'.controllers[rs.environment.nextStep.actor].idx
  requires rs.controllers[rs.environment.nextStep.actor].current_command_id ==
           rs'.controllers[rs.environment.nextStep.actor].current_command_id
  requires rs.controllers[rs.environment.nextStep.actor].controllerState ==
           rs'.controllers[rs.environment.nextStep.actor].controllerState

  requires rs.switches == rs'.switches
  requires rs.logger == rs'.logger
  requires rs'.controllers == rs.controllers[
        rs.environment.nextStep.actor := rs'.controllers[rs.environment.nextStep.actor]]
  ensures controllers_state_correct(
      rs'.initControllerState,
      rs'.controllers,
      rs'.switches)
  {
    lemma_controllers_state_correct_if_controller_stuff_unchanged1(rs, rs');
  }

  lemma
  lemma_controllers_state_correct_if_controller_stuff_unchanged1(
      rs: RState, rs': RState)
  requires rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor in rs.controllers
  requires rs.environment.nextStep.actor in rs'.controllers

  requires is_prefix(
              rs.controllers[rs.environment.nextStep.actor].log_copy,
              rs'.controllers[rs.environment.nextStep.actor].log_copy
            )
  requires (forall xid ::
     xid in rs'.controllers[rs.environment.nextStep.actor].buffered_commands ==>
     xid in rs.controllers[rs.environment.nextStep.actor].buffered_commands &&
     forall command_id ::
     command_id in rs'.controllers[rs.environment.nextStep.actor].buffered_commands[xid] ==>
     command_id in rs.controllers[rs.environment.nextStep.actor].buffered_commands[xid] &&
     rs'.controllers[rs.environment.nextStep.actor].buffered_commands[xid][command_id] ==
     rs.controllers[rs.environment.nextStep.actor].buffered_commands[xid][command_id]
     )

  requires rs.controllers[rs.environment.nextStep.actor].idx ==
           rs'.controllers[rs.environment.nextStep.actor].idx
  requires rs.controllers[rs.environment.nextStep.actor].current_command_id ==
           rs'.controllers[rs.environment.nextStep.actor].current_command_id
  requires rs.controllers[rs.environment.nextStep.actor].controllerState ==
           rs'.controllers[rs.environment.nextStep.actor].controllerState

  requires rs.switches == rs'.switches
  requires rs.logger == rs'.logger
  requires rs'.controllers == rs.controllers[
        rs.environment.nextStep.actor := rs'.controllers[rs.environment.nextStep.actor]]
  ensures controllers_state_correct(
      rs'.initControllerState,
      rs'.controllers,
      rs'.switches)
  {
    reveal_controllers_state_correct();

    forall ep | ep in rs'.controllers
    ensures controller_state_correct(rs'.initControllerState, rs'.controllers[ep], rs'.switches)
    {
      if (ep == rs.environment.nextStep.actor) {
        assert controller_state_correct(
            rs.initControllerState, rs.controllers[ep], rs.switches);

        var s := rs.controllers[rs.environment.nextStep.actor];
        var s' := rs'.controllers[rs.environment.nextStep.actor];
        assert s'.idx == s.idx;
        assert s.idx <= |s.log_copy|;
        assert |s.log_copy| <= |s'.log_copy|;
        assert 0 <= s'.idx <= |s'.log_copy|;

        assert s.log_copy[0 .. s.idx] == s'.log_copy[0 .. s'.idx];

        forall xid | xid in s'.buffered_commands
        ensures
          buffered_commands_correct(rs'.initControllerState,
              xid, s'.log_copy, s'.buffered_commands[xid], rs'.switches)
        {
          assert buffered_commands_correct(rs.initControllerState,
              xid, s.log_copy, s.buffered_commands[xid], rs.switches);
          assert s'.log_copy[0 .. xid] == s.log_copy[0 .. xid];
        }

        assert controller_state_correct(rs'.initControllerState,
            rs'.controllers[ep], rs'.switches);
      } else {
        assert controller_state_correct(rs'.initControllerState,
            rs'.controllers[ep], rs'.switches);
      }
    }
  }

  lemma lemma_prefix_of_log_gives_prefix_of_commands(
      log1: seq<LogEntry>,
      log2: seq<LogEntry>,
      init: ControllerState)
  requires is_prefix(log1, log2)
  ensures is_prefix(
      controller_state_looking_forward(log1, init).commands,
      controller_state_looking_forward(log2, init).commands
    )
  {
    if (|log1| == |log2|) {
      assert log1 == log2;
    } else {
      assert |log2| > |log1|;
      assert is_prefix(log1, log2[0 .. |log2| - 1]);
      lemma_prefix_of_log_gives_prefix_of_commands(log1, log2[0 .. |log2| - 1], init);
    }
  }

  lemma lemma_controller_recved_events_valid_for_switch_change(rs: RState, rs': RState)
  requires rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor in rs.switches
  requires rs.environment.nextStep.actor in rs'.switches

  requires (forall be ::
      be in rs.switches[rs.environment.nextStep.actor].bufferedEvents ==>
      be in rs'.switches[rs.environment.nextStep.actor].bufferedEvents &&
      rs.switches[rs.environment.nextStep.actor].bufferedEvents[be] ==
      rs'.switches[rs.environment.nextStep.actor].bufferedEvents[be]
    )

  requires rs.controllers == rs'.controllers
  requires rs.logger == rs'.logger
  requires rs'.switches == rs.switches[
        rs.environment.nextStep.actor := rs'.switches[rs.environment.nextStep.actor]]
  ensures controllers_recved_events_valid(
      rs'.switches,
      rs'.controllers)
  {
    reveal_controllers_recved_events_valid();
  }

  lemma lemma_controllers_state_correct_for_switch_change(rs: RState, rs': RState)
  requires rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor in rs.switches
  requires rs.environment.nextStep.actor in rs'.switches

  requires (forall be ::
      be in rs.switches[rs.environment.nextStep.actor].bufferedEvents ==>
      be in rs'.switches[rs.environment.nextStep.actor].bufferedEvents &&
      rs.switches[rs.environment.nextStep.actor].bufferedEvents[be] ==
      rs'.switches[rs.environment.nextStep.actor].bufferedEvents[be]
    )

  requires rs.controllers == rs'.controllers
  requires rs.logger == rs'.logger
  requires rs'.switches == rs.switches[
        rs.environment.nextStep.actor := rs'.switches[rs.environment.nextStep.actor]]
  ensures controllers_state_correct(
      rs'.initControllerState,
      rs'.controllers,
      rs'.switches)
  {
    reveal_controllers_state_correct();
  }
}
