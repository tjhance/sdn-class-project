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

  lemma {:axiom} lemma_packets_are_valid_no_sending(rs: RState, rs': RState)
  requires rstate_valid(rs)
  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires packet_validation_preserved(rs, rs')
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires forall io :: io in rs.environment.nextStep.ios ==> !io.LIoOpSend?
  ensures packets_are_valid(rs')
  /*
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
  */

  lemma
  {:axiom}
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
  /*
  {
    assert packets_are_valid(rs);
    assert packet in rs.environment.sentPackets;
    reveal_packets_are_valid();
  }
  */

  lemma {:axiom} lemma_packets_are_valid_sending_1(rs: RState, rs': RState)
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
  /*
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
  */

  lemma {:axiom} lemma_packets_are_valid_send_and_recv(rs: RState, rs': RState)
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
  /*
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
  */

  lemma {:axiom} lemma_outstanding_commands_eq(rs: RState, rs': RState)
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
  /*
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
  */

  lemma {:axiom}
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
  /*
  {
    reveal_accepted_commands_are_valid();
  }
  */

  lemma {:axiom} lemma_outstanding_events_eq(rs: RState, rs': RState)
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
  /*
  {
    lemma_outstanding_events_set_eq(rs, rs');
  }
  */

  lemma {:axiom} lemma_outstanding_events_set_eq(rs: RState, rs': RState)
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
  /*
  {
  }
  */

  lemma {:axiom} lemma_controllers_recved_events_valid_if_recved_events_unchanged(
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
  /*
  {
    reveal_controllers_recved_events_valid();
  }
  */

  lemma
  {:axiom}
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
  /*
  {
    reveal_controllers_log_valid();
  }
  */

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
  requires rs.controllers[rs.environment.nextStep.actor].log_copy ==
           rs'.controllers[rs.environment.nextStep.actor].log_copy
  requires rs.switches == rs'.switches
  requires rs.logger == rs'.logger
  requires rs'.controllers == rs.controllers[
        rs.environment.nextStep.actor := rs'.controllers[rs.environment.nextStep.actor]]
  ensures controllers_state_correct(
      rs'.initControllerState,
      rs'.controllers,
      rs'.switches)
  /*
  {
    reveal_controllers_log_valid();
  }
  */

}
