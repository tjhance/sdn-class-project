include "../Types.i.dfy"
include "../Refinement.i.dfy"
include "../Service.i.dfy"
include "../DistributedSystem.i.dfy"
include "../RefinementLemmas.i.dfy"

module Refinement_Proof_SwitchRecvCommand {
  import opened Types_i
  import opened Refinement_i
  import opened Service_i
  import opened DistributedSystem_i
  import opened RefinementLemmas_i

  predicate conditions(rs: RState, rs': RState)
  {
    rstate_valid(rs)

    && LEnvironment_Next(rs.environment, rs'.environment)
    && rs.environment.nextStep.LEnvStepHostIos?
    && rs.endpoint_logger == rs'.endpoint_logger
    && rs.initControllerState == rs'.initControllerState
    && rs.environment.nextStep.actor in rs.switches
    && rs.environment.nextStep.actor in rs'.switches
    && Node_SwitchRecvCommand(
                rs.switches[rs.environment.nextStep.actor],
                rs'.switches[rs.environment.nextStep.actor],
                rs.environment.nextStep.ios)
    && rs.controllers == rs'.controllers
    && rs.logger == rs'.logger
    && rs'.switches == rs.switches[
        rs.environment.nextStep.actor := rs'.switches[rs.environment.nextStep.actor]]
  }

  lemma lemma_refines_SwitchRecvCommand(rs: RState, rs': RState)
  requires conditions(rs, rs')

  ensures rstate_valid(rs')
  ensures Service_NextApplyCommand(refinement(rs), refinement(rs'))
  {
    lemma_packets_are_valid(rs, rs');
    lemma_log_is_valid(rs, rs');
    lemma_accepted_commands_are_valid(rs, rs');
    lemma_switches_valid(rs, rs');

    lemma_controller_recved_events_valid_for_switch_change(rs, rs');
    lemma_controllers_state_correct_for_switch_change(rs, rs');

    lemma_outstanding_events_eq(rs, rs');

    var sc := SingleCommand(rs.environment.nextStep.actor,
                            rs.environment.nextStep.ios[0].r.msg.command);

    lemma_multiset(rs, rs', sc);
  }

  lemma lemma_packets_are_valid(rs: RState, rs': RState)
  requires conditions(rs, rs')
  ensures packets_are_valid(rs')
  {
    packet_validation_preservation(rs, rs');
    lemma_packets_are_valid_no_sending(rs, rs');
  }

  lemma packet_validation_preservation(rs: RState, rs': RState)
  requires conditions(rs, rs')
  ensures packet_validation_preserved(rs, rs')
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
            assert is_valid_LogMessage(rs', p.src, p.dst, p.msg);
          }
          case LogBroadcastMessage(full_log: seq<LogEntry>) => {
            assert is_valid_LogBroadcastMessage(rs', p.src, p.dst, p.msg);
          }
      }
    }
    reveal_packet_validation_preserved();
  }

  lemma lemma_log_is_valid(rs: RState, rs': RState)
  requires conditions(rs, rs')
  ensures log_is_valid(rs'.switches, rs'.logger.log)
  {
    reveal_log_is_valid();
  }

  lemma lemma_accepted_commands_are_valid(rs: RState, rs': RState)
  requires conditions(rs, rs')
  ensures accepted_commands_are_valid(rs'.initControllerState,
        rs'.switches, rs'.logger.log)
  {
    reveal_accepted_commands_are_valid();

    var all_commands := controller_state_looking_forward(
                rs'.logger.log, rs'.initControllerState).commands;

    var s := rs.switches[rs.environment.nextStep.actor];

    forall ep | ep in rs'.switches
      ensures forall command_id :: command_id in rs'.switches[ep].received_command_ids ==>
        0 <= command_id < |all_commands| &&
        all_commands[command_id].switch == ep
    {
      forall command_id | command_id in rs'.switches[ep].received_command_ids
      ensures 0 <= command_id < |all_commands|
      ensures all_commands[command_id].switch == ep
      {
        if (ep != rs.environment.nextStep.actor) {
          assert 0 <= command_id < |all_commands|;
          assert all_commands[command_id].switch == ep;
        } else {
          assert command_id in (s.received_command_ids +
              [rs.environment.nextStep.ios[0].r.msg.command_id]);
          if (command_id in s.received_command_ids) {
            assert 0 <= command_id < |all_commands|;
            assert all_commands[command_id].switch == ep;
          } else {
            assert command_id == rs.environment.nextStep.ios[0].r.msg.command_id;
            lemma_valid_command_msg(rs, rs');
            assert 0 <= command_id < |all_commands|;
            assert all_commands[command_id].switch == ep;
          }
        }
      }
    }
  }

  lemma lemma_valid_command_msg(rs: RState, rs': RState)
  requires conditions(rs, rs')
  ensures is_valid_CommandMessage(rs,
      rs.environment.nextStep.ios[0].r.src,
      rs.environment.nextStep.ios[0].r.dst,
      rs.environment.nextStep.ios[0].r.msg)
  {
    reveal_packets_are_valid();
  }

  lemma lemma_switches_valid(rs: RState, rs': RState)
  requires conditions(rs, rs')
  ensures switches_valid(rs'.switches)
  {
    reveal_switches_valid();
  }

  lemma lemma_multiset(rs: RState, rs': RState, sc: SingleCommand)
  requires conditions(rs, rs')
  requires rstate_valid(rs')
  requires sc == SingleCommand(rs.environment.nextStep.actor,
                               rs.environment.nextStep.ios[0].r.msg.command)
  ensures multiset_adds_one(
      refinement(rs').outstandingCommands,
      refinement(rs).outstandingCommands)
  ensures sc == added_obj(
      refinement(rs').outstandingCommands,
      refinement(rs).outstandingCommands)
  {
    lemma_multiset_inc(rs, rs', sc);
    reveal_added_obj();
  }

  lemma lemma_multiset_inc(rs: RState, rs': RState, sc: SingleCommand)
  requires conditions(rs, rs')
  requires rstate_valid(rs')
  requires sc == SingleCommand(rs.environment.nextStep.actor,
                               rs.environment.nextStep.ios[0].r.msg.command)
  ensures refinement_outstandingCommands(rs.logger.log, rs.initControllerState, rs.switches)
       == refinement_outstandingCommands(rs'.logger.log, rs'.initControllerState, rs'.switches) + multiset{sc}
  {
    lemma_incoming_command_matches_log(rs, rs', sc,
              rs.environment.nextStep.ios[0].r.msg.command_id);
    lemma_filter_out_accepted_commands_inc(rs, rs', sc,
              rs.environment.nextStep.ios[0].r.msg.command_id,
              controller_state_looking_forward(
                rs'.logger.log, rs'.initControllerState).commands);
    assert refinement_outstandingCommands(rs.logger.log, rs.initControllerState, rs.switches)
        == filter_out_accepted_commands(controller_state_looking_forward(
              rs.logger.log, rs.initControllerState).commands, rs.switches)
        == filter_out_accepted_commands(controller_state_looking_forward(
              rs'.logger.log, rs'.initControllerState).commands, rs'.switches)
            + multiset{sc}
        == refinement_outstandingCommands(rs'.logger.log, rs'.initControllerState, rs'.switches)
            + multiset{sc};
  }

  lemma lemma_filter_out_accepted_commands_inc(
      rs: RState, rs': RState, sc: SingleCommand, idx: int, comms: seq<SingleCommand>)
  requires conditions(rs, rs')
  requires rstate_valid(rs')
  requires 0 <= idx < |comms|
  requires comms[idx] == sc
  requires sc.switch in rs.switches
  requires !(idx in rs.switches[sc.switch].received_command_ids)
  requires rs'.switches[sc.switch].received_command_ids ==
             rs.switches[sc.switch].received_command_ids + [idx]
  ensures  filter_out_accepted_commands(comms, rs.switches)
        == filter_out_accepted_commands(comms, rs'.switches)
            + multiset{sc}
  {
    assert |comms| != 0;
    if (idx == |comms| - 1) {
      lemma_filter_out_accepted_commands_inc2(rs, rs', sc, idx, comms[0 .. |comms| - 1]);
    } else {
      lemma_filter_out_accepted_commands_inc(rs, rs', sc, idx, comms[0 .. |comms| - 1]);
    }
  }

  lemma lemma_filter_out_accepted_commands_inc2(
      rs: RState, rs': RState, sc: SingleCommand, idx: int, comms: seq<SingleCommand>)
  requires conditions(rs, rs')
  requires rstate_valid(rs')
  requires |comms| <= idx
  requires sc.switch in rs.switches
  requires !(idx in rs.switches[sc.switch].received_command_ids)
  requires rs'.switches[sc.switch].received_command_ids ==
             rs.switches[sc.switch].received_command_ids + [idx]
  ensures  filter_out_accepted_commands(comms, rs.switches)
        == filter_out_accepted_commands(comms, rs'.switches)
  {
    if (|comms| == 0) {
    } else {
      lemma_filter_out_accepted_commands_inc2(rs, rs', sc, idx, comms[0 .. |comms| - 1]);
    }
  }

  lemma lemma_incoming_command_matches_log(rs: RState, rs': RState, sc: SingleCommand,
      command_id: int)
  requires conditions(rs, rs')
  requires rstate_valid(rs')
  requires command_id == rs.environment.nextStep.ios[0].r.msg.command_id
  requires sc == SingleCommand(rs.environment.nextStep.actor,
                               rs.environment.nextStep.ios[0].r.msg.command)
  ensures 0 <= command_id < |controller_state_looking_forward(
                rs.logger.log, rs.initControllerState).commands|
  ensures controller_state_looking_forward(
                rs.logger.log, rs.initControllerState).commands[command_id] == sc
  {
    lemma_valid_command_msg(rs, rs');
  }
}
