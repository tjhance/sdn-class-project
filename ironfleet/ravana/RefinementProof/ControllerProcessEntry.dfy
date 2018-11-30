include "../Types.i.dfy"
include "../Refinement.i.dfy"
include "../Service.i.dfy"
include "../DistributedSystem.i.dfy"
include "../RefinementLemmas.i.dfy"

module Refinement_Proof_ControllerProcessEntry {
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
    && rs.environment.nextStep.actor in rs.controllers
    && rs.environment.nextStep.actor in rs'.controllers
    && Node_ControllerProcessEntry(
                rs.controllers[rs.environment.nextStep.actor],
                rs'.controllers[rs.environment.nextStep.actor],
                rs.environment.nextStep.ios)
    && rs.switches == rs'.switches
    && rs.logger == rs'.logger
    && rs'.controllers == rs.controllers[
        rs.environment.nextStep.actor := rs'.controllers[rs.environment.nextStep.actor]]
  }

  lemma lemma_refines_ControllerProcessEntry(rs: RState, rs': RState)
  requires conditions(rs, rs')
  ensures rstate_valid(rs')
  ensures refinement(rs) == refinement(rs')
  {
    lemma_packets_are_valid(rs, rs');

    lemma_controllers_recved_events_valid_if_recved_events_unchanged(rs, rs');
    lemma_controllers_log_valid_if_log_copy_unchanged(rs, rs');

    lemma_controllers_state_correct(rs, rs');

    assert refinement_switchStates(rs.switches)
        == refinement_switchStates(rs'.switches);

    assert refinement_controllerState(rs.logger.log, rs.initControllerState)
        == refinement_controllerState(rs'.logger.log, rs'.initControllerState);

    assert refinement_outstandingCommands(rs.logger.log, rs.initControllerState, rs.switches)
        == refinement_outstandingCommands(rs'.logger.log, rs'.initControllerState, rs'.switches);

    assert refinement_outstandingEvents(rs.switches, rs.logger.log)
        == refinement_outstandingEvents(rs'.switches, rs'.logger.log);
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

  lemma lemma_controllers_state_correct(rs: RState, rs': RState)
  requires conditions(rs, rs')
  ensures controllers_state_correct(
        rs'.initControllerState, rs'.controllers,
        rs'.switches)
  {
    reveal_controllers_state_correct();

    forall ep | ep in rs.controllers
    ensures controller_state_correct(rs'.initControllerState,
        rs'.controllers[ep], rs'.switches)
    {
      if (ep == rs.environment.nextStep.actor) {
        lemma_actor_state_correct(rs, rs');
        assert controller_state_correct(rs'.initControllerState,
            rs'.controllers[ep], rs'.switches);
      } else {
        assert rs'.controllers[ep] == rs.controllers[ep];
        assert controller_state_correct(rs'.initControllerState,
            rs'.controllers[ep], rs'.switches);
      }
    }
  }

  lemma lemma_actor_state_correct(rs: RState, rs': RState)
  requires conditions(rs, rs')
  requires controller_state_correct(
      rs.initControllerState,
      rs.controllers[rs.environment.nextStep.actor],
      rs.switches)
  ensures controller_state_correct(
      rs'.initControllerState,
      rs'.controllers[rs.environment.nextStep.actor],
      rs'.switches)
  {
    var s' := rs'.controllers[rs.environment.nextStep.actor];

    lemma_controllerState_correct(rs, rs', s');

    forall xid | xid in s'.buffered_commands
    ensures
      buffered_commands_correct(rs'.initControllerState, xid,
          s'.log_copy,
          s'.buffered_commands[xid],
          rs'.switches);
    {
      lemma_buffered_commands_correct(rs, rs', xid, s');
    }
  }

  lemma lemma_controllerState_correct(rs: RState, rs': RState, s': NodeController)
  requires conditions(rs, rs')
  requires s' == rs'.controllers[rs.environment.nextStep.actor]
  requires controller_state_correct(
      rs.initControllerState,
      rs.controllers[rs.environment.nextStep.actor],
      rs.switches)
  ensures s'.controllerState ==
        controller_state_looking_forward(
          s'.log_copy[0 .. s'.idx], rs'.initControllerState).controllerState
  ensures s'.current_command_id ==
        |controller_state_looking_forward(s'.log_copy[0 .. s'.idx],
        rs'.initControllerState).commands|
  {
    var s := rs.controllers[rs.environment.nextStep.actor];
    var l := s.log_copy[s.idx];

    assert s'.idx == s.idx + 1;
    assert s'.idx >= 1;
    var s'_prefix := s'.log_copy[0 .. s'.idx];
    assert s'_prefix[0 .. |s'_prefix| - 1]
        == s'.log_copy[0 .. s'.idx][0 .. |s'.log_copy[0 .. s'.idx]| - 1]
        == s'.log_copy[0 .. |s'.log_copy[0 .. s'.idx]| - 1]
        == s'.log_copy[0 .. s'.idx - 1]
        == s.log_copy[0 .. s'.idx - 1]
        == s.log_copy[0 .. s.idx];

    assert s.controllerState
        == controller_state_looking_forward(
              s.log_copy[0 .. s.idx], rs'.initControllerState).controllerState
        == controller_state_looking_forward(
              s'_prefix[0 .. |s'_prefix| - 1], rs'.initControllerState).controllerState;

    if (l.LMRecv?) {
      if (s.leader) {
        assert s'.controllerState ==
              controller_state_looking_forward(
                s'.log_copy[0 .. s'.idx], rs'.initControllerState).controllerState;
      } else {
        assert s'.controllerState ==
              controller_state_looking_forward(
                s'.log_copy[0 .. s'.idx], rs'.initControllerState).controllerState;
      }
    } else {
      if (s.leader) {
        assert s'.controllerState ==
              controller_state_looking_forward(
                s'.log_copy[0 .. s'.idx], rs'.initControllerState).controllerState;
      } else {
        assert s'.controllerState ==
              controller_state_looking_forward(
                s'.log_copy[0 .. s'.idx], rs'.initControllerState).controllerState;
      }
    }
  }

  lemma
    lemma_buffered_commands_correct(rs: RState, rs': RState, xid: int, s': NodeController)
  requires conditions(rs, rs')
  requires s' == rs'.controllers[rs.environment.nextStep.actor]
  requires xid in s'.buffered_commands
  requires controller_state_correct(
      rs.initControllerState,
      rs.controllers[rs.environment.nextStep.actor],
      rs.switches)
  ensures buffered_commands_correct(rs'.initControllerState, xid,
          s'.log_copy,
          s'.buffered_commands[xid],
          rs'.switches);
  {
    var s := rs.controllers[rs.environment.nextStep.actor];
    var comms := s'.buffered_commands[xid];
    var command_id_base :=
        |controller_state_looking_forward(s'.log_copy[0 .. xid], rs'.initControllerState).commands|;
    var commands := controllerTransition(
      controller_state_looking_forward(s'.log_copy[0 .. xid], rs'.initControllerState).controllerState,
      s'.log_copy[xid].switch,
      s'.log_copy[xid].event).1;

    if (xid == s.idx) {
      lemma_all_commands_in_new_map_good(rs, rs', xid, s, s', comms,
          command_id_base, commands);
    } else {
      assert s'.buffered_commands[xid] == s.buffered_commands[xid];
      assert xid in s.buffered_commands;
      assert buffered_commands_correct(rs.initControllerState, xid,
              s.log_copy,
              s.buffered_commands[xid],
              rs.switches);
      assert buffered_commands_correct(rs'.initControllerState, xid,
              s'.log_copy,
              s'.buffered_commands[xid],
              rs'.switches);
    }
  }

  lemma lemma_all_commands_in_new_map_good(rs: RState, rs': RState,
      xid: int, s: NodeController, s': NodeController, comms: map<int, SingleCommand>,
      command_id_base: int, commands: seq<SingleCommand>)
  requires conditions(rs, rs')
  requires s == rs.controllers[rs.environment.nextStep.actor]
  requires s' == rs'.controllers[rs.environment.nextStep.actor]
  requires xid in s'.buffered_commands
  requires controller_state_correct(
      rs.initControllerState,
      rs.controllers[rs.environment.nextStep.actor],
      rs.switches)

  requires comms == s'.buffered_commands[xid]
  requires command_id_base ==
        |controller_state_looking_forward(s'.log_copy[0 .. xid], rs'.initControllerState).commands|

  requires commands == controllerTransition(
      controller_state_looking_forward(s'.log_copy[0 .. xid], rs'.initControllerState).controllerState,
      s'.log_copy[xid].switch,
      s'.log_copy[xid].event).1
  requires xid == s.idx

  ensures all_commands_in_map_good(comms, commands, command_id_base)
  {
    var l := s.log_copy[s.idx];
    if (l.LMRecv?) {
      if (s.leader) {
        forall command_id | command_id in comms
        ensures command_id_base <= command_id < command_id_base + |commands|
        ensures commands[command_id - command_id_base] == comms[command_id]
        {
          assert command_id in 
            (map i : int
                  | s.current_command_id <= i < s.current_command_id + |commands|
                 :: commands[i - s.current_command_id]
            );
          assert s.current_command_id <= command_id < s.current_command_id + |commands|;
          assert command_id_base == s.current_command_id;
        }
        assert all_commands_in_map_good(comms, commands, command_id_base);
      } else {
        assert s'.buffered_commands[xid] == s.buffered_commands[xid];
      }
    } else {
      assert s'.buffered_commands[xid] == s.buffered_commands[xid];
    }
  }
}
