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
    && rs.server_logger == rs'.server_logger
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

    assert refinement_controllerState(rs.server_logger.log, rs.initControllerState)
        == refinement_controllerState(rs'.server_logger.log, rs'.initControllerState);

    assert refinement_outstandingCommands(rs.server_logger.log, rs.initControllerState, rs.switches)
        == refinement_outstandingCommands(rs'.server_logger.log, rs'.initControllerState, rs'.switches);

    assert refinement_outstandingEvents(rs.switches, rs.server_logger.log)
        == refinement_outstandingEvents(rs'.switches, rs'.server_logger.log);
  }

  lemma {:axiom} lemma_packets_are_valid(rs: RState, rs': RState)
  requires conditions(rs, rs')
  ensures packets_are_valid(rs')
  /*
  {
    packet_validation_preservation(rs, rs');
    lemma_packets_are_valid_no_sending(rs, rs');
  }
  */

  lemma {:axiom} packet_validation_preservation(rs: RState, rs': RState)
  requires conditions(rs, rs')
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
  ensures controller_state_correct(
      rs'.initControllerState,
      rs'.controllers[rs.environment.nextStep.actor],
      rs'.switches)
    lemma_controllerState_correct(rs, rs');

    forall xid | xid in s.buffered_commands
    ensures
      buffered_commands_correct(rs'.initControllerState, xid,
          rs'.switches[
          .log_copy, s.buffered_commands[xid], switches)
    {
      lemma_buffered_commands_correct(rs, rs');
    }
  {
  }
}
