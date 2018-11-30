include "../Types.i.dfy"
include "../Refinement.i.dfy"
include "../Service.i.dfy"
include "../DistributedSystem.i.dfy"
include "../RefinementLemmas.i.dfy"

module Refinement_Proof_ControllerSendCommand {
  import opened Types_i
  import opened Refinement_i
  import opened Service_i
  import opened DistributedSystem_i
  import opened RefinementLemmas_i

  predicate conditions(rs: RState, rs': RState, xid: int, command_id: int)
  {
    rstate_valid(rs)

    && LEnvironment_Next(rs.environment, rs'.environment)
    && rs.environment.nextStep.LEnvStepHostIos?
    && rs.endpoint_logger == rs'.endpoint_logger
    && rs.initControllerState == rs'.initControllerState
    && rs.environment.nextStep.actor in rs.controllers
    && rs.environment.nextStep.actor in rs'.controllers
    && Node_ControllerSendCommand(
                rs.controllers[rs.environment.nextStep.actor],
                rs'.controllers[rs.environment.nextStep.actor],
                xid,
                command_id,
                rs.environment.nextStep.ios)
    && rs.switches == rs'.switches
    && rs.logger == rs'.logger
    && rs'.controllers == rs.controllers[
        rs.environment.nextStep.actor := rs'.controllers[rs.environment.nextStep.actor]]
  }

  lemma lemma_refines_ControllerSendCommand(rs: RState, rs': RState, xid: int, command_id: int)
  requires conditions(rs, rs', xid, command_id)
  ensures rstate_valid(rs')
  ensures refinement(rs) == refinement(rs')
  {
    lemma_packets_are_valid(rs, rs', xid, command_id);

    lemma_controllers_recved_events_valid_if_recved_events_unchanged(rs, rs');
    lemma_controllers_log_valid_if_log_copy_unchanged(rs, rs');
    lemma_controllers_state_correct_if_controller_stuff_unchanged(rs, rs');

    assert refinement_switchStates(rs.switches)
        == refinement_switchStates(rs'.switches);

    assert refinement_controllerState(rs.logger.log, rs.initControllerState)
        == refinement_controllerState(rs'.logger.log, rs'.initControllerState);

    assert refinement_outstandingCommands(rs.logger.log, rs.initControllerState, rs.switches)
        == refinement_outstandingCommands(rs'.logger.log, rs'.initControllerState, rs'.switches);

    assert refinement_outstandingEvents(rs.switches, rs.logger.log)
        == refinement_outstandingEvents(rs'.switches, rs'.logger.log);
  }

  lemma lemma_packets_are_valid(rs: RState, rs': RState, xid: int, command_id: int)
  requires conditions(rs, rs', xid, command_id)
  ensures packets_are_valid(rs')
  {
    lemma_new_packet_valid(rs, rs', xid, command_id);
    packet_validation_preservation(rs, rs', xid, command_id);
    lemma_packets_are_valid_sending_1(rs, rs');
  }

  lemma lemma_new_packet_valid(rs: RState, rs': RState, xid: int, command_id: int)
  requires conditions(rs, rs', xid, command_id)
  ensures is_valid_CommandMessage(rs', 
      rs.environment.nextStep.ios[0].s.src,
      rs.environment.nextStep.ios[0].s.dst,
      rs.environment.nextStep.ios[0].s.msg)
  {
  }

  lemma packet_validation_preservation(rs: RState, rs': RState, xid: int, command_id: int)
  requires conditions(rs, rs', xid, command_id)
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
}
