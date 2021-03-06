include "../Types.i.dfy"
include "../Refinement.i.dfy"
include "../Service.i.dfy"
include "../DistributedSystem.i.dfy"
include "../RefinementLemmas.i.dfy"

module Refinement_Proof_SwitchEventSend {
  import opened Types_i
  import opened Refinement_i
  import opened Service_i
  import opened DistributedSystem_i
  import opened RefinementLemmas_i

  predicate conditions(rs: RState, rs': RState, event_id: int)
  {
    rstate_valid(rs)

    && LEnvironment_Next(rs.environment, rs'.environment)
    && rs.environment.nextStep.LEnvStepHostIos?
    && rs.endpoint_logger == rs'.endpoint_logger
    && rs.initControllerState == rs'.initControllerState
    && rs.environment.nextStep.actor in rs.switches
    && rs.environment.nextStep.actor in rs'.switches
    && Node_SwitchEventSend(
                rs.switches[rs.environment.nextStep.actor],
                rs'.switches[rs.environment.nextStep.actor],
                event_id,
                rs.environment.nextStep.ios)
    && rs.controllers == rs'.controllers
    && rs.logger == rs'.logger
    && rs'.switches == rs.switches[
        rs.environment.nextStep.actor := rs'.switches[rs.environment.nextStep.actor]]
  }

  lemma lemma_refines_SwitchEventSend(rs: RState, rs': RState, event_id: int)
  requires conditions(rs, rs', event_id)

  ensures rstate_valid(rs')
  ensures refinement(rs) == refinement(rs')
  {
    lemma_packets_are_valid(rs, rs', event_id);
    lemma_log_is_valid(rs, rs', event_id);
    lemma_accepted_commands_are_valid(rs, rs', event_id);
    lemma_switches_valid(rs, rs', event_id);

    lemma_controller_recved_events_valid_for_switch_change(rs, rs');
    lemma_controllers_state_correct_for_switch_change(rs, rs');

    lemma_refinement_switchStates_eq(rs, rs', event_id);

    assert refinement_switchStates(rs.switches)
        == refinement_switchStates(rs'.switches);

    assert refinement_controllerState(rs.logger.log, rs.initControllerState)
        == refinement_controllerState(rs'.logger.log, rs'.initControllerState);

    lemma_outstanding_commands_eq(rs, rs');
    assert refinement_outstandingCommands(rs.logger.log, rs.initControllerState, rs.switches)
        == refinement_outstandingCommands(rs'.logger.log, rs'.initControllerState, rs'.switches);

    lemma_outstanding_events_eq(rs, rs');
    assert refinement_outstandingEvents(rs.switches, rs.logger.log)
        == refinement_outstandingEvents(rs'.switches, rs'.logger.log);
  }

  lemma lemma_packets_are_valid(rs: RState, rs': RState, event_id: int)
  requires conditions(rs, rs', event_id)
  ensures packets_are_valid(rs')
  {
    packet_validation_preservation(rs, rs', event_id);
    lemma_packets_are_valid_sending_1(rs, rs');
  }

  lemma packet_validation_preservation(rs: RState, rs': RState, event_id: int)
  requires conditions(rs, rs', event_id)
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

  lemma lemma_log_is_valid(rs: RState, rs': RState, event_id: int)
  requires conditions(rs, rs', event_id)
  ensures log_is_valid(rs'.switches, rs'.logger.log)
  {
    reveal_log_is_valid();
  }

  lemma lemma_accepted_commands_are_valid(rs: RState, rs': RState, event_id: int)
  requires conditions(rs, rs', event_id)
  ensures accepted_commands_are_valid(rs'.initControllerState,
        rs'.switches, rs'.logger.log)
  {
    reveal_accepted_commands_are_valid();
  }

  lemma lemma_switches_valid(rs: RState, rs': RState, event_id: int)
  requires conditions(rs, rs', event_id)
  ensures switches_valid(rs'.switches)
  {
    reveal_switches_valid();
  }

  lemma lemma_refinement_switchStates_eq(rs: RState, rs': RState, event_id: int)
  requires conditions(rs, rs', event_id)
  ensures refinement_switchStates(rs.switches)
       == refinement_switchStates(rs'.switches);
  {
  }
}
