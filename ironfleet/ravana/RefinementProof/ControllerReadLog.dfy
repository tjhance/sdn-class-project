include "../Types.i.dfy"
include "../Refinement.i.dfy"
include "../Service.i.dfy"
include "../DistributedSystem.i.dfy"
include "../RefinementLemmas.i.dfy"

module Refinement_Proof_ControllerReadLog {
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
    && rs.environment.nextStep.actor in rs.server_controllers
    && rs.environment.nextStep.actor in rs'.server_controllers
    && Node_ControllerReadLog(
                rs.server_controllers[rs.environment.nextStep.actor],
                rs'.server_controllers[rs.environment.nextStep.actor],
                rs.environment.nextStep.ios)
    && rs.server_switches == rs'.server_switches
    && rs.server_logger == rs'.server_logger
    && rs'.server_controllers == rs.server_controllers[
        rs.environment.nextStep.actor := rs'.server_controllers[rs.environment.nextStep.actor]]
  }

  lemma lemma_refines_ControllerReadLog(rs: RState, rs': RState)
  requires conditions(rs, rs')
  ensures rstate_valid(rs')
  ensures refinement(rs) == refinement(rs')
  {
    lemma_packets_are_valid(rs, rs');

    lemma_controllers_recved_events_valid_if_recved_events_unchanged(rs, rs');
    lemma_controllers_log_valid(rs, rs');

    assert refinement_switchStates(rs.server_switches)
        == refinement_switchStates(rs'.server_switches);

    assert refinement_controllerState(rs.server_logger.log, rs.initControllerState)
        == refinement_controllerState(rs'.server_logger.log, rs'.initControllerState);

    assert refinement_outstandingCommands(rs.server_logger.log, rs.initControllerState, rs.server_switches)
        == refinement_outstandingCommands(rs'.server_logger.log, rs'.initControllerState, rs'.server_switches);

    assert refinement_outstandingEvents(rs.server_switches, rs.server_logger.log)
        == refinement_outstandingEvents(rs'.server_switches, rs'.server_logger.log);
  }

  lemma lemma_controllers_log_valid(rs: RState, rs': RState)
  requires conditions(rs, rs')
  ensures controllers_log_valid(rs'.server_logger.log, rs'.server_controllers)
  {
    reveal_controllers_log_valid();
    forall ep | ep in rs'.server_controllers
    {
      lemma_controller_log_valid(rs, rs', ep);
    }
  }

  lemma lemma_controller_log_valid(rs: RState, rs': RState, ep: EndPoint)
  requires conditions(rs, rs')
  requires ep in rs'.server_controllers
  ensures controller_log_valid(rs'.server_logger.log, rs'.server_controllers[ep])
  {
    if (ep == rs.environment.nextStep.actor) {
      lemma_log_msg_is_valid(rs, rs');
      if (|rs.environment.nextStep.ios[0].r.msg.full_log| >
          |rs.server_controllers[rs.environment.nextStep.actor].log_copy|) {
        assert is_prefix(rs.environment.nextStep.ios[0].r.msg.full_log, rs.server_logger.log);
        assert rs.environment.nextStep.ios[0].r.msg.full_log
            == rs'.server_controllers[rs.environment.nextStep.actor].log_copy
            == rs'.server_controllers[ep].log_copy;
        assert rs.server_logger.log == rs'.server_logger.log;
        assert is_prefix(rs'.server_controllers[ep].log_copy, rs'.server_logger.log);
        assert controller_log_valid(rs'.server_logger.log, rs'.server_controllers[ep]);
      } else {
        assert rs'.server_controllers[ep].log_copy ==
               rs.server_controllers[ep].log_copy;
        reveal_controllers_log_valid();
        assert is_prefix(rs.server_controllers[ep].log_copy, rs.server_logger.log);
        assert is_prefix(rs'.server_controllers[ep].log_copy, rs'.server_logger.log);
        assert controller_log_valid(rs'.server_logger.log, rs'.server_controllers[ep]);
      }
    } else {
      reveal_controllers_log_valid();
    }
  }

  lemma lemma_log_msg_is_valid(rs: RState, rs': RState)
  requires conditions(rs, rs')
  ensures is_valid_LogBroadcastMessage(rs,
      rs.environment.nextStep.ios[0].r.src,
      rs.environment.nextStep.ios[0].r.dst,
      rs.environment.nextStep.ios[0].r.msg)
  {
    reveal_packets_are_valid();
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
}
