include "../Types.i.dfy"
include "../Refinement.i.dfy"
include "../Service.i.dfy"
include "../DistributedSystem.i.dfy"
include "../RefinementLemmas.i.dfy"

module Refinement_Proof_LoggerBroadcast {
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
    && rs.environment.nextStep.actor == rs'.endpoint_logger
    && Node_LoggerBroadcast(
                rs.server_logger, rs'.server_logger, rs.environment.nextStep.ios)
    && rs.server_controllers == rs'.server_controllers
    && rs.server_switches == rs'.server_switches
  }

  lemma lemma_refines_LoggerBroadcast(rs: RState, rs': RState)
  requires conditions(rs, rs')

  ensures rstate_valid(rs')
  ensures refinement(rs) == refinement(rs')
  {
    lemma_packets_are_valid(rs, rs');
  }

  lemma lemma_packets_are_valid(rs: RState, rs': RState)
  requires conditions(rs, rs')
  ensures packets_are_valid(rs')
  {
    var packet := rs.environment.nextStep.ios[0].s;
    assert is_valid_message(rs', packet.src, packet.dst, packet.msg);

    packet_validation_preservation(rs, rs');
    lemma_packets_are_valid_sending_1(rs, rs');
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
}
