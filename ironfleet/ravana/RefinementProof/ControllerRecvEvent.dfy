include "../Types.i.dfy"
include "../Refinement.i.dfy"
include "../Service.i.dfy"
include "../DistributedSystem.i.dfy"
include "../RefinementLemmas.i.dfy"

module Refinement_Proof_ControllerRecvEvent {
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
    && Node_ControllerRecvEvent(
                rs.controllers[rs.environment.nextStep.actor],
                rs'.controllers[rs.environment.nextStep.actor],
                rs.environment.nextStep.ios)
    && rs.switches == rs'.switches
    && rs.logger == rs'.logger
    && rs'.controllers == rs.controllers[
        rs.environment.nextStep.actor := rs'.controllers[rs.environment.nextStep.actor]]
  }

  lemma lemma_refines_ControllerRecvEvent(rs: RState, rs': RState)
  requires conditions(rs, rs')
  ensures rstate_valid(rs')
  ensures refinement(rs) == refinement(rs')
  {
    lemma_packets_are_valid(rs, rs');

    lemma_recved_events_valid(rs, rs');
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

  lemma lemma_recved_events_valid(rs: RState, rs': RState)
  requires conditions(rs, rs')
  ensures controllers_recved_events_valid(rs'.switches, rs'.controllers)
  {
    forall cn | cn in rs'.controllers
    ensures 
      forall sip :: sip in rs'.controllers[cn].recved_events ==>
        sip.switch in rs'.switches &&
        sip.event_id in rs'.switches[sip.switch].bufferedEvents &&
        rs'.switches[sip.switch].bufferedEvents[sip.event_id] == rs'.controllers[cn].recved_events[sip]
    {
      forall sip | sip in rs'.controllers[cn].recved_events
      ensures sip.switch in rs'.switches
      ensures sip.event_id in rs'.switches[sip.switch].bufferedEvents
      ensures rs'.switches[sip.switch].bufferedEvents[sip.event_id]
           == rs'.controllers[cn].recved_events[sip]
      {
        lemma_recved_event_valid(rs, rs', cn, sip);
        
      }
    }
    reveal_controllers_recved_events_valid();
  }

  lemma lemma_recved_event_valid(rs: RState, rs': RState, cn: EndPoint, sip: SwitchIdPair)
  requires conditions(rs, rs')
  requires cn in rs'.controllers
  requires sip in rs'.controllers[cn].recved_events
  ensures sip.switch in rs'.switches
  ensures sip.event_id in rs'.switches[sip.switch].bufferedEvents
  ensures rs'.switches[sip.switch].bufferedEvents[sip.event_id]
       == rs'.controllers[cn].recved_events[sip]
  {
    if (cn == rs.environment.nextStep.actor) {
      var recv_packet := rs.environment.nextStep.ios[0].r;
      if (sip == SwitchIdPair(recv_packet.src, recv_packet.msg.event_id)) {
        lemma_event_msg_is_valid(rs, rs');
        assert rs.environment.nextStep.ios[0].r.src == sip.switch;
        assert rs.environment.nextStep.ios[0].r.msg.event ==
            rs'.controllers[cn].recved_events[sip];
        assert rs.environment.nextStep.ios[0].r.msg.event_id == sip.event_id;
      } else {
        assert sip in rs.controllers[cn].recved_events;
        reveal_controllers_recved_events_valid();
        assert sip.switch in rs.switches;
        assert sip.event_id in rs.switches[sip.switch].bufferedEvents;
        assert rs.switches[sip.switch].bufferedEvents[sip.event_id]
             == rs.controllers[cn].recved_events[sip];
      }
    } else {
      reveal_controllers_recved_events_valid();
      assert sip.switch in rs.switches;
      assert sip.event_id in rs.switches[sip.switch].bufferedEvents;
      assert rs.switches[sip.switch].bufferedEvents[sip.event_id]
           == rs.controllers[cn].recved_events[sip];
    }
  }

  lemma lemma_event_msg_is_valid(rs: RState, rs': RState)
  requires conditions(rs, rs')
  ensures is_valid_EventMessage(rs,
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
