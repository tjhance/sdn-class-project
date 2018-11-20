include "Types.i.dfy"
include "Refinement.i.dfy"
include "Service.i.dfy"
include "DistributedSystem.i.dfy"

module Refinement_Proof_i {
  import opened Types_i
  import opened Refinement_i
  import opened Service_i
  import opened DistributedSystem_i

  /** MAIN LEMMA **/

  /*
  lemma rs_refines_ss(rs: RState, rs': RState)
  requires rstate_valid(rs)
  requires RS_Next(rs, rs')
  ensures rstate_valid(rs')
  ensures Service_Next(refinement(rs), refinement(rs'))
  {
  }
  */

  /*
  lemma lemma_refines_Logger_InitNewMaster(rs: RState, rs': RState)
  requires rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor == rs'.endpoint_logger
  requires Node_LoggerInitNewMaster(
              rs.server_logger, rs'.server_logger, rs.environment.nextStep.ios)
  requires rs.server_controllers == rs'.server_controllers
  requires rs.server_switches == rs'.server_switches

  ensures rstate_valid(rs')
  ensures refinement(rs) == refinement(rs')
  {
    assert refinement_switchStates(rs.server_switches)
        == refinement_switchStates(rs'.server_switches);

    assert rs.server_logger.log == rs'.server_logger.log;

    assert refinement_controllerState(rs.server_logger.log, rs.initControllerState)
        == refinement_controllerState(rs'.server_logger.log, rs'.initControllerState);

    assert refinement_outstandingCommands(rs.server_logger.log, rs.initControllerState, rs.server_switches)
        == refinement_outstandingCommands(rs'.server_logger.log, rs'.initControllerState, rs'.server_switches);

    assert refinement_outstandingEvents(rs.server_switches, rs.server_logger.log)
        == refinement_outstandingEvents(rs'.server_switches, rs'.server_logger.log);
  }

  lemma lemma_refines_Logger_InitNewMasterMsg(rs: RState, rs': RState)
  requires rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor == rs'.endpoint_logger
  requires Node_LoggerInitNewMasterMsg(
              rs.server_logger, rs'.server_logger, rs.environment.nextStep.ios)
  requires rs.server_controllers == rs'.server_controllers
  requires rs.server_switches == rs'.server_switches

  ensures rstate_valid(rs')
  ensures refinement(rs) == refinement(rs')
  {
    
  }

  lemma lemma_refines_LoggerLogEvent(rs: RState, rs': RState)
  requires rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor == rs'.endpoint_logger
  requires Node_LoggerLogEvent(
              rs.server_logger, rs'.server_logger, rs.environment.nextStep.ios)
  requires rs.server_controllers == rs'.server_controllers
  requires rs.server_switches == rs'.server_switches

  ensures rstate_valid(rs')
  ensures Service_NextApplyEvent(refinement(rs), refinement(rs'))
       || refinement(rs) == refinement(rs')
          
  {
    var s := refinement(rs);
    var s' := refinement(rs');

    assert rs.environment.nextStep.ios[0].LIoOpReceive?;
    assert rs.environment.nextStep.ios[0].r.msg.LogMessage?;
    var log_entry := rs.environment.nextStep.ios[0].r.msg.log_entry;

    if (log_entry.LMRecv?) {
      var switch_event := SwitchEvent(log_entry.switch, log_entry.event);

      assert s.switchStates == s'.switchStates;

      lemma_refines_LoggerLogEvent_multiset(rs, rs', log_entry);

      assert multiset_adds_one(s'.outstandingEvents, s.outstandingEvents);
      var event := added_obj(s'.outstandingEvents, s.outstandingEvents);
      assert event == switch_event;

      var cas := controllerTransition(s.controllerState, event.switch, event.event);
      var cs' := cas.0;
      var singleCommands := cas.1;

      assert s'.controllerState == cs';
      assert s'.outstandingCommands == s.outstandingCommands + seq_to_multiset(singleCommands);

      assert Service_NextApplyEvent(refinement(rs), refinement(rs'));
    } else {
      assert s == s';
    }
  }
  */

  lemma lemma_refines_LoggerLogEvent_multiset(rs: RState, rs': RState, log_entry: LogEntry)
  requires rstate_valid(rs)
  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor == rs'.endpoint_logger
  requires Node_LoggerLogEvent(
              rs.server_logger, rs'.server_logger, rs.environment.nextStep.ios)
  requires rs.server_controllers == rs'.server_controllers
  requires rs.server_switches == rs'.server_switches

  requires rs.environment.nextStep.ios[0].LIoOpReceive?;
  requires rs.environment.nextStep.ios[0].r.msg.LogMessage?;
  requires rs.environment.nextStep.ios[0].r.msg.log_entry == log_entry
  requires log_entry.LMRecv?

  ensures multiset_adds_one(refinement(rs').outstandingEvents, refinement(rs).outstandingEvents);
  ensures SwitchEvent(log_entry.switch, log_entry.event)
          == added_obj(refinement(rs').outstandingEvents, refinement(rs).outstandingEvents)
  {
    assert rs'.server_logger.log == rs.server_logger.log + [log_entry];
    assert rs.server_switches == rs'.server_switches;

    assert log_entry.switch in rs.server_switches;
    assert log_entry.event_id in rs.server_switches[log_entry.switch].bufferedEvents;
    assert rs.server_switches[log_entry.switch].bufferedEvents[log_entry.event_id]
        == log_entry.event;

    assert (forall entry :: entry in rs.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == log_entry.event_id &&
                  entry.switch == log_entry.switch));

    assert 
      (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      ) - (
      set
        switch : EndPoint, eid : int | (
          switch in rs'.server_switches &&
          eid in rs'.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs'.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs'.server_switches[switch].bufferedEvents[eid]))
      )
      ==
      (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      ) - (
      set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs'.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      )
      ==
      (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
          && !(
            switch in rs.server_switches &&
            eid in rs.server_switches[switch].bufferedEvents &&
            (forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
                !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
          )
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      )
      ==
      (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
          && !(
            (forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
                !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
          )
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      )
      ==
      (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
          && (log_entry.LMRecv? && log_entry.event_id == eid && log_entry.switch == switch)
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      )
      ==
      { ((log_entry.switch, log_entry.event_id),
             SwitchEvent(log_entry.switch,
             rs.server_switches[log_entry.switch].bufferedEvents[log_entry.event_id])) }
      ==
      { ((log_entry.switch, log_entry.event_id),
             SwitchEvent(log_entry.switch, log_entry.event)) }
      ;

  }

  /*
  lemma lemma_refines_LoggerBroadcast(rs: RState, rs': RState)
  requires rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor == rs'.endpoint_logger
  requires Node_LoggerBroadcast(
              rs.server_logger, rs'.server_logger, rs.environment.nextStep.ios)
  requires rs.server_controllers == rs'.server_controllers
  requires rs.server_switches == rs'.server_switches

  ensures rstate_valid(rs')
  ensures refinement(rs) == refinement(rs')
  {

  }
  */
}
