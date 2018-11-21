include "../Types.i.dfy"
include "../Refinement.i.dfy"
include "../Service.i.dfy"
include "../DistributedSystem.i.dfy"
include "../RefinementLemmas.i.dfy"

module Refinement_Proof_LogEvent_i {
  import opened Types_i
  import opened Refinement_i
  import opened Service_i
  import opened DistributedSystem_i
  import opened RefinementLemmas_i

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
    lemma_packets_are_valid_no_sending();

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

  lemma
  lemma_refines_LoggerLogEvent_multiset(rs: RState, rs': RState, log_entry: LogEntry)
  requires rstate_valid(rs)
  requires rstate_valid(rs')
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
  requires is_valid_LogMessage(rs,
      rs.environment.nextStep.ios[0].r.src,
      rs.environment.nextStep.ios[0].r.dst,
      rs.environment.nextStep.ios[0].r.msg)

  ensures multiset_adds_one(refinement(rs').outstandingEvents, refinement(rs).outstandingEvents);
  ensures SwitchEvent(log_entry.switch, log_entry.event)
          == added_obj(refinement(rs').outstandingEvents, refinement(rs).outstandingEvents)
  {
      lemma_refines_LoggerLogEvent_multiset_helper1(rs, rs', log_entry);
      lemma_refines_LoggerLogEvent_multiset_helper2(rs, rs', log_entry);

      lemma_refines_LoggerLogEvent_outstandingEvents(
          refinement_outstandingEventsSet(rs'.server_switches, rs'.server_logger.log),
          refinement_outstandingEventsSet(rs.server_switches, rs.server_logger.log),
          (log_entry.switch, log_entry.event_id),
          SwitchEvent(log_entry.switch, log_entry.event));
  }

  lemma
      lemma_refines_LoggerLogEvent_multiset_helper1
      (rs: RState, rs': RState, log_entry: LogEntry)
  requires rstate_valid(rs)
  requires rstate_valid(rs')
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
  requires is_valid_LogMessage(rs,
      rs.environment.nextStep.ios[0].r.src,
      rs.environment.nextStep.ios[0].r.dst,
      rs.environment.nextStep.ios[0].r.msg)
  ensures (set
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
      ) ==
      { ((log_entry.switch, log_entry.event_id),
             SwitchEvent(log_entry.switch, log_entry.event)) }
  {
    reveal_log_is_valid();

    assert rs'.server_logger.log == rs.server_logger.log + [log_entry];
    assert rs.server_switches == rs'.server_switches;

    assert log_entry.switch in rs.server_switches;
    assert log_entry.event_id in rs.server_switches[log_entry.switch].bufferedEvents;
    assert rs.server_switches[log_entry.switch].bufferedEvents[log_entry.event_id]
        == log_entry.event;

    assert log_is_valid(rs.server_switches, rs.server_logger.log);
    assert forall entry :: entry in rs.server_logger.log ==>
                    is_valid_log_entry(rs.server_switches, entry);

    forall entry | entry in rs.server_logger.log
      ensures !(entry.LMRecv? && entry.event_id == log_entry.event_id &&
                entry.switch == log_entry.switch);
    {
      assert is_valid_log_entry(rs.server_switches, entry);
    }

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

      assert (forall switch : EndPoint :: forall eid : int :: (
            switch in rs.server_switches &&
            eid in rs.server_switches[switch].bufferedEvents &&
            (forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
                !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
          ) ==> (
            switch in rs.server_switches &&
            eid in rs.server_switches[switch].bufferedEvents &&
            (forall entry :: entry in rs.server_logger.log ==>
                !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
          )
        );

      assert (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      ) >= (
      set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      );
      
      assert (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      )
      ==
      (
      set
        switch : EndPoint, eid : int | (
          switch in rs'.server_switches &&
          eid in rs'.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs'.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs'.server_switches[switch].bufferedEvents[eid]))
      );

  }

  lemma lemma_refines_LoggerLogEvent_multiset_helper2
      (rs: RState, rs': RState, log_entry: LogEntry)
  requires rstate_valid(rs)
  requires rstate_valid(rs')
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
  requires is_valid_LogMessage(rs,
      rs.environment.nextStep.ios[0].r.src,
      rs.environment.nextStep.ios[0].r.dst,
      rs.environment.nextStep.ios[0].r.msg)
  ensures (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      ) >= (
      set
        switch : EndPoint, eid : int | (
          switch in rs'.server_switches &&
          eid in rs'.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs'.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs'.server_switches[switch].bufferedEvents[eid]))
      )
  {
      assert (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      ) >= (
      set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      );
      
      assert (set
        switch : EndPoint, eid : int | (
          switch in rs.server_switches &&
          eid in rs.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in (rs.server_logger.log + [log_entry]) ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
      )
      ==
      (
      set
        switch : EndPoint, eid : int | (
          switch in rs'.server_switches &&
          eid in rs'.server_switches[switch].bufferedEvents &&
          (forall entry :: entry in rs'.server_logger.log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, rs'.server_switches[switch].bufferedEvents[eid]))
      );
  }

  lemma {:axiom} lemma_refines_LoggerLogEvent_outstandingEvents<A,B>
        (s : set<(A,B)>, s' : set<(A,B)>, key : A, t : B)
  requires s' >= s
  requires s' - s == {(key, t)}
  ensures multiset_adds_one(set_to_multiset(s), set_to_multiset(s'))
  ensures added_obj(set_to_multiset(s), set_to_multiset(s')) == t
  /*
  {
    if (|s| == 0) {
      assert set_to_multiset(s) == multiset{};
      assert set_to_multiset(s') == multiset{t};
      var y :| y in set_to_multiset(s') - set_to_multiset(s);
      assert y == added_obj(set_to_multiset(s), set_to_multiset(s'));
      assert set_to_multiset(s') - set_to_multiset(s) == multiset{t};
      assert y == t;
    } else {
      var y :| y in s;
      assert y in s';
      lemma_refines_LoggerLogEvent_outstandingEvents(s - {y}, s' - {y}, key, t);
      assert set_to_multiset(s) == set_to_multiset(s - {y}) + multiset{y.1};
      assert set_to_multiset(s') == set_to_multiset(s' - {y}) + multiset{y.1};

      assert |set_to_multiset(s') - set_to_multiset(s)| ==
              |(set_to_multiset(s' - {y}) + multiset{t}) - 
              (set_to_multiset(s - {y}) + multiset{t})|
          == |set_to_multiset(s' - {y}) - set_to_multiset(s - {y})|
          == 1;
      
      assert |set_to_multiset(s')| - |set_to_multiset(s)| ==
              |set_to_multiset(s' - {y}) + multiset{t}| - 
              |set_to_multiset(s - {y}) + multiset{t}|
        ==
              |set_to_multiset(s' - {y})| + |multiset{t}| - 
              (|set_to_multiset(s - {y})| + |multiset{t}|)
        ==
              |set_to_multiset(s' - {y})| - |set_to_multiset(s - {y})|
        == 1; 
      
      assert added_obj(set_to_multiset(s - {y}), set_to_multiset(s' - {y})) == t;

      assert t in ((set_to_multiset(s' - {y})) - set_to_multiset(s - {y}));

      assert set_to_multiset(s - {y}) == set_to_multiset(s) - multiset{y.1};
      assert set_to_multiset(s' - {y}) == set_to_multiset(s') - multiset{y.1};

      assert ((set_to_multiset(s' - {y})) - set_to_multiset(s - {y}))
        == (set_to_multiset(s') - multiset{y.1}) - (set_to_multiset(s) - multiset{y.1})
        == set_to_multiset(s') - set_to_multiset(s);

      assert t in set_to_multiset(s') - set_to_multiset(s);

      assert t in ((set_to_multiset(s')) - set_to_multiset(s));

      assert forall t' :: t' in (set_to_multiset(s') - set_to_multiset(s)) ==> t' == t;

      var z :| z in (set_to_multiset(s') - set_to_multiset(s));
      assert z == t;
      assert z == added_obj(set_to_multiset(s), set_to_multiset(s'));
    }
  }
  */

}
