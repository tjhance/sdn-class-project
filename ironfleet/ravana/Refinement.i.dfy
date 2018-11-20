include "Types.i.dfy"

module Refinement_i {
  import opened Types_i

  predicate rstate_valid(rs: RState) {
    packets_are_valid(rs)
  }

  function refinement(rs: RState) : ServiceState
  requires rstate_valid(rs)
  {
    ServiceState(
      refinement_switchStates(rs.server_switches),
      refinement_controllerState(rs.server_logger.log, rs.initControllerState),
      refinement_outstandingCommands(rs.server_logger.log, rs.initControllerState,
          rs.server_switches),
      refinement_outstandingEvents(rs.server_switches, rs.server_logger.log)
    )
  }

  function refinement_switchStates(
      server_switches: map<EndPoint, NodeSwitch>) : map<EndPoint, SwitchState>
  {
      map switch : EndPoint
      | switch in server_switches
      :: server_switches[switch].switchState
  }

  function refinement_outstandingEvents(
      server_switches: map<EndPoint, NodeSwitch>,
      log: seq<LogEntry>
      ) : multiset<SwitchEvent>
  {
      set_to_multiset(set
        switch : EndPoint, eid : int | (
          switch in server_switches &&
          eid in server_switches[switch].bufferedEvents &&
          (forall entry :: entry in log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, server_switches[switch].bufferedEvents[eid]))
      )
  }

  function refinement_controllerState(
      log: seq<LogEntry>, initControllerState: ControllerState) : ControllerState
  { 
      controller_state_looking_forward(log, initControllerState).controllerState
  }

  function refinement_outstandingCommands(
      log: seq<LogEntry>, initControllerState: ControllerState,
      server_switches: map<EndPoint, NodeSwitch>) : multiset<SingleCommand>
  {
      var fwdOutstandingCommands := 
          controller_state_looking_forward(log, initControllerState).commands;
      set_to_multiset(set
        command_id : int | (
          0 <= command_id < |fwdOutstandingCommands| &&
          var command := fwdOutstandingCommands[command_id];
          command.switch in server_switches &&
          !(command_id in server_switches[command.switch].received_command_ids)
        ) ::
          (command_id, fwdOutstandingCommands[command_id])
      )
  }

  datatype StateAndCommands = StateAndCommands(
      controllerState: ControllerState,
      commands: seq<SingleCommand>)

  function controller_state_looking_forward(
      log: seq<LogEntry>,
      controllerState: ControllerState) : StateAndCommands
  {
    if |log| == 0 then
      StateAndCommands(controllerState, [])
    else (
      var elem := log[|log| - 1];
      if elem.LMProc? then (
        controller_state_looking_forward(log[0 .. |log| - 1], controllerState)
      ) else (
        var sac1 := controller_state_looking_forward(log[0 .. |log| - 1], controllerState);
        var (cs'', commands) := controllerTransition(sac1.controllerState, elem.switch, elem.event);
        StateAndCommands(cs'', sac1.commands + commands)
      )
    )
  }

  function set_to_multiset<A, B>(m: set<(A, B)>) : multiset<B>
  {
    if |m| == 0 then
      multiset{}
    else (
      var y :| y in m;
      var (a, b) := y;
      var m' := m - {y};
      set_to_multiset(m') + multiset{b}
    )
  }

  predicate {:opaque} packets_are_valid(rs: RState)
  {
    (forall p :: p in rs.environment.sentPackets ==>
        is_valid_message(rs, p.src, p.dst, p.msg))
  }

  predicate is_valid_message(rs: RState, src: EndPoint, dst: EndPoint, msg: RavanaMessage)
  {
    (msg.EventMessage? ==> is_valid_EventMessage(rs, src, dst, msg)) &&
    (msg.EventAck? ==> is_valid_EventAck(rs, src, dst, msg)) &&
    (msg.CommandMessage? ==> is_valid_CommandMessage(rs, src, dst, msg)) &&
    (msg.CommandAck? ==> is_valid_CommandAck(rs, src, dst, msg)) &&
    (msg.InitNewMaster? ==> is_valid_InitNewMaster(rs, src, dst, msg)) &&
    (msg.NewMaster? ==> is_valid_NewMaster(rs, src, dst, msg)) &&
    (msg.NewMasterAck? ==> is_valid_NewMasterAck(rs, src, dst, msg)) &&
    (msg.LogMessage? ==> is_valid_LogMessage(rs, src, dst, msg)) &&
    (msg.LogBroadcastMessage? ==> is_valid_LogBroadcastMessage(rs, src, dst, msg))
  }

  predicate is_valid_EventMessage(rs: RState, src: EndPoint, dst: EndPoint, msg: RavanaMessage)
  requires msg.EventMessage?
  {
    true
  }

  predicate is_valid_EventAck(rs: RState, src: EndPoint, dst: EndPoint, msg: RavanaMessage)
  requires msg.EventAck?
  {
    true
  }

  predicate is_valid_CommandMessage(rs: RState, src: EndPoint, dst: EndPoint, msg: RavanaMessage)
  requires msg.CommandMessage?
  {
    true
  }

  predicate is_valid_CommandAck(rs: RState, src: EndPoint, dst: EndPoint, msg: RavanaMessage)
  requires msg.CommandAck?
  {
    true
  }

  predicate is_valid_InitNewMaster(rs: RState, src: EndPoint, dst: EndPoint, msg: RavanaMessage)
  requires msg.InitNewMaster?
  {
    true
  }

  predicate is_valid_NewMaster(rs: RState, src: EndPoint, dst: EndPoint, msg: RavanaMessage)
  requires msg.NewMaster?
  {
    true
  }

  predicate is_valid_NewMasterAck(rs: RState, src: EndPoint, dst: EndPoint, msg: RavanaMessage)
  requires msg.NewMasterAck?
  {
    true
  }

  predicate is_valid_LogMessage(rs: RState, src: EndPoint, dst: EndPoint, msg: RavanaMessage)
  requires msg.LogMessage?
  {
    if (msg.log_entry.LMRecv?) then (
      // LMRecv
         msg.log_entry.switch in rs.server_switches
      && msg.log_entry.event_id in rs.server_switches[msg.log_entry.switch].bufferedEvents
      && rs.server_switches[msg.log_entry.switch].bufferedEvents[msg.log_entry.event_id] ==
            msg.log_entry.event
    ) else (
      // LMProc
      true
    )
  }

  predicate is_valid_LogBroadcastMessage(rs: RState, src: EndPoint, dst: EndPoint, msg: RavanaMessage)
  requires msg.LogBroadcastMessage?
  {
    true
  }
}
