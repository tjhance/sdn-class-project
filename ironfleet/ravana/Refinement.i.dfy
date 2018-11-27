include "Types.i.dfy"
include "Collections.dfy"

module Refinement_i {
  import opened Types_i
  import opened Collections

  predicate rstate_valid(rs: RState) {
    packets_are_valid(rs)
    && log_is_valid(rs.server_switches, rs.server_logger.log)
    && accepted_commands_are_valid(rs.initControllerState,
        rs.server_switches, rs.server_logger.log)
    && switches_valid(rs.server_switches)
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
      set_to_multiset(refinement_outstandingEventsSet(server_switches, log))
  }

  function refinement_outstandingEventsSet(
      server_switches: map<EndPoint, NodeSwitch>,
      log: seq<LogEntry>
      ) : set<((EndPoint, int), SwitchEvent)>
  {
    set
        switch : EndPoint, eid : int | (
          switch in server_switches &&
          eid in server_switches[switch].bufferedEvents &&
          (forall entry :: entry in log ==>
              !(entry.LMRecv? && entry.event_id == eid && entry.switch == switch))
        ) ::
          ((switch, eid), SwitchEvent(switch, server_switches[switch].bufferedEvents[eid]))
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
      filter_out_accepted_commands(fwdOutstandingCommands, server_switches)
  }

  function filter_out_accepted_commands(
      commands: seq<SingleCommand>,
      server_switches: map<EndPoint, NodeSwitch>) : multiset<SingleCommand>
  {
    if (|commands| == 0) then (
      multiset{}
    ) else (
      var command := commands[|commands| - 1];
      filter_out_accepted_commands(commands[0 .. |commands| - 1], server_switches) + (
        if !(
            command.switch in server_switches &&
            (|commands| - 1) in server_switches[command.switch].received_command_ids)
        then multiset{command} else multiset{}
      )
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

  predicate {:opaque} packets_are_valid(rs: RState)
  {
    forall p :: p in rs.environment.sentPackets ==>
        is_valid_message(rs, p.src, p.dst, p.msg)
  }

  predicate {:opaque} log_is_valid(switches: map<EndPoint, NodeSwitch>, log: seq<LogEntry>)
  {
    forall entry :: entry in log ==> is_valid_log_entry(switches, entry)
  }

  predicate {:opaque} accepted_commands_are_valid(
      initControllerState: ControllerState,
      switches: map<EndPoint, NodeSwitch>, log: seq<LogEntry>)
  {
    var all_commands := controller_state_looking_forward(
                log, initControllerState).commands;

    forall ep :: ep in switches ==>
      forall command_id :: command_id in switches[ep].received_command_ids ==>
        0 <= command_id < |all_commands| &&
        all_commands[command_id].switch == ep
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
    is_valid_log_entry(rs.server_switches, msg.log_entry)
  }

  predicate is_valid_log_entry(switches: map<EndPoint, NodeSwitch>, entry: LogEntry)
  {
    if (entry.LMRecv?) then (
      // LMRecv
         entry.switch in switches
      && entry.event_id in switches[entry.switch].bufferedEvents
      && switches[entry.switch].bufferedEvents[entry.event_id] == entry.event
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

  predicate {:opaque} switches_valid(switches: map<EndPoint, NodeSwitch>)
  {
    forall ep :: ep in switches ==> switch_valid(switches[ep])
  }

  predicate switch_valid(switch: NodeSwitch)
  {
    (forall event_id :: event_id in switch.bufferedEvents ==> event_id < switch.event_id)
  }
}
