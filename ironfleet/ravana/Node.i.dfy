include "Types.i.dfy"

module Protocol_Node_i {
  import opened Types_i

  datatype Config = Config(
      node_logger: EndPoint,
      node_controllers: seq<EndPoint>,
      node_switches: seq<EndPoint>
    )

  datatype Node =
      NodeLogger(
          log: seq<LogEntry>,
          clients: seq<EndPoint>
      )
    | NodeController(
          leader: bool,
          controllerState: ControllerState,
          config: Config,

          recved_events: map<SwitchIdPair, Event>,

          log_copy: seq<LogEntry>,
          idx: int,

          buffered_commands: map<int /* xid */, map<int /* command id */, SingleCommand>>,
          current_command_id: int
      )
    | NodeSwitch(
          bufferedEvents: seq<Event>,
          switchState: SwitchState,
          event_id: int,
          master: EndPoint,
          received_command_ids: seq<int>
      )

  predicate NodeInit(node: Node, my_index: int, config: Config) {
    (
      node.NodeLogger? &&
        node.log == [] &&
        node.clients == config.node_controllers
    ) || (
      node.NodeController? &&
        node.leader == (my_index == 0) &&
        controllerStateInit(node.controllerState) &&
        node.config == config &&
        node.recved_events == map[] &&
        node.log_copy == [] &&
        node.current_command_id == 0 &&
        node.idx == 0
    ) || (
      node.NodeSwitch? &&
        node.bufferedEvents == [] &&
        switchStateInit(node.switchState) &&
        node.event_id == 0 &&
        |config.node_controllers| >= 1 &&
        node.master == config.node_controllers[0]
    )
  }

  predicate Node_SwitchEvent(s: Node, s': Node, event: Event, ios: seq<RavanaIo>) {
    s.NodeSwitch? &&
      s' == s.
          (bufferedEvents := s.bufferedEvents + [event]).
          (event_id := s.event_id + 1) &&
      |ios| == 1 && ios[0].LIoOpSend? &&

      var packet := ios[0].s;
          packet.msg == EventMessage(event, s.event_id)
       && packet.dst == s.master
  }

  // TODO I think we want to combine these two:

  predicate Node_ControllerRecvEvent(s: Node, s': Node, ios: seq<RavanaIo>) {
    s.NodeController? &&
    s.leader &&

    |ios| == 1 &&
    ios[0].LIoOpReceive? &&
    var recv_packet := ios[0].r;

    recv_packet.msg.EventMessage? &&

    s' == s.(recved_events := s.recved_events[
        SwitchIdPair(recv_packet.src, recv_packet.msg.event_id) := recv_packet.msg.event])
  }

  predicate Node_ControllerLogEvent(s: Node, s': Node, p: SwitchIdPair, ios: seq<RavanaIo>) {
    s.NodeController? &&
    s.leader &&

    p in s.recved_events &&

    |ios| == 1 &&
    ios[0].LIoOpSend? &&
    var send_packet := ios[0].s;
    send_packet.dst == s.config.node_logger &&
    send_packet.msg == LogMessage(LMRecv(p.switch, s.recved_events[p], p.event_id))
  }

  predicate Node_LoggerLogEvent(s: Node, s': Node, ios: seq<RavanaIo>) {
    s.NodeLogger? &&

    |ios| == 1 &&
    ios[0].LIoOpReceive? &&
    var recv_packet := ios[0].r;
    recv_packet.msg.LogMessage? &&

    s' == s.(log := s.log + [recv_packet.msg.log_entry])
  }

  predicate Node_LoggerBroadcast(s: Node, s': Node, ios: seq<RavanaIo>) {
    s.NodeLogger? &&
    s' == s &&

    |ios| == |s.clients| &&
    forall i :: 0 <= i < |s.clients| ==>
        ios[i].LIoOpSend? &&
        ios[i].s.dst == s.clients[i] &&
        ios[i].s.msg == LogBroadcastMessage(s.log)
  }

  predicate Node_ControllerReadLog(s: Node, s': Node, ios: seq<RavanaIo>) {
    s.NodeController? &&
    |ios| == 1 &&
    ios[0].LIoOpReceive? &&
    var recv_packet := ios[0].r;
    recv_packet.src == s.config.node_logger &&
    recv_packet.msg.LogBroadcastMessage? &&
    var new_log_copy := recv_packet.msg.full_log;
    s' == s.(log_copy :=
        if |new_log_copy| > |s.log_copy| then new_log_copy else s.log_copy)
  }

  predicate Node_ControllerProcessEntry(s: Node, s': Node, ios: seq<RavanaIo>) {
    // TODO there should be something that checks if it's the leader, here
    // TODO should send EventAck to the client
    s.NodeController? &&
    0 <= s.idx < |s.log_copy| &&
    ios == [] &&
    var l := s.log_copy[s.idx];
    (
      l.LMRecv? &&
      var (new_state, commands) := controllerTransition(s.controllerState, l.switch, l.event);
      (
        // Leader: prepare commands to send to switches
        s.leader &&
        var new_bc :=
            map i : int
                  | s.current_command_id <= i < s.current_command_id + |commands|
                 :: commands[i - s.current_command_id];
        s' == s.
            (idx := s.idx + 1).
            (current_command_id := s.current_command_id + |commands|).
            (controllerState := new_state).
            (buffered_commands := s.buffered_commands[s.idx := new_bc])
      ) || (
        // Slave: 
        !s.leader &&
        (exists j : int :: 0 <= j < |s.log_copy| && s.log_copy[j] == LMProc(s.idx)) &&
        s' == s.
            (idx := s.idx + 1).
            (controllerState := new_state).
            (current_command_id := s.current_command_id + |commands|)
      )
    ) || (
      l.LMProc? &&
      s' == s.(idx := s.idx + 1)
    )
  }

  predicate Node_ControllerSendCommand(
      s: Node, s': Node, xid: int, command_id: int, ios: seq<RavanaIo>) {
    s.NodeController? &&
    s.leader &&
    xid in s.buffered_commands &&
    command_id in s.buffered_commands[xid] &&
    var comm := s.buffered_commands[xid][command_id];
    |ios| == 1 &&
    ios[0].LIoOpSend? &&
    var send_packet := ios[0].s;
    send_packet.dst == comm.switch &&
    send_packet.msg == CommandMessage(comm.command, command_id)
  }

  predicate Node_SwitchRecvCommand(
      s: Node, s': Node, ios: seq<RavanaIo>) {
    s.NodeSwitch? &&
    |ios| >= 1 &&
    ios[0].LIoOpReceive? &&
    var recv_packet := ios[0].r;
    recv_packet.msg.CommandMessage? &&
    var command := recv_packet.msg.command;
    var command_id := recv_packet.msg.command_id;
    (
      // not from the master: just ignore it
      recv_packet.src != s.master &&
      |ios| == 1 &&
      s' == s
    ) ||
    (
      // from the master
      recv_packet.src == s.master &&

      // send an ACK in any case
      |ios| == 2 &&
      ios[1].LIoOpSend? &&
      var send_packet := ios[1].s;
      send_packet.msg == CommandAck(command_id) &&

      ((
        // already got this one, don't do anything else
        (command_id in s.received_command_ids) &&
        s' == s
      ) || (
        // apply to state, save the command_id
        !(command_id in s.received_command_ids) &&
        s' == s.(received_command_ids := s.received_command_ids + [command_id])
               .(switchState := switchTransition(s.switchState, command))
      ))
    )
  }
}