include "Types.i.dfy"

module Protocol_Node_i {
  import opened Types_i

  predicate NodeInit_Logger(node: NodeLogger, config: Config)
  {
      node.log == [] &&
      node.clients == config.node_controllers &&
      |config.node_controllers| >= 1 &&
      node.master_log == [config.node_controllers[0]]
  }

  predicate NodeInit_Controller(node: NodeController, my_index: int, config: Config)
  {
      node.leader == (my_index == 0) &&
      node.is_next_leader == (my_index == 0) &&
      controllerStateInit(node.controllerState) &&
      node.config == config &&
      node.recved_events == map[] &&
      node.log_copy == [] &&
      node.current_command_id == 0 &&
      node.idx == 0 &&
      node.my_leader_id == (if my_index == 0 then 0 else -1)
  }

  predicate NodeInit_Switch(node: NodeSwitch, my_index: int, config: Config)
  {
      node.bufferedEvents == map[] &&
      switchStateInit(node.switchState) &&
      node.event_id == 0 &&
      |config.node_controllers| >= 1 &&
      node.master == config.node_controllers[0] &&
      node.master_id == 0
  }

  predicate NodeNext_Logger(s: NodeLogger, s': NodeLogger, ios: seq<RavanaIo>) {
    Node_LoggerLogEvent(s, s', ios) ||
    Node_LoggerBroadcast(s, s', ios) ||
    Node_LoggerInitNewMaster(s, s', ios) ||
    Node_LoggerInitNewMasterMsg(s, s', ios)
  }

  predicate NodeNext_Controller(s: NodeController, s': NodeController, ios: seq<RavanaIo>) {
    Node_ControllerRecvEvent(s, s', ios) ||
    (exists p :: Node_ControllerLogEvent(s, s', p, ios)) ||
    Node_ControllerReadLog(s, s', ios) ||
    Node_ControllerProcessEntry(s, s', ios) ||
    (exists xid :: exists command_id ::
        Node_ControllerSendCommand(s, s', xid, command_id, ios)) ||
    Node_ControllerRecvAck(s, s', ios) ||
    (exists xid :: Node_ControllerMarkEventComplete(s, s',xid, ios)) ||
    Node_ControllerNewMaster(s, s', ios) ||
    Node_ControllerSendNewMaster(s, s', ios) ||
    Node_ControllerRecvNewMasterAck(s, s', ios) ||
    Node_ControllerNewMasterFinish(s, s', ios)
  }

  predicate NodeNext_Switch(s: NodeSwitch, s': NodeSwitch, ios: seq<RavanaIo>) {
    (exists event :: Node_SwitchEvent(s, s', event, ios)) ||
    (exists event_id :: Node_SwitchEventSend(s, s', event_id, ios)) ||
    Node_SwitchRecvCommand(s, s', ios) ||
    Node_SwitchNewMaster(s, s', ios)
  }

  /*
   * Events
   */

  predicate Node_SwitchEvent(s: NodeSwitch, s': NodeSwitch, event: Event, ios: seq<RavanaIo>) {
      s' == s.
          (bufferedEvents := s.bufferedEvents[s.event_id := event]).
          (event_id := s.event_id + 1) &&
      |ios| == 0
  }

  predicate Node_SwitchEventSend(
          s: NodeSwitch, s': NodeSwitch,
          event_id: int, ios: seq<RavanaIo>) {
      |ios| == 1 && ios[0].LIoOpSend? &&
      event_id in s.bufferedEvents &&
      var event := s.bufferedEvents[event_id];
      var packet := ios[0].s;
          packet.msg == EventMessage(event, event_id)
       && packet.dst == s.master
  }

  // TODO I think we want to combine these two:

  predicate Node_ControllerRecvEvent(s: NodeController, s': NodeController, ios: seq<RavanaIo>) {
    s.leader &&

    |ios| == 1 &&
    ios[0].LIoOpReceive? &&
    var recv_packet := ios[0].r;

    recv_packet.msg.EventMessage? &&

    s' == s.(recved_events := s.recved_events[
        SwitchIdPair(recv_packet.src, recv_packet.msg.event_id) := recv_packet.msg.event])
  }

  predicate Node_ControllerLogEvent(s: NodeController, s': NodeController, p: SwitchIdPair, ios: seq<RavanaIo>) {
    s.leader &&

    p in s.recved_events &&

    |ios| == 1 &&
    ios[0].LIoOpSend? &&
    var send_packet := ios[0].s;
    send_packet.dst == s.config.node_logger &&
    send_packet.msg == LogMessage(LMRecv(p.switch, s.recved_events[p], p.event_id))
  }

  predicate Node_LoggerLogEvent(s: NodeLogger, s': NodeLogger, ios: seq<RavanaIo>) {
    |ios| == 1 &&
    ios[0].LIoOpReceive? &&
    var recv_packet := ios[0].r;
    recv_packet.msg.LogMessage? &&

    !(recv_packet.msg.log_entry in s.log) &&

    s' == s.(log := s.log + [recv_packet.msg.log_entry])
  }

  predicate Node_LoggerBroadcast(s: NodeLogger, s': NodeLogger, ios: seq<RavanaIo>) {
    s' == s &&

    |ios| == 1 &&

    ios[0].LIoOpSend? &&
    ios[0].s.dst in s.clients &&
    ios[0].s.msg == LogBroadcastMessage(s.log)
  }

  predicate Node_ControllerReadLog(s: NodeController, s': NodeController, ios: seq<RavanaIo>) {
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

  predicate Node_ControllerProcessEntry(s: NodeController, s': NodeController, ios: seq<RavanaIo>) {
    // TODO should send EventAck to the client
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
      (
        (
          s.leader &&
          s'.NodeController? &&
          var old_map := s.buffered_commands;
          var new_map := s'.buffered_commands;
          var xid := l.comp_id;
          !(xid in new_map) &&
          (xid in old_map) &&
          old_map == new_map[xid := old_map[xid]] &&
          s' == s.(buffered_commands := new_map)
        ) || (
          !s.leader &&
          s' == s.(idx := s.idx + 1)
        )
      )
    )
  }

  predicate Node_ControllerSendCommand(
      s: NodeController, s': NodeController, xid: int, command_id: int, ios: seq<RavanaIo>) {
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
      s: NodeSwitch, s': NodeSwitch, ios: seq<RavanaIo>) {
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

  predicate Node_ControllerRecvAck(
      s: NodeController, s': NodeController, ios: seq<RavanaIo>) {
    s.leader &&
    |ios| == 1 &&
    ios[0].LIoOpReceive? &&
    var recv_packet := ios[0].r;
    recv_packet.msg.CommandAck? &&
    var command_id := recv_packet.msg.command_ack_id;
    (
      (
        !s.leader && |ios| == 1 && s' == s
      ) || (
        s.leader &&
        (
          (
            exists xid : int ::
                xid in s.buffered_commands &&
                command_id in s.buffered_commands[xid] &&
                xid in s'.buffered_commands &&
                var old_map := s.buffered_commands[xid];
                var new_map := s'.buffered_commands[xid];
                s' == s.(buffered_commands := s.buffered_commands[xid := new_map]) &&
                !(command_id in new_map) &&
                var command := old_map[command_id];
                old_map == new_map[command_id := command]
          ) || (
            !(exists xid : int ::
                xid in s.buffered_commands &&
                command_id in s.buffered_commands[xid]) &&
            s' == s
          )
        )
      )
    )
  }

  predicate Node_ControllerMarkEventComplete(
      s: NodeController, s': NodeController, xid: int, ios: seq<RavanaIo>) {
    s.leader &&
    xid in s.buffered_commands &&
    s.buffered_commands[xid] == map[] &&

    |ios| == 1 &&
    ios[0].LIoOpSend? &&
    var send_packet := ios[0].s;
    send_packet.dst == s.config.node_logger &&
    send_packet.msg == LogMessage(LMProc(xid)) &&

    s == s'
  }

  predicate Node_LoggerInitNewMaster(
      s: NodeLogger, s': NodeLogger, ios: seq<RavanaIo>) {
    s'.clients == s.clients &&
    s'.log == s.log &&
    |s'.master_log| >= 1 &&
    s.master_log == s'.master_log[0 .. |s'.master_log| - 1] &&
    |ios| == 0
  }

  predicate Node_LoggerInitNewMasterMsg(
      s: NodeLogger, s': NodeLogger, ios: seq<RavanaIo>) {
    s == s' &&
    |s.master_log| >= 1 &&

    |ios| == 1 &&
    ios[0].LIoOpSend? &&
    var send_packet := ios[0].s;
    send_packet.dst == s.master_log[|s.master_log| - 1] &&
    send_packet.msg == InitNewMaster(|s.master_log| - 1)
  }

  predicate Node_ControllerNewMaster(
      s: NodeController, s': NodeController, ios: seq<RavanaIo>) {
    s.NodeController? &&

    |ios| == 1 &&
    ios[0].LIoOpReceive? &&
    var recv_packet := ios[0].r;
    recv_packet.msg.InitNewMaster? &&

    !s.is_next_leader &&

    s' == s.(is_next_leader := true)
           .(switches_acked_master := {})
           .(my_leader_id := recv_packet.msg.leader_id)
  }

  predicate Node_ControllerSendNewMaster(s: NodeController, s': NodeController, ios: seq<RavanaIo>) {
    s.is_next_leader &&

    |ios| == 1 &&
    ios[0].LIoOpSend? &&
    var send_packet := ios[0].s;
    send_packet.dst in s.config.node_switches &&
    send_packet.msg == NewMaster(s.my_leader_id) &&

    s == s'
  }

  predicate Node_SwitchNewMaster(s: NodeSwitch, s': NodeSwitch, ios: seq<RavanaIo>) {
    |ios| == 2 &&
    ios[0].LIoOpReceive? &&
    var recv_packet := ios[0].r;
    recv_packet.msg.NewMaster? &&
    recv_packet.msg.master_id >= s.master_id &&

    s' == s.(master := recv_packet.src).(master_id := recv_packet.msg.master_id) &&

    ios[1].LIoOpSend? &&
    var send_packet := ios[1].s;
    send_packet.dst == recv_packet.src &&
    send_packet.msg == NewMasterAck
  }

  predicate Node_ControllerRecvNewMasterAck(s: NodeController, s': NodeController, ios: seq<RavanaIo>) {
    s.is_next_leader &&

    |ios| == 1 &&
    ios[0].LIoOpReceive? &&
    var recv_packet := ios[0].r;
    recv_packet.msg.NewMasterAck? &&

    s' == s.(switches_acked_master := s.switches_acked_master + { recv_packet.src })
  }

  predicate Node_ControllerNewMasterFinish(s: NodeController, s': NodeController, ios: seq<RavanaIo>) {
    |ios| == 0 &&
    s.is_next_leader &&
    (forall sw :: sw in s.config.node_switches ==> sw in s.switches_acked_master) &&
    s' == s.(leader := true)
  }
}
