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
          log: seq<LogEntry>
      )
    | NodeController(
          leader: bool,
          controllerState: ControllerState,
          config: Config,

          recved_events: map<SwitchIdPair, Event>,

          log_copy: seq<LogEntry>
      )
    | NodeSwitch(
          bufferedEvents: seq<Event>,
          switchState: SwitchState,
          event_id: int,
          master: EndPoint
      )

  predicate NodeInit(node: Node, my_index: int, config: Config) {
    (
      node.NodeLogger? &&
        node.log == []
    ) || (
      node.NodeController? &&
        node.leader == (my_index == 0) &&
        controllerStateInit(node.controllerState) &&
        node.config == config
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

  predicate Node_ControllerLogEvent(s: Node, s': Node, ios: seq<RavanaIo>) {
    s.NodeController? &&
    s.leader &&
    s' == s &&
    |ios| == 2 &&
    ios[0].LIoOpReceive? &&
    ios[1].LIoOpSend? &&
    var recv_packet := ios[0].r;
    var send_packet := ios[1].s;

    recv_packet.msg.EventMessage? &&

    send_packet.dst == s.config.node_logger &&
    send_packet.msg == LogMessage(LMRecv(
        recv_packet.src, recv_packet.msg.event, recv_packet.msg.event_id))
  }

  // TODO get the log 

  //predicate Node_ControllerProc
}
