include "../src/Dafny/Distributed/Common/Framework/Environment.s.dfy"
include "../src/Dafny/Distributed/Common/Native/Io.s.dfy"

module Types_i {
  import opened Environment_s
  import opened Native__Io_s

  type SwitchState
  type ControllerState

  predicate controllerStateInit(cs: ControllerState)
  predicate switchStateInit(ss: SwitchState)

  type Event
  type Command

  datatype RavanaMessage = 
      EventMessage(event: Event, event_id: int)
    | EventAck(event_ack_id: int)
    | CommandMessage(command: Command, command_id: int)
    | CommandAck(command_ack_id: int)
    | InitNewMaster(leader_id: int)
    | NewMaster(master_id: int)
    | NewMasterAck
    | LogMessage(log_entry: LogEntry)
    | LogBroadcastMessage(full_log: seq<LogEntry>)

  datatype LogEntry =
      LMRecv(switch: EndPoint, event: Event, event_id: int)
    | LMProc(comp_id: int)

  datatype SwitchIdPair = SwitchIdPair(switch: EndPoint, event_id: int)

  type RavanaEnvironment = LEnvironment<EndPoint, RavanaMessage>
  type RavanaPacket = LPacket<EndPoint, RavanaMessage>
  type RavanaIo = LIoOp<EndPoint, RavanaMessage>

  datatype SingleCommand = SingleCommand(switch: EndPoint, command: Command)

  function controllerTransition(
      cs: ControllerState,
      switch: EndPoint,
      event: Event) : (ControllerState, seq<SingleCommand>)

  function switchTransition(
      ss: SwitchState,
      command: Command) : SwitchState

  datatype SwitchEvent = SwitchEvent(switch: EndPoint, event: Event)

  datatype ServiceState = ServiceState(
      switchStates: map<EndPoint, SwitchState>,
      controllerState: ControllerState,

      outstandingCommands: multiset<SingleCommand>,
      outstandingEvents: multiset<SwitchEvent>
    )

  datatype Config = Config(
      node_logger: EndPoint,
      node_controllers: seq<EndPoint>,
      node_switches: seq<EndPoint>
    )

  datatype NodeLogger = NodeLogger(
          clients: seq<EndPoint>,

          log: seq<LogEntry>,

          master_log: seq<EndPoint>
      )
  datatype NodeController = NodeController(
          leader: bool,
          controllerState: ControllerState,
          config: Config,

          recved_events: map<SwitchIdPair, Event>,

          log_copy: seq<LogEntry>,
          idx: int,

          buffered_commands: map<int /* xid */, map<int /* command id */, SingleCommand>>,
          current_command_id: int,

          is_next_leader: bool,
          switches_acked_master: set<EndPoint>,
          my_leader_id: int
      )
  datatype NodeSwitch = NodeSwitch(
          bufferedEvents: map<int, Event>,
          switchState: SwitchState,
          event_id: int,
          master: EndPoint,
          master_id: int,
          received_command_ids: seq<int>
      )

  datatype RState = RState(
      environment: RavanaEnvironment,

      endpoint_logger: EndPoint,
      server_logger: NodeLogger,
      server_controllers: map<EndPoint, NodeController>,
      server_switches: map<EndPoint, NodeSwitch>,

      initControllerState: ControllerState
    )
}
