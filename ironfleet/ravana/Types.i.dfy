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
    | NewMaster
    | LogMessage(log_entry: LogEntry)

  datatype LogEntry =
      LMRecv(switch: EndPoint, event: Event, event_id: int)
    | LMProc(comp_id: int)

  datatype SwitchIdPair = SwitchIdPair(switch: EndPoint, event_id: int)

  type RavanaEnvironment = LEnvironment<EndPoint, RavanaMessage>
  type RavanaPacket = LPacket<EndPoint, RavanaMessage>
  type RavanaIo = LIoOp<EndPoint, RavanaMessage>
}
