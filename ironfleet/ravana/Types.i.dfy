include "../../Common/Framework/Environment.s.dfy"
include "../../Common/Native/Io.s.dfy"

module Types_i {
  import opened Environment_s
  import opened Native__Io_s

  type SwitchState
  type ControllerState

  datatype RavanaMessage = 

  type RavanaEnvironment = LEnvironment<EndPoint, RavanaMessage>
  type RavanaPacket = LPacket<EndPoint, RavanaMessage>
  type RavanaIo = LIoOp<EndPoint, RavanaMessage>
}
