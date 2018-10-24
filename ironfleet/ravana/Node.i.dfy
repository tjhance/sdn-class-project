include "Types.i.dfy"

module Protocol_Node_i {
  import opened Types_i

  datatype Node = NodeController(
                      leader: bool,
                      controllerState: ControllerState,
                | NodeSwitch(
                      bufferedMessages: seq<S2C_Message>,
                      switchState: SwitchState,

   
}
