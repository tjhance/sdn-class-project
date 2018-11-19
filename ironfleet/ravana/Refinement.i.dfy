include "Types.i.dfy"

module Refinement_i {
  import opened Types_i

  predicate rstate_valid(rs: RState) {
    true /* TODO */
  }

  predicate service_state_valid(ss: ServiceState) {
    true /* TODO */
  }

  predicate refinement(rs: RState, ss: ServiceState)
  {
    rstate_valid(rs) &&
    service_state_valid(ss) &&

    //var master_node := rs_master_controller(rs);
    var log := rs_log(rs);

    var (fwdControllerState, fwdOutstandingCommands) :=
          controller_state_looking_forward(log, rs.initControllerState);

    var curOutstandingCommands := map_to_multiset(map
          command_id : int | (
            0 <= command_id < |fwdOutstandingCommands| &&
            var command := master_node.buffered_commands[xid][command_id];
            !(command_id in rs.servers[command.switch].received_command_ids)
          ) ::
            master_node.buffered_commands[xid][command_id]
        );


    /*
    var curOutstandingCommands := set_to_multiset(set
          xid : int , command_id : int | (
            xid in master_node.buffered_commands &&
            command_id in master_node.buffered_commands[xid] &&
            var command := master_node.buffered_commands[xid][command_id];
            !(command_id in rs.servers[command.switch].received_command_ids)
          ) ::
            ((xid, command_id), master_node.buffered_commands[xid][command_id])
        );
    */

    ss.switchStates == (
      map switch : EndPoint
      | switch in rs_switches(rs)
      :: rs.servers[switch].switchState
    ) &&

    ss.controllerState == fwdControllerState &&
    ss.outstandingCommands == fwdOutstandingCommands &&

    var outstandingEvents := set_to_multiset(set
          switch : EndPoint, eid : int | (
            switch in rs.servers &&
            rs.servers[switch].NodeSwitch? &&
            eid in rs.servers[switch].bufferedEvents
          ) ::
            ((switch, eid), rs.servers[switch].bufferedEvents[eid])
        );

    ss.outstandingEvents == outstandingEvents
  }

  function rs_logger_controller(rs: RState) : Node
  requires rstate_valid(rs)
  ensures Node.NodeLogger?
  {
    var ep :| ep in rs.servers && rs.servers[ep].NodeLogger?;
    ep
  }

  function rs_log(rs: RState) : seq<LogEntry>
  requires rstate_valid(rs)
  {
    rs_logger_controller(rs).log
  }

  function controller_state_looking_forward(
      log: seq<LogEntry>,
      controllerState: ControllerState) : (ControllerState, seq<SingleCommand>)
  {
    if |log| == 0 then
      (controllerState, [])
    else (
      var elem := log[0];
      if elem.LMProc then (
        controller_state_looking_forward(log[1 .. ], controllerState)
      ) else (
        var cs', comms1 := controllerTransition(controllerState, elem.switch, elem.event);
        var cs'', comms2 := controller_state_looking_forward(log[1 .. ], cs');
        (cs'', comms1 + comms2)
      )
    )
  }
}
