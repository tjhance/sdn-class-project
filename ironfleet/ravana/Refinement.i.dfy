include "Types.i.dfy"

module Refinement_i {
  import opened Types_i

  predicate rstate_valid(rs: RState) {
    true
  }

  predicate service_state_valid(ss: ServiceState) {
    true /* TODO */
  }

  predicate refinement(rs: RState, ss: ServiceState)
  {
    rstate_valid(rs) &&
    service_state_valid(ss) &&

    var log := rs.server_logger.log;

    var (fwdControllerState, fwdOutstandingCommands) :=
          controller_state_looking_forward(log, rs.initControllerState);

    var curOutstandingCommands := set_to_multiset(set
          command_id : int | (
            0 <= command_id < |fwdOutstandingCommands| &&
            var command := fwdOutstandingCommands[command_id];
            command.switch in rs.server_switches &&
            !(command_id in rs.server_switches[command.switch].received_command_ids)
          ) ::
            (command_id, fwdOutstandingCommands[command_id])
        );

    ss.switchStates == (
      map switch : EndPoint
      | switch in rs.server_switches
      :: rs.server_switches[switch].switchState
    ) &&

    ss.controllerState == fwdControllerState &&
    ss.outstandingCommands == curOutstandingCommands &&

    var outstandingEvents := set_to_multiset(set
          switch : EndPoint, eid : int | (
            switch in rs.server_switches &&
            eid in rs.server_switches[switch].bufferedEvents
          ) ::
            ((switch, eid), SwitchEvent(switch, rs.server_switches[switch].bufferedEvents[eid]))
        );

    ss.outstandingEvents == outstandingEvents
  }

  function controller_state_looking_forward(
      log: seq<LogEntry>,
      controllerState: ControllerState) : (ControllerState, seq<SingleCommand>)
  {
    if |log| == 0 then
      (controllerState, [])
    else (
      var elem := log[0];
      if elem.LMProc? then (
        controller_state_looking_forward(log[1 .. ], controllerState)
      ) else (
        var (cs', comms1) := controllerTransition(controllerState, elem.switch, elem.event);
        var (cs'', comms2) := controller_state_looking_forward(log[1 .. ], cs');
        (cs'', comms1 + comms2)
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
}
