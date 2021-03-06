include "Types.i.dfy"
include "Collections.dfy"

module Service_i {
  import opened Types_i
  import opened Collections

  predicate Service_Init(s: ServiceState, switches: set<EndPoint>) {
    s.outstandingCommands == multiset{} &&
    s.outstandingEvents == multiset{} &&
    keys_match(s.switchStates, switches)
  }

  predicate Service_Next(s: ServiceState, s': ServiceState) {
    Service_NextNewEvent(s, s') ||
    Service_NextApplyEvent(s, s') ||
    Service_NextApplyCommand(s, s') ||
    s == s'
  }

  predicate Service_NextNewEvent(s: ServiceState, s': ServiceState) {
    s.switchStates == s'.switchStates &&
    s.controllerState == s'.controllerState &&
    s.outstandingCommands == s'.outstandingCommands &&
    multiset_adds_one(s.outstandingEvents, s'.outstandingEvents)
  }

  predicate Service_NextApplyEvent(s: ServiceState, s': ServiceState) {
    s.switchStates == s'.switchStates &&

    multiset_adds_one(s'.outstandingEvents, s.outstandingEvents) &&
    var event := added_obj(s'.outstandingEvents, s.outstandingEvents);
    var (cs', singleCommands) :=
        controllerTransition(s.controllerState, event.switch, event.event);
    s'.controllerState == cs' &&
    s'.outstandingCommands == s.outstandingCommands + seq_to_multiset(singleCommands)
  }

  predicate Service_NextApplyCommand(s: ServiceState, s': ServiceState) {
    s.controllerState == s'.controllerState &&
    s.outstandingEvents == s'.outstandingEvents &&

    multiset_adds_one(s'.outstandingCommands, s.outstandingCommands) &&
    var command := added_obj(s'.outstandingCommands, s.outstandingCommands);

    command.switch in s.switchStates &&
    s'.switchStates == s.switchStates[command.switch :=
        switchTransition(s.switchStates[command.switch], command.command) ]
  }
}
