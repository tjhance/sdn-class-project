include "Types.i.dfy"

module Service_i {
  predicate Service_Init(s: ServiceState, switches: set<EndPoint>) {
    s.outstandingCommands == {} &&
    s.outstandingEvents == {} &&
    keys_match(s.switchStates, switches)
  }

  predicate Service_Next(s: ServiceState, s': ServiceState) {
    Service_NextNewEvent(s, s') ||
    Service_NextApplyEvent(s, s') ||
    Service_NextApplyCommand(s, s')
  }

  predicate Service_NextNewEvent(s: ServiceState, s': ServiceState) {
  }
}
