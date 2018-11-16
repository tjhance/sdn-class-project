include "Types.i.dfy"

module Service_i {
  import opened Types_i

  predicate Service_Init(s: ServiceState, switches: set<EndPoint>) {
    s.outstandingCommands == multiset{} &&
    s.outstandingEvents == multiset{} &&
    keys_match(s.switchStates, switches)
  }

  predicate Service_Next(s: ServiceState, s': ServiceState) {
    Service_NextNewEvent(s, s') ||
    Service_NextApplyEvent(s, s') ||
    Service_NextApplyCommand(s, s')
  }

  predicate Service_NextNewEvent(s: ServiceState, s': ServiceState) {
    s.switchStates == s'.switchStates &&
    s.controllerState == s'.controllerState &&
    s.outstandingCommands == s'.outstandingCommands &&
    multiset_adds_one(s.outstandingEvents, s'.outstandingEvents)
  }

  predicate Service_NextApplyEvent(s: ServiceState, s': ServiceState) {
    s.switchStates == s'.switchStates &&
    s.outstandingCommands == multiset{} &&

    multiset_adds_one(s'.outstandingEvents, s.outstandingEvents) &&
    var event := added_obj(s'.outstandingEvents, s.outstandingEvents);
    var (cs', singleCommands) :=
        controllerTransition(s.controllerState, event.switch, event.event);
    s'.controllerState == cs' &&
    s'.outstandingCommands == seq_to_multiset(singleCommands)
  }

  predicate Service_NextApplyCommand(s: ServiceState, s': ServiceState) {
    s.controllerState == s'.controllerState &&
    s.outstandingCommands == s'.outstandingCommands &&

    multiset_adds_one(s'.outstandingCommands, s.outstandingCommands) &&
    var command := added_obj(s'.outstandingCommands, s.outstandingCommands);

    command.switch in s.switchStates &&
    s'.switchStates == s.switchStates[command.switch :=
        switchTransition(s.switchStates[command.switch], command.command) ]
  }

  // helpers

  predicate {:opaque} keys_match<A, B>(m: map<A, B>, s: set<A>) {
    (forall k : A :: k in m ==> k in s) &&
    (forall k : A :: k in s ==> k in m)
  }

  predicate multiset_adds_one<A>(m: multiset<A>, m1: multiset<A>) {
    |m1| == |m| + 1 &&
    |m1 - m| == 1
  }

  function {:opaque}
  added_obj<A>(m: multiset<A>, m1: multiset<A>) : A
  requires multiset_adds_one<A>(m, m1)
  {
    var y :| y in (m1 - m);
    y
  }

  function {:opaque} seq_to_multiset<A>(s: seq<A>) : multiset<A>
  {
    if s == [] then
      multiset{}
    else (
      seq_to_multiset(s[1..]) + multiset{s[0]}
    )
  }
}
