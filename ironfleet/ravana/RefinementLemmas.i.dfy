include "Types.i.dfy"
include "Refinement.i.dfy"
include "Service.i.dfy"
include "DistributedSystem.i.dfy"
include "../src/Dafny/Distributed/Common/Framework/Environment.s.dfy"

module Refinement_Lemmas_i {
  import opened Types_i
  import opened Refinement_i
  import opened Service_i
  import opened DistributedSystem_i
  import opened Environment_s

  predicate {:opaque} packet_validation_preserved(rs: RState, rs': RState)
  {
    forall p : LPacket<EndPoint, RavanaMessage>
             :: is_valid_message(rs, p.src, p.dst, p.msg) ==>
                is_valid_message(rs', p.src, p.dst, p.msg)
  }

  lemma lemma_packets_are_valid_no_sending(rs: RState, rs': RState)
  requires rstate_valid(rs)
  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires packet_validation_preserved(rs, rs')
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires forall io :: io in rs.environment.nextStep.ios ==> !io.LIoOpSend?
  ensures packets_are_valid(rs')
  {
      assert rs'.environment.sentPackets == rs.environment.sentPackets +
          (set io | io in rs.environment.nextStep.ios && io.LIoOpSend? :: io.s);

      assert rs'.environment.sentPackets == rs.environment.sentPackets;

      reveal_packets_are_valid();
      assert packets_are_valid(rs);
      assert forall p :: p in rs.environment.sentPackets ==> is_valid_message(rs, p.src, p.dst, p.msg);

      forall p | p in rs'.environment.sentPackets
        ensures is_valid_message(rs', p.src, p.dst, p.msg)
      {
        assert p in rs.environment.sentPackets;
        assert is_valid_message(rs, p.src, p.dst, p.msg);
        reveal_packet_validation_preserved();
      }
  }
}
