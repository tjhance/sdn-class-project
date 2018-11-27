include "Types.i.dfy"
include "Refinement.i.dfy"
include "Service.i.dfy"
include "DistributedSystem.i.dfy"
include "../src/Dafny/Distributed/Common/Framework/Environment.s.dfy"

module RefinementLemmas_i {
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

  lemma {:axiom} lemma_packets_are_valid_no_sending(rs: RState, rs': RState)
  requires rstate_valid(rs)
  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires packet_validation_preserved(rs, rs')
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires forall io :: io in rs.environment.nextStep.ios ==> !io.LIoOpSend?
  ensures packets_are_valid(rs')
  /*
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
  */

  lemma
  {:axiom}
  {:fuel is_valid_message,0,0}
  lemma_received_packet_is_valid(
      rs: RState, rs': RState,
      packet: LPacket<EndPoint, RavanaMessage>)
  requires rstate_valid(rs)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires |rs.environment.nextStep.ios| >= 1
  requires rs.environment.nextStep.ios[0].LIoOpReceive?
  requires packet == rs.environment.nextStep.ios[0].r
  ensures is_valid_message(rs, packet.src, packet.dst, packet.msg)
  /*
  {
    assert packets_are_valid(rs);
    assert packet in rs.environment.sentPackets;
    reveal_packets_are_valid();
  }
  */

  lemma {:axiom} lemma_packets_are_valid_sending_1(rs: RState, rs': RState)
  requires rstate_valid(rs)
  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires packet_validation_preserved(rs, rs')
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires |rs.environment.nextStep.ios| == 1
  requires rs.environment.nextStep.ios[0].LIoOpSend?
  requires is_valid_message(rs', 
      rs.environment.nextStep.ios[0].s.src,
      rs.environment.nextStep.ios[0].s.dst,
      rs.environment.nextStep.ios[0].s.msg)
  ensures packets_are_valid(rs')
  /*
  {
      assert rs'.environment.sentPackets == rs.environment.sentPackets +
          (set io | io in rs.environment.nextStep.ios && io.LIoOpSend? :: io.s);

      assert rs'.environment.sentPackets == rs.environment.sentPackets +
          { rs.environment.nextStep.ios[0].s };

      reveal_packets_are_valid();
      assert packets_are_valid(rs);
      assert forall p :: p in rs.environment.sentPackets ==> is_valid_message(rs, p.src, p.dst, p.msg);

      forall p | p in rs'.environment.sentPackets
        ensures is_valid_message(rs', p.src, p.dst, p.msg)
      {
        if (p == rs.environment.nextStep.ios[0].s) {
        } else {
          assert p in rs.environment.sentPackets;
          assert is_valid_message(rs, p.src, p.dst, p.msg);
          reveal_packet_validation_preserved();
        }
      }
  }
  */
}
