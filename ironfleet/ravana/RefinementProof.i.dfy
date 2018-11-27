include "Types.i.dfy"
include "Refinement.i.dfy"
include "Service.i.dfy"
include "DistributedSystem.i.dfy"

module Refinement_Proof_i {
  import opened Types_i
  import opened Refinement_i
  import opened Service_i
  import opened DistributedSystem_i

  /** MAIN LEMMA **/

  /*
  lemma rs_refines_ss(rs: RState, rs': RState)
  requires rstate_valid(rs)
  requires RS_Next(rs, rs')
  ensures rstate_valid(rs')
  ensures Service_Next(refinement(rs), refinement(rs'))
  {
  }
  */
}
