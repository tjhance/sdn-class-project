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

  /*
  lemma lemma_refines_Logger_InitNewMaster(rs: RState, rs': RState)
  requires rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor == rs'.endpoint_logger
  requires Node_LoggerInitNewMaster(
              rs.server_logger, rs'.server_logger, rs.environment.nextStep.ios)
  requires rs.server_controllers == rs'.server_controllers
  requires rs.server_switches == rs'.server_switches

  ensures rstate_valid(rs')
  ensures refinement(rs) == refinement(rs')
  {
    assert refinement_switchStates(rs.server_switches)
        == refinement_switchStates(rs'.server_switches);

    assert rs.server_logger.log == rs'.server_logger.log;

    assert refinement_controllerState(rs.server_logger.log, rs.initControllerState)
        == refinement_controllerState(rs'.server_logger.log, rs'.initControllerState);

    assert refinement_outstandingCommands(rs.server_logger.log, rs.initControllerState, rs.server_switches)
        == refinement_outstandingCommands(rs'.server_logger.log, rs'.initControllerState, rs'.server_switches);

    assert refinement_outstandingEvents(rs.server_switches, rs.server_logger.log)
        == refinement_outstandingEvents(rs'.server_switches, rs'.server_logger.log);
  }

  lemma lemma_refines_Logger_InitNewMasterMsg(rs: RState, rs': RState)
  requires rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor == rs'.endpoint_logger
  requires Node_LoggerInitNewMasterMsg(
              rs.server_logger, rs'.server_logger, rs.environment.nextStep.ios)
  requires rs.server_controllers == rs'.server_controllers
  requires rs.server_switches == rs'.server_switches

  ensures rstate_valid(rs')
  ensures refinement(rs) == refinement(rs')
  {
    
  }
  */

  /*
  lemma lemma_refines_LoggerBroadcast(rs: RState, rs': RState)
  requires rstate_valid(rs)

  requires LEnvironment_Next(rs.environment, rs'.environment)
  requires rs.environment.nextStep.LEnvStepHostIos?
  requires rs.endpoint_logger == rs'.endpoint_logger
  requires rs.initControllerState == rs'.initControllerState
  requires rs.environment.nextStep.actor == rs'.endpoint_logger
  requires Node_LoggerBroadcast(
              rs.server_logger, rs'.server_logger, rs.environment.nextStep.ios)
  requires rs.server_controllers == rs'.server_controllers
  requires rs.server_switches == rs'.server_switches

  ensures rstate_valid(rs')
  ensures refinement(rs) == refinement(rs')
  {

  }
  */
}
