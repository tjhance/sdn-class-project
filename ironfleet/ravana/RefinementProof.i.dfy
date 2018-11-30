include "Types.i.dfy"
include "Refinement.i.dfy"
include "Service.i.dfy"
include "DistributedSystem.i.dfy"

include "RefinementProof/ControllerLogEvent.dfy"
include "RefinementProof/ControllerMarkEventComplete.dfy"
include "RefinementProof/ControllerNewMaster.dfy"
include "RefinementProof/ControllerNewMasterFinish.dfy"
include "RefinementProof/ControllerProcessEntry.dfy"
include "RefinementProof/ControllerReadLog.dfy"
include "RefinementProof/ControllerRecvAck.dfy"
include "RefinementProof/ControllerRecvEvent.dfy"
include "RefinementProof/ControllerRecvNewMasterAck.dfy"
include "RefinementProof/ControllerSendCommand.dfy"
include "RefinementProof/ControllerSendNewMaster.dfy"

include "RefinementProof/LoggerInitNewMaster.dfy"
include "RefinementProof/LoggerInitNewMasterMsg.dfy"
include "RefinementProof/LoggerLogEvent.dfy"
include "RefinementProof/LoggerBroadcast.dfy"

include "RefinementProof/SwitchEvent.dfy"
include "RefinementProof/SwitchEventSend.dfy"
include "RefinementProof/SwitchNewMaster.dfy"
include "RefinementProof/SwitchRecvCommand.dfy"
include "RefinementProof/SwitchRecvCommandSendAck.dfy"

module Refinement_Proof_i {
  import opened Types_i
  import opened Refinement_i
  import opened Service_i
  import opened DistributedSystem_i

  import Refinement_Proof_LoggerInitNewMaster
  import Refinement_Proof_LoggerInitNewMasterMsg
  import Refinement_Proof_LoggerLogEvent
  import Refinement_Proof_LoggerBroadcast

  import Refinement_Proof_ControllerLogEvent
  import Refinement_Proof_ControllerMarkEventComplete
  import Refinement_Proof_ControllerNewMaster
  import Refinement_Proof_ControllerNewMasterFinish
  import Refinement_Proof_ControllerProcessEntry
  import Refinement_Proof_ControllerReadLog
  import Refinement_Proof_ControllerRecvAck
  import Refinement_Proof_ControllerRecvEvent
  import Refinement_Proof_ControllerRecvNewMasterAck
  import Refinement_Proof_ControllerSendCommand
  import Refinement_Proof_ControllerSendNewMaster

  import Refinement_Proof_SwitchEvent
  import Refinement_Proof_SwitchEventSend
  import Refinement_Proof_SwitchNewMaster
  import Refinement_Proof_SwitchRecvCommand
  import Refinement_Proof_SwitchRecvCommandSendAck

  /** MAIN LEMMA **/

  lemma rs_refines_ss(rs: RState, rs': RState)
  requires rstate_valid(rs)
  requires RS_Next(rs, rs')
  ensures rstate_valid(rs')
  ensures Service_Next(refinement(rs), refinement(rs'))
  {
    if (rs.environment.nextStep.LEnvStepHostIos?) {
      if (rs.environment.nextStep.actor == rs.endpoint_logger) {
        var s := rs.logger;
        var s' := rs'.logger;
        var ios := rs.environment.nextStep.ios;

        if (Node_LoggerLogEvent(s, s', ios)) {
          Refinement_Proof_LoggerLogEvent.lemma_refines_LoggerLogEvent(rs, rs');
        } else if (Node_LoggerBroadcast(s, s', ios)) {
          Refinement_Proof_LoggerBroadcast.lemma_refines_LoggerBroadcast(rs, rs');
        } else if (Node_LoggerInitNewMaster(s, s', ios)) {
          Refinement_Proof_LoggerInitNewMaster.lemma_refines_LoggerInitNewMaster(rs, rs');
        } else if (Node_LoggerInitNewMasterMsg(s, s', ios)) {
          Refinement_Proof_LoggerInitNewMasterMsg.lemma_refines_LoggerInitNewMasterMsg(rs, rs');
        }

      } else if (rs.environment.nextStep.actor in rs.controllers) {
        var s := rs.controllers[rs.environment.nextStep.actor];
        var s' := rs'.controllers[rs.environment.nextStep.actor];
        var ios := rs.environment.nextStep.ios;

        if (exists p :: Node_ControllerLogEvent(s, s', p, ios)) {
          var p :| Node_ControllerLogEvent(s, s', p, ios);
          Refinement_Proof_ControllerLogEvent.lemma_refines_ControllerLogEvent(rs, rs', p);
        } else if (exists a :: Node_ControllerMarkEventComplete(s, s', a, ios)) {
          var a :| Node_ControllerMarkEventComplete(s, s', a, ios);
          Refinement_Proof_ControllerMarkEventComplete.lemma_refines_ControllerMarkEventComplete(rs, rs', a);
        } else if (Node_ControllerNewMaster(s, s', ios)) {
          Refinement_Proof_ControllerNewMaster.lemma_refines_ControllerNewMaster(rs, rs');
        } else if (Node_ControllerNewMasterFinish(s, s', ios)) {
          Refinement_Proof_ControllerNewMasterFinish.lemma_refines_ControllerNewMasterFinish(rs, rs');
        } else if (Node_ControllerProcessEntry(s, s', ios)) {
          Refinement_Proof_ControllerProcessEntry.lemma_refines_ControllerProcessEntry(rs, rs');
        } else if (Node_ControllerReadLog(s, s', ios)) {
          Refinement_Proof_ControllerReadLog.lemma_refines_ControllerReadLog(rs, rs');
        } else if (Node_ControllerRecvAck(s, s', ios)) {
          Refinement_Proof_ControllerRecvAck.lemma_refines_ControllerRecvAck(rs, rs');
        } else if (Node_ControllerRecvEvent(s, s', ios)) {
          Refinement_Proof_ControllerRecvEvent.lemma_refines_ControllerRecvEvent(rs, rs');
        } else if (Node_ControllerRecvNewMasterAck(s, s', ios)) {
          Refinement_Proof_ControllerRecvNewMasterAck.lemma_refines_ControllerRecvNewMasterAck(rs, rs');
        } else if (exists a, b :: Node_ControllerSendCommand(s, s', a, b, ios)) {
          var a, b :| Node_ControllerSendCommand(s, s', a, b, ios);
          Refinement_Proof_ControllerSendCommand.lemma_refines_ControllerSendCommand(rs, rs', a, b);
        } else if (Node_ControllerSendNewMaster(s, s', ios)) {
          Refinement_Proof_ControllerSendNewMaster.lemma_refines_ControllerSendNewMaster(rs, rs');
        }

      } else if (rs.environment.nextStep.actor in rs.switches) {
        var s := rs.switches[rs.environment.nextStep.actor];
        var s' := rs'.controllers[rs.environment.nextStep.actor];
        var ios := rs.environment.nextStep.ios;

        if (Node_SwitchEvent(s, s', ios)) {
          Refinement_Proof_SwitchEvent.lemma_refines_SwitchEvent(rs, rs');
        } else if (Node_SwitchEventSend(s, s', ios)) {
          Refinement_Proof_SwitchEventSend.lemma_refines_SwitchEventSend(rs, rs');
        } else if (Node_SwitchNewMaster(s, s', ios)) {
          Refinement_Proof_SwitchNewMaster.lemma_refines_SwitchNewMaster(rs, rs');
        } else if (Node_SwitchRecvCommand(s, s', ios)) {
          Refinement_Proof_SwitchRecvCommand.lemma_refines_SwitchRecvCommand(rs, rs');
        } else if (Node_SwitchRecvCommandSendAck(s, s', ios)) {
          Refinement_Proof_SwitchRecvCommandSendAck.lemma_refines_SwitchRecvCommandSendAck(rs, rs');
        }

      } else {
      }
    } else {
    }
  }
}
