include "Node.i.dfy"
include "Types.i.dfy"
include "../src/Dafny/Distributed/Impl/Common/SeqIsUniqueDef.i.dfy"

module DistributedSystem_i {
  import opened Types_i
  import opened Protocol_Node_i
  import opened Common__SeqIsUniqueDef_i

  predicate RS_Init(rs: RState, config: Config)
  {
       LEnvironment_Init(rs.environment)

    && config.node_logger == rs.endpoint_logger
    && NodeInit_Logger(rs.server_logger, config)

    && SeqIsUnique([config.node_logger] + config.node_controllers + config.node_switches)

    && |config.node_controllers| > 0
    && (forall e :: e in rs.server_controllers <==> e in config.node_controllers)
    && (forall index :: 0 <= index < |config.node_controllers| ==>
            NodeInit_Controller(rs.server_controllers[config.node_controllers[index]],
                                index,
                                config)
       )

    && |config.node_switches| > 0
    && (forall e :: e in rs.server_switches <==> e in config.node_switches)
    && (forall index :: 0 <= index < |config.node_switches| ==>
            NodeInit_Switch(rs.server_switches[config.node_switches[index]],
                           index,
                           config)
       )

  }

  predicate RS_Next(rs: RState, rs': RState)
  {
    LEnvironment_Next(rs.environment, rs'.environment) &&
    rs.endpoint_logger == rs'.endpoint_logger &&
    rs.initControllerState == rs'.initControllerState &&
    (if rs.environment.nextStep.LEnvStepHostIos? then
        (if rs.environment.nextStep.actor == rs.endpoint_logger then
            RS_NextOneServer_Logger(rs, rs',
                rs.environment.nextStep.actor, rs.environment.nextStep.ios) &&
            rs.server_controllers == rs'.server_controllers &&
            rs.server_switches == rs'.server_switches
        else if rs.environment.nextStep.actor in rs.server_controllers then
            RS_NextOneServer_Controller(rs, rs',
                rs.environment.nextStep.actor, rs.environment.nextStep.ios) &&
            rs.server_logger == rs'.server_logger &&
            rs.server_switches == rs'.server_switches
        else if rs.environment.nextStep.actor in rs.server_switches then
            RS_NextOneServer_Switch(rs, rs',
                rs.environment.nextStep.actor, rs.environment.nextStep.ios) &&
            rs.server_logger == rs'.server_logger &&
            rs.server_controllers == rs'.server_controllers
        else
            rs.server_logger == rs'.server_logger &&
            rs.server_controllers == rs'.server_controllers &&
            rs.server_switches == rs'.server_switches
        )
      else
        rs.server_logger == rs'.server_logger &&
        rs.server_controllers == rs'.server_controllers &&
        rs.server_switches == rs'.server_switches
    )
  }

  predicate RS_NextOneServer_Logger(rs: RState, rs': RState, id: EndPoint, ios: seq<RavanaIo>)
  requires id == rs.endpoint_logger
  {
        id == rs'.endpoint_logger
     && NodeNext_Logger(rs.server_logger, rs'.server_logger, ios)
  }

  predicate RS_NextOneServer_Controller(rs: RState, rs': RState, id: EndPoint, ios: seq<RavanaIo>)
  requires id in rs.server_controllers
  {
        id in rs'.server_controllers
     && NodeNext_Controller(rs.server_controllers[id], rs'.server_controllers[id], ios)
     && rs'.server_controllers == rs.server_controllers[id := rs'.server_controllers[id]]
  }

  predicate RS_NextOneServer_Switch(rs: RState, rs': RState, id: EndPoint, ios: seq<RavanaIo>)
  requires id in rs.server_switches
  {
        id in rs'.server_switches
     && NodeNext_Switch(rs.server_switches[id], rs'.server_switches[id], ios)
     && rs'.server_switches == rs.server_switches[id := rs'.server_switches[id]]
  }

}
