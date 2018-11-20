include "Node.i.dfy"
include "Types.i.dfy"
include "../src/Dafny/Distributed/Impl/Common/SeqIsUniqueDef.i.dfy"

module DistributedSystem_i {
  import opened Types_i
  import opened Protocol_Node_i
  import opened Common__SeqIsUniqueDef_i

  predicate RS_Init(rs: RState, config: Config)
  {
       LEnvironment_Init(rs.env)

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
}
