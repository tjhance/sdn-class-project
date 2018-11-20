include "Node.i.dfy"
include "Types.i.dfy"

module DistributedSystem_i {
  import opened Protocol_Node_i

  predicate RS_Init(rs: RS_State, config: Config)
  {
       LEnvironment_Init(rs.environment)
    && |config.node_controllers| > 0
    && |config.node_switches| > 0
    && NodeInit_Logger(config.node_logger, config)
    && (forall e :: e in rs.servers <==> (e == config.node_logger
          || e in config.node_controllers || e in config.node_switches))
    && NodeInit_Controller(rs.servers[config.node_logger], config)
    && (forall e in config.node_controllers ::
          NodeInit_Logger
  }
}
