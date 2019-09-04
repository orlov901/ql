private import csharp
private import cil
private import dotnet
private import semmle.code.csharp.dataflow.internal.DataFlowPrivate
private import DelegateDataFlow
private import semmle.code.csharp.dispatch.Dispatch
private import semmle.code.csharp.frameworks.system.Collections
private import semmle.code.csharp.frameworks.system.collections.Generic
import semmle.code.csharp.dataflow.internal.DataFlowDispatchCommon

cached
private module Cached {
  private import CallContext
  private import semmle.code.csharp.Caching

  /** Gets a viable run-time target for the call `call`. */
  cached
  DataFlowCallable viableImpl(DataFlowCall call) { result = getARuntimeTarget(call) }

  /**
   * Gets a viable run-time target for the delegate call `call`, requiring
   * call context `cc`.
   */
  private DotNet::Callable viableDelegateCallable(DataFlowCall call, CallContext cc) {
    result = getARuntimeTarget(call, cc)
  }

  /**
   * Holds if the call context `ctx` reduces the set of viable run-time
   * targets of call `call` in `c`.
   */
  cached
  predicate reducedViableImplInCallContext(DataFlowCall call, DataFlowCallable c, DataFlowCall ctx) {
    c = viableImpl(ctx) and
    c = call.getEnclosingCallable() and
    exists(CallContext cc | exists(viableDelegateCallable(call, cc)) |
      not cc instanceof EmptyCallContext
    )
  }

  private DotNet::Callable viableImplInCallContext(DataFlowCall call, DataFlowCall ctx) {
    exists(ArgumentCallContext cc | result = viableDelegateCallable(call, cc) |
      cc.isArgument(ctx.getExpr(), _)
    )
  }

  /**
   * Gets a viable run-time target for the call `call` in the context
   * `ctx`. This is restricted to those call nodes for which a context
   * might make a difference.
   */
  cached
  DotNet::Callable prunedViableImplInCallContext(DataFlowCall call, DataFlowCall ctx) {
    result = viableImplInCallContext(call, ctx) and
    reducedViableImplInCallContext(call, _, ctx)
  }

  /**
   * Holds if flow returning from callable `c` to call `call` might return
   * further and if this path restricts the set of call sites that can be
   * returned to.
   */
  cached
  predicate reducedViableImplInReturn(DataFlowCallable c, DataFlowCall call) {
    exists(int tgts, int ctxtgts |
      c = viableImpl(call) and
      ctxtgts = strictcount(DataFlowCall ctx | c = viableImplInCallContext(call, ctx)) and
      tgts = strictcount(DataFlowCall ctx | viableImpl(ctx) = call.getEnclosingCallable()) and
      ctxtgts < tgts
    )
  }

  /**
   * Gets a viable run-time target for the call `call` in the context `ctx`.
   * This is restricted to those call nodes and results for which the return
   * flow from the result to `call` restricts the possible context `ctx`.
   */
  cached
  DataFlowCallable prunedViableImplInCallContextReverse(DataFlowCall call, DataFlowCall ctx) {
    result = viableImplInCallContext(call, ctx) and
    reducedViableImplInReturn(result, call)
  }
}
import Cached

predicate viableCallable = viableImpl/1;

/** Gets a viable run-time target of this call requiring call context `cc`. */
DotNet::Callable getARuntimeTarget(DelegateDataFlowCall call, CallContext::CallContext cc) {
  result = call.(ExplicitDelegateDataFlowCall).getDelegateCall().getARuntimeTarget(cc)
  or
  exists(ControlFlow::Nodes::ElementNode cfn |
    cfn = call.(ImplicitDelegateDataFlowCall).getControlFlowNode()
  |
    result = cfn.getElement().(DelegateArgumentToLibraryCallable).getARuntimeTarget(cc)
  )
}

/**
 * Gets a run-time target of this call. A target is always a source
 * declaration, and if the callable has both CIL and source code, only
 * the source code version is returned.
 */
DataFlowCallable getARuntimeTarget(DataFlowCall call) {
  result = getCallableForDataFlow(call
          .(NonDelegateDataFlowCall)
          .getDispatchCall()
          .getADynamicTarget())
  or
  result = getARuntimeTarget(call, _)
  or
  transitiveCapturedCallTarget(call.(TransitiveCapturedDataFlowCall).getControlFlowNode(), result)
  or
  // There is no dispatch library for CIL, so do not consider overrides for now
  result = getCallableForDataFlow(call.(CilDataFlowCall).getCall().getTarget())
}
