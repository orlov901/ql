/**
 * INTERNAL: Do not use.
 *
 * Provides classes for resolving delegate calls.
 */

import csharp
private import dotnet
private import DataFlowImpl
private import DataFlowImplCommon
private import semmle.code.csharp.dataflow.internal.DataFlowDispatchCommon
private import semmle.code.csharp.dataflow.internal.DataFlowPrivate
private import semmle.code.csharp.dataflow.internal.DataFlowPublic
private import semmle.code.csharp.dispatch.Dispatch
private import semmle.code.csharp.frameworks.system.linq.Expressions

/** A source of flow for a delegate expression. */
private class DelegateFlowSource extends DataFlow::ExprNode {
  Callable c;

  DelegateFlowSource() {
    this.getExpr() = any(Expr e |
        c = e.(AnonymousFunctionExpr) or
        c = e.(CallableAccess).getTarget().getSourceDeclaration()
      )
  }

  /** Gets the callable that is referenced in this delegate flow source. */
  Callable getCallable() { result = c }
}

/** A sink of flow for a delegate expression. */
abstract private class DelegateFlowSink extends DataFlow::ExprNode {

  private 
  predicate well2(DelegateFlowSource dfs, CallContext ctx) {
    exists(Blah x, PathNode source, PathNode sink|
      x.hasFlowPath(source, sink) and
      dfs = source.getNode() and
      this = sink.getNode()
      |
      source.getNode() = sink.getNode() and
      ctx instanceof CallContextAny
      or
      exists(PathNode last |
        source.getASuccessor*() = last and
        last.getASuccessor() = sink and
        ctx = last.getCallContext()
      )
    )
  }

  /**
   * Gets an actual run-time target of this delegate call in the given call
   * context, if any. The call context records the *last* call required to
   * resolve the target, if any. Example:
   *
   * ```
   * public int M(Func<string, int> f, string x) {
   *   return f(x);
   * }
   *
   * void M2() {
   *   M(x => x.Length, y);
   *
   *   M(_ => 42, z);
   *
   *   Func<int, bool> isZero = x => x == 0;
   *   isZero(10);
   * }
   * ```
   *
   * - The call on line 2 can be resolved to either `x => x.Length` (line 6)
   *   or `_ => 42` (line 8) in the call contexts from lines 7 and 8,
   *   respectively.
   * - The call on line 11 can be resolved to `x => x == 0` (line 10) in an
   *   empty call context (the call is locally resolvable).
   *
   * Note that only the *last* call required is taken into account, hence if
   * `M` above is redefined as follows:
   *
   * ```
   * public int M(Func<string, int> f, string x) {
   *   return M2(f, x);
   * }
   *
   * public int M2(Func<string, int> f, string x) {
   *   return f(x);
   * }
   *
   * void M2() {
   *   M(x => x.Length, y);
   *
   *   M(_ => 42, z);
   *
   *   Func<int, bool> isZero = x => x == 0;
   *   isZero(10);
   * }
   * ```
   *
   * then the call context from line 2 is the call context for all
   * possible delegates resolved on line 6.
   */
  cached
  Callable getARuntimeTarget(CallContext::CallContext context) {
    exists(DelegateFlowSource dfs, CallContext ctx |
      well2(dfs, ctx) and
      result = dfs.getCallable()
    |
      exists(DataFlowCall call, int i |
        ctx = TSpecificCall(call, i, _) |
        context.(CallContext::ArgumentCallContext).isArgument(call.getExpr(), i)
      )
      or
      not ctx instanceof TSpecificCall and
      context instanceof CallContext::EmptyCallContext
    )
  }
}

/** A delegate call expression. */
class DelegateCallExpr extends DelegateFlowSink {
  DelegateCall dc;

  DelegateCallExpr() { this.getExpr() = dc.getDelegateExpr() }

  /** Gets the delegate call that this expression belongs to. */
  DelegateCall getDelegateCall() { result = dc }
}

/** A delegate expression that is passed as the argument to a library callable. */
class DelegateArgumentToLibraryCallableSink extends DelegateFlowSink {
  DelegateArgumentToLibraryCallableSink() {
    this.getExpr() instanceof DelegateArgumentToLibraryCallable
  }
}

/** A delegate expression that is added to an event. */
class AddEventSource extends DelegateFlowSink {
  AddEventExpr ae;

  AddEventSource() { this.getExpr() = ae.getRValue() }

  /** Gets the event that this delegate is added to. */
  Event getEvent() { result = ae.getTarget() }
}

/** A non-delegate call. */
private class NonDelegateCall extends Expr {
  private DispatchCall dc;

  NonDelegateCall() { this = dc.getCall() }

  /**
   * Gets a run-time target of this call. A target is always a source
   * declaration, and if the callable has both CIL and source code, only
   * the source code version is returned.
   */
  Callable getARuntimeTarget() { result = getCallableForDataFlow(dc.getADynamicTarget()) }

  /** Gets the `i`th argument of this call. */
  Expr getArgument(int i) { result = dc.getArgument(i) }
}

private class Blah extends Configuration {
  Blah() { this = "blah" }

  override predicate isSource(Node source) {
    source instanceof DelegateFlowSource
  }

  override predicate isSink(Node sink) {
    sink instanceof DelegateFlowSink
  }

  override predicate isAdditionalFlowStep(Node node1, Node node2) {
    // TODO: Splitting
    node1.asExpr() = node2.asExpr().(DelegateCreation).getArgument()
  }
}

predicate well(Blah b, Node source, Node sink) {
  b.hasFlow(source, sink)
}

predicate well2(PathNode source, PathNode sink, CallContext ctx) {
    exists(Blah x|
      x.hasFlowPath(source, sink) |
      source.getNode() = sink.getNode() and
      ctx instanceof CallContextAny
      or
      exists(PathNode last |
        source.getASuccessor*() = last and
        last.getASuccessor() = sink and
        ctx = last.getCallContext()
      )
    )
  }