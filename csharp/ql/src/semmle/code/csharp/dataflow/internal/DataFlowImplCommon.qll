private import DataFlowImplSpecific::Private
private import DataFlowImplSpecific::Public

module Public {
  import Cached

  cached
  private module Cached {
    /**
     * Holds if `p` is the `i`th parameter of a viable dispatch target of `call`.
     * The instance parameter is considered to have index `-1`.
     */
    pragma[nomagic]
    private predicate viableParam(DataFlowCall call, int i, ParameterNode p) {
      p.isParameterOf(viableCallable(call), i)
    }

    /**
     * Holds if `arg` is a possible argument to `p` in `call`, taking virtual
     * dispatch into account.
     */
    cached
    predicate viableParamArg(DataFlowCall call, ParameterNode p, ArgumentNode arg) {
      exists(int i |
        viableParam(call, i, p) and
        arg.argumentOf(call, i)
      )
    }

    private module FlowThrough {
      /**
       * Holds if `p` can flow to `node` in the same callable using only
       * value-preserving steps, not taking call contexts into account.
       *
       * `contentIn` describes the content of `p` that can flow to `node`
       * (if any), and `contentOut` describes the content of `node` that
       * it flows to (if any).
       */
      predicate parameterValueFlowNoCtx(
        ParameterNode p, Node node, ContentOption contentIn, ContentOption contentOut
      ) {
        parameterValueFlowNoCtx0(p, node, contentIn, contentOut) and
        (
          // normal flow through
          contentIn = TContentNone() and
          contentOut = TContentNone() and
          compatibleTypes(getErasedNodeTypeBound(p), getErasedNodeTypeBound(node))
          or
          // getter
          exists(Content fIn |
            contentIn.getContent() = fIn and
            contentOut = TContentNone() and
            compatibleTypes(fIn.getType(), getErasedNodeTypeBound(node))
          )
          or
          // setter
          exists(Content fOut |
            contentIn = TContentNone() and
            contentOut.getContent() = fOut and
            compatibleTypes(getErasedNodeTypeBound(p), fOut.getType()) and
            compatibleTypes(fOut.getContainerType(), getErasedNodeTypeBound(node))
          )
          or
          // getter+setter
          exists(Content fIn, Content fOut |
            contentIn.getContent() = fIn and
            contentOut.getContent() = fOut and
            compatibleTypes(fIn.getType(), fOut.getType()) and
            compatibleTypes(fOut.getContainerType(), getErasedNodeTypeBound(node))
          )
        )
      }

      pragma[nomagic]
      private predicate parameterValueFlowNoCtx0(
        ParameterNode p, Node node, ContentOption contentIn, ContentOption contentOut
      ) {
        p = node and
        contentIn = TContentNone() and
        contentOut = TContentNone()
        or
        // local flow
        exists(Node mid |
          parameterValueFlowNoCtx(p, mid, contentIn, contentOut) and
          simpleLocalFlowStep(mid, node)
        )
        or
        // read
        exists(Node mid, Content f, ContentOption contentInMid, ContentOption contentOutMid |
          parameterValueFlowNoCtx(p, mid, contentInMid, contentOutMid) and
          readStep(mid, f, node)
        |
          // value neither read nor stored prior to read
          contentInMid = TContentNone() and
          contentOutMid = TContentNone() and
          contentIn.getContent() = f and
          contentOut = TContentNone()
          or
          // value (possibly read and then) stored prior to read (same content)
          contentIn = contentInMid and
          contentOutMid.getContent() = f and
          contentOut = TContentNone()
        )
        or
        // store
        exists(Node mid, Content f |
          parameterValueFlowNoCtx(p, mid, contentIn, TContentNone()) and
          storeStep(mid, f, node) and
          contentOut.getContent() = f
        )
        or
        // flow through: no prior read or store
        exists(ArgumentNode arg |
          parameterValueFlowArgNoCtx(p, arg, TContentNone(), TContentNone()) and
          argumentValueFlowsThroughNoCtx(arg, node, contentIn, contentOut)
        )
        or
        // flow through: no read or store inside method
        exists(ArgumentNode arg |
          parameterValueFlowArgNoCtx(p, arg, contentIn, contentOut) and
          argumentValueFlowsThroughNoCtx(arg, node, TContentNone(), TContentNone())
        )
        or
        // flow through: prior read (but no store); in this case the flow-through
        // method is not allowed to read, but is allowed to store
        exists(ArgumentNode arg |
          parameterValueFlowArgNoCtx(p, arg, contentIn, TContentNone()) and
          argumentValueFlowsThroughNoCtx(arg, node, TContentNone(), contentOut) and
          contentIn.hasContent()
        )
        or
        // flow through: possible prior read and definite prior store; in this case
        // the flow-through method is allowed to read same content back out
        exists(ArgumentNode arg, ContentOption contentOutBefore |
          parameterValueFlowArgNoCtx(p, arg, contentIn, contentOutBefore) and
          argumentValueFlowsThroughNoCtx(arg, node, TContentSome(contentOutBefore.getContent()),
            contentOut)
        )
      }

      pragma[noinline]
      private predicate parameterValueFlowArgNoCtx(
        ParameterNode p, ArgumentNode arg, ContentOption contentIn, ContentOption contentOut
      ) {
        parameterValueFlowNoCtx(p, arg, contentIn, contentOut) and
        argumentValueFlowsThroughNoCtx(arg, _, _, _)
      }

      pragma[noinline]
      private predicate parameterValueFlowsToPreUpdateNoCtx(ParameterNode p, PostUpdateNode n) {
        parameterValueFlowNoCtx(p, n.getPreUpdateNode(), TContentNone(), TContentNone())
      }

      pragma[noinline]
      private predicate parameterValueFlowsToPostUpdateNoCtx(
        ParameterNode p, PostUpdateNode n, ContentOption contentIn, ContentOption contentOut
      ) {
        parameterValueFlowNoCtx(p, n, contentIn, contentOut) and
        contentOut.hasContent()
      }

      /**
       * Holds if `p` can flow to a return node of kind `kind` in the same
       * callable using only value-preserving steps, not taking call contexts
       * into account.
       *
       * `contentIn` describes the content of `p` that can flow to the return
       * node (if any), and `contentOut` describes the content of the return
       * node that it flows to (if any).
       */
      private predicate parameterValueFlowsThroughNoCtx(
        ParameterNode p, ReturnKindExt kind, ContentOption contentIn, ContentOption contentOut
      ) {
        exists(ReturnNode ret |
          parameterValueFlowNoCtx(p, ret, contentIn, contentOut) and
          kind = TValueReturn(ret.getKind())
        )
        or
        exists(ParameterNode p2, int pos2, PostUpdateNode n |
          parameterValueFlowsToPostUpdateNoCtx(p, n, contentIn, contentOut) and
          parameterValueFlowsToPreUpdateNoCtx(p2, n) and
          p2.isParameterOf(_, pos2) and
          kind = TParamUpdate(pos2)
        )
      }

      pragma[nomagic]
      private predicate argumentValueFlowsThroughNoCtx0(
        DataFlowCall call, ArgumentNode arg, ReturnKindExt kind, ContentOption contentIn,
        ContentOption contentOut
      ) {
        exists(ParameterNode param | viableParamArg(call, param, arg) |
          parameterValueFlowsThroughNoCtx(param, kind, contentIn, contentOut)
        )
      }

      /**
       * Holds if `arg` flows to `out` through a call using only value-preserving steps,
       * not taking call contexts into account.
       *
       * `contentIn` describes the content of `arg` that can flow to `out` (if any), and
       * `contentOut` describes the content of `out` that it flows to (if any).
       */
      private predicate argumentValueFlowsThroughNoCtx(
        ArgumentNode arg, Node out, ContentOption contentIn, ContentOption contentOut
      ) {
        exists(DataFlowCall call, ReturnKindExt kind |
          argumentValueFlowsThroughNoCtx0(call, arg, kind, contentIn, contentOut) and
          out = kind.getAnOutNode(call)
        |
          contentIn.hasContent()
          or
          contentIn = TContentNone() and
          contentOut = TContentNone() and
          compatibleTypes(getErasedNodeTypeBound(arg), getErasedNodeTypeBound(out))
          or
          exists(Content fOut |
            contentIn = TContentNone() and
            contentOut.getContent() = fOut and
            compatibleTypes(getErasedNodeTypeBound(arg), fOut.getType())
          )
        )
      }

      /**
       * Holds if `arg` is the `i`th argument of `call` inside the callable
       * `enclosing`, and `arg` may flow through `call`.
       */
      pragma[noinline]
      private predicate argumentOfNoCtx(
        DataFlowCall call, int i, ArgumentNode arg, DataFlowCallable enclosing
      ) {
        arg.argumentOf(call, i) and
        argumentValueFlowsThroughNoCtx(arg, _, _, _) and
        enclosing = arg.getEnclosingCallable()
      }

      pragma[noinline]
      private predicate viableParamArgNoCtx0(
        int i, ArgumentNode arg, CallContext outercc, DataFlowCall call
      ) {
        exists(DataFlowCallable c | argumentOfNoCtx(call, i, arg, c) |
          (
            outercc = TAnyCallContext()
            or
            outercc = TSomeCall()
            or
            exists(DataFlowCall other | outercc = TSpecificCall(other) |
              recordDataFlowCallSite(other, c)
            )
          ) and
          not isUnreachableInCall(arg, outercc.(CallContextSpecificCall).getCall())
        )
      }

      pragma[noinline]
      private predicate viableParamArgNoCtx1(
        ParameterNode p, DataFlowCallable callable, int i, ArgumentNode arg, CallContext outercc,
        DataFlowCall call
      ) {
        viableParamArgNoCtx0(i, arg, outercc, call) and
        callable = resolveCall(call, outercc) and
        p.isParameterOf(callable, any(int j | j <= i and j >= i))
      }

      /**
       * Holds if `arg` is a possible argument to `p`, in the call `call`, and
       * `arg` may flow through `call`. The possible contexts before and after
       * entering the callable are `outercc` and `innercc`, respectively.
       */
      private predicate viableParamArgNoCtx(
        DataFlowCall call, ParameterNode p, ArgumentNode arg, CallContext outercc,
        CallContextCall innercc
      ) {
        exists(int i, DataFlowCallable callable |
          viableParamArgNoCtx1(p, callable, i, arg, outercc, call)
        |
          if recordDataFlowCallSite(call, callable)
          then innercc = TSpecificCall(call)
          else innercc = TSomeCall()
        )
      }

      private CallContextCall getAValidCallContextForParameter(ParameterNode p) {
        result = TSomeCall()
        or
        exists(DataFlowCall call, DataFlowCallable callable |
          result = TSpecificCall(call) and
          p.isParameterOf(callable, _) and
          recordDataFlowCallSite(call, callable)
        )
      }

      /**
       * Holds if `p` can flow to `node` in the same callable using only
       * value-preserving steps, in call context `cc`.
       *
       * `contentIn` describes the content of `p` that can flow to `node`
       * (if any), and `contentOut` describes the content of `node` that
       * it flows to (if any).
       *
       * This predicate is further restricted to parameters `p` that can either
       * flow through without taking call contexts into account, or that can
       * flow to a post-update node through which another parameter can flow
       * (again without taking call contexts into account).
       */
      private predicate parameterValueFlow(
        ParameterNode p, Node node, ContentOption contentIn, ContentOption contentOut,
        CallContextCall cc
      ) {
        parameterValueFlow0(p, node, contentIn, contentOut, cc) and
        (
          // normal flow through
          contentIn = TContentNone() and
          contentOut = TContentNone() and
          compatibleTypes(getErasedNodeTypeBound(p), getErasedNodeTypeBound(node))
          or
          // getter
          exists(Content fIn |
            contentIn.getContent() = fIn and
            contentOut = TContentNone() and
            compatibleTypes(fIn.getType(), getErasedNodeTypeBound(node))
          )
          or
          // setter
          exists(Content fOut |
            contentIn = TContentNone() and
            contentOut.getContent() = fOut and
            compatibleTypes(getErasedNodeTypeBound(p), fOut.getType()) and
            compatibleTypes(fOut.getContainerType(), getErasedNodeTypeBound(node))
          )
          or
          // getter+setter
          exists(Content fIn, Content fOut |
            contentIn.getContent() = fIn and
            contentOut.getContent() = fOut and
            compatibleTypes(fIn.getType(), fOut.getType()) and
            compatibleTypes(fOut.getContainerType(), getErasedNodeTypeBound(node))
          )
        )
      }

      pragma[nomagic]
      private predicate parameterValueFlow0(
        ParameterNode p, Node node, ContentOption contentIn, ContentOption contentOut,
        CallContextCall cc
      ) {
        p = node and
        (
          parameterValueFlowsThroughNoCtx(p, _, _, _)
          or
          exists(DataFlowCallable c, ParameterNode other, int pos |
            parameterValueFlowsThroughNoCtx(other, TParamUpdate(pos), _, _) and
            other.isParameterOf(c, _) and
            p.isParameterOf(c, pos)
          )
        ) and
        contentIn = TContentNone() and
        contentOut = TContentNone() and
        cc = getAValidCallContextForParameter(p)
        or
        // local flow
        exists(Node mid |
          parameterValueFlow(p, mid, contentIn, contentOut, cc) and
          simpleLocalFlowStep(mid, node) and
          not isUnreachableInCall(node, cc.(CallContextSpecificCall).getCall())
        )
        or
        // read
        exists(Node mid, Content f, ContentOption contentInMid, ContentOption contentOutMid |
          parameterValueFlow(p, mid, contentInMid, contentOutMid, cc) and
          readStep(mid, f, node) and
          not isUnreachableInCall(node, cc.(CallContextSpecificCall).getCall())
        |
          // value neither read nor stored prior to read
          contentInMid = TContentNone() and
          contentOutMid = TContentNone() and
          contentIn.getContent() = f and
          contentOut = TContentNone()
          or
          // value (possibly read and then) stored prior to read (same content)
          contentIn = contentInMid and
          contentOutMid.getContent() = f and
          contentOut = TContentNone()
        )
        or
        // store
        exists(Node mid, Content f |
          parameterValueFlow(p, mid, contentIn, TContentNone(), cc) and
          storeStep(mid, f, node) and
          contentOut.getContent() = f
        )
        or
        // flow through: no prior read or store
        exists(ArgumentNode arg |
          parameterValueFlowArg(p, arg, TContentNone(), TContentNone(), cc) and
          argumentValueFlowsThrough(_, arg, node, contentIn, contentOut, cc)
        )
        or
        // flow through: no read or store inside method
        exists(ArgumentNode arg |
          parameterValueFlowArg(p, arg, contentIn, contentOut, cc) and
          argumentValueFlowsThrough(_, arg, node, TContentNone(), TContentNone(), cc)
        )
        or
        // flow through: prior read (but no store); in this case the flow-through
        // method is not allowed to read, but is allowed to store
        exists(ArgumentNode arg |
          parameterValueFlowArg(p, arg, contentIn, TContentNone(), cc) and
          argumentValueFlowsThrough(_, arg, node, TContentNone(), contentOut, cc) and
          contentIn.hasContent()
        )
        or
        // flow through: possible prior read and definite prior store; in this case
        // the flow-through method is allowed to read same content back out
        exists(ArgumentNode arg, ContentOption contentOutBefore |
          parameterValueFlowArg(p, arg, contentIn, contentOutBefore, cc) and
          argumentValueFlowsThrough(_, arg, node, TContentSome(contentOutBefore.getContent()),
            contentOut, cc)
        )
      }

      pragma[noinline]
      private predicate parameterValueFlowArg(
        ParameterNode p, ArgumentNode arg, ContentOption contentIn, ContentOption contentOut,
        CallContextCall cc
      ) {
        parameterValueFlow(p, arg, contentIn, contentOut, cc) and
        argumentValueFlowsThroughNoCtx(arg, _, _, _)
      }

      pragma[noinline]
      private predicate parameterValueFlowsToPreUpdate(
        ParameterNode p, PostUpdateNode n, CallContext cc
      ) {
        parameterValueFlow(p, n.getPreUpdateNode(), TContentNone(), TContentNone(), cc)
      }

      pragma[noinline]
      private predicate parameterValueFlowsToPostUpdate(
        ParameterNode p, PostUpdateNode n, ContentOption contentIn, ContentOption contentOut,
        CallContext cc
      ) {
        parameterValueFlow(p, n, contentIn, contentOut, cc) and
        contentOut.hasContent()
      }

      /**
       * Holds if `p` can flow to a return node of kind `kind` in the same
       * callable using only value-preserving steps, in call context `cc`.
       *
       * `contentIn` describes the content of `p` that can flow to the return
       * node (if any), and `contentOut` describes the content of the return
       * node that it flows to (if any).
       */
      predicate parameterValueFlowsThrough(
        ParameterNode p, ReturnKindExt kind, ContentOption contentIn, ContentOption contentOut,
        CallContextCall cc
      ) {
        exists(ReturnNode ret |
          parameterValueFlow(p, ret, contentIn, contentOut, cc) and
          kind = TValueReturn(ret.getKind())
        )
        or
        exists(ParameterNode p2, int pos2, PostUpdateNode n |
          parameterValueFlowsToPostUpdate(p, n, contentIn, contentOut, cc) and
          parameterValueFlowsToPreUpdate(p2, n, cc) and
          p2.isParameterOf(_, pos2) and
          kind = TParamUpdate(pos2)
        )
      }

      pragma[nomagic]
      private predicate argumentValueFlowsThrough0(
        DataFlowCall call, ArgumentNode arg, ReturnKindExt kind, ContentOption contentIn,
        ContentOption contentOut, CallContext cc
      ) {
        exists(ParameterNode param, CallContext innercc |
          viableParamArgNoCtx(call, param, arg, cc, innercc) and
          parameterValueFlowsThrough(param, kind, contentIn, contentOut, innercc)
        )
      }

      /**
       * Holds if `arg` flows to `out` through a call using only value-preserving steps,
       * in call context cc.
       *
       * `contentIn` describes the content of `arg` that can flow to `out` (if any), and
       * `contentOut` describes the content of `out` that it flows to (if any).
       */
      predicate argumentValueFlowsThrough(
        DataFlowCall call, ArgumentNode arg, Node out, ContentOption contentIn,
        ContentOption contentOut, CallContext cc
      ) {
        exists(ReturnKindExt kind |
          argumentValueFlowsThrough0(call, arg, kind, contentIn, contentOut, cc) and
          out = kind.getAnOutNode(call) and
          not isUnreachableInCall(out, cc.(CallContextSpecificCall).getCall())
        |
          contentIn.hasContent()
          or
          contentIn = TContentNone() and
          contentOut = TContentNone() and
          compatibleTypes(getErasedNodeTypeBound(arg), getErasedNodeTypeBound(out))
          or
          exists(Content fOut |
            contentIn = TContentNone() and
            contentOut.getContent() = fOut and
            compatibleTypes(getErasedNodeTypeBound(arg), fOut.getType())
          )
        )
      }
    }

    /**
     * Holds if `p` can flow to the pre-update node associated with post-update
     * node `n`, in the same callable, using only value-preserving steps.
     */
    cached
    predicate parameterValueFlowsToPreUpdate(ParameterNode p, PostUpdateNode n) {
      FlowThrough::parameterValueFlowNoCtx(p, n.getPreUpdateNode(), TContentNone(), TContentNone())
    }

    /**
     * Holds if `p` can flow to a return node of kind `kind` in the same
     * callable using only value-preserving steps, in call context `cc`.
     */
    cached
    predicate parameterValueFlowsThrough(ParameterNode p, ReturnKindExt kind, CallContextCall cc) {
      FlowThrough::parameterValueFlowsThrough(p, kind, TContentNone(), TContentNone(), cc)
    }

    /**
     * Holds if `arg` flows to `out` through a call using only value-preserving steps,
     * in call context cc.
     */
    cached
    predicate argumentValueFlowsThrough(NodeExt arg, NodeExt out, CallContext cc) {
      FlowThrough::argumentValueFlowsThrough(_, arg.getNode(), out.getNode(), TContentNone(),
        TContentNone(), cc)
    }

    /*
     * Calculation of `predicate store(Node node1, Content f, Node node2)`:
     * There are four cases:
     * - The base case: A direct local assignment given by `storeStep`.
     * - A call to a method or constructor with two arguments, `arg1` and `arg2`,
     *   such that the call has the side-effect `arg2.f = arg1`.
     * - A call to a method that returns an object in which an argument has been
     *   stored.
     * - A reverse step through a read when the result of the read has been
     *   stored into. This handles cases like `x.f1.f2 = y`.
     * `argumentValueFlowsThrough` covers the second and third case.
     */

    /**
     * Holds if data can flow from `node1` to `node2` via a direct assignment to
     * `f` or via a call that acts as a setter.
     */
    cached
    predicate store(NodeExt node1, Content f, NodeExt node2) {
      storeStep(node1.getNode(), f, node2.getNode()) and readStep(_, f, _)
      or
      FlowThrough::argumentValueFlowsThrough(_, node1.getNode(), node2.getNode(), TContentNone(),
        TContentSome(f), _)
      or
      read(TNormalNode(node2.getNode().(PostUpdateNode).getPreUpdateNode()), f,
        TNormalNode(node1.getNode().(PostUpdateNode).getPreUpdateNode()))
      or
      node1 = TReadStoreNode(_, _, node2.getNode(), _, f)
    }

    /**
     * Holds if data can flow from `node1` to `node2` via a direct read of `f` or
     * via a getter.
     */
    cached
    predicate read(NodeExt node1, Content f, NodeExt node2) {
      readStep(node1.getNode(), f, node2.getNode())
      or
      FlowThrough::argumentValueFlowsThrough(_, node1.getNode(), node2.getNode(), TContentSome(f),
        TContentNone(), _)
      or
      node2 = TReadStoreNode(_, node1.getNode(), _, f, _)
    }

    /**
     * Holds if the call context `call` either improves virtual dispatch in
     * `callable` or if it allows us to prune unreachable nodes in `callable`.
     */
    cached
    predicate recordDataFlowCallSite(DataFlowCall call, DataFlowCallable callable) {
      reducedViableImplInCallContext(_, callable, call)
      or
      exists(Node n | n.getEnclosingCallable() = callable | isUnreachableInCall(n, call))
    }

    cached
    newtype TCallContext =
      TAnyCallContext() or
      TSpecificCall(DataFlowCall call) { recordDataFlowCallSite(call, _) } or
      TSomeCall() or
      TReturn(DataFlowCallable c, DataFlowCall call) { reducedViableImplInReturn(c, call) }

    cached
    newtype TReturnPosition =
      TReturnPosition0(DataFlowCallable c, ReturnKindExt kind) {
        exists(ReturnNodeExt ret |
          c = returnNodeGetEnclosingCallable(ret) and
          kind = ret.getKind()
        )
      }

    cached
    newtype TLocalFlowCallContext =
      TAnyLocalCall() or
      TSpecificLocalCall(DataFlowCall call) { isUnreachableInCall(_, call) }

    cached
    newtype TReturnKindExt =
      TValueReturn(ReturnKind kind) or
      TParamUpdate(int pos) { exists(ParameterNode p | p.isParameterOf(_, pos)) }

    cached
    newtype TNodeExt =
      TNormalNode(Node n) or
      TReadStoreNode(DataFlowCall call, Node node1, Node node2, Content f1, Content f2) {
        FlowThrough::argumentValueFlowsThrough(call, node1, node2, TContentSome(f1),
          TContentSome(f2), _)
      }
  }

  /**
   * An extended data flow node. Either a normal node, or an intermediate node
   * used to split up a read+store step through a call into first a read step
   * followed by a store step.
   *
   * This is purely an internal implementation detail.
   */
  class NodeExt extends TNodeExt {
    /** Gets the underlying (normal) node, if any. */
    Node getNode() { this = TNormalNode(result) }

    DataFlowType getErasedNodeTypeBound() {
      result = getErasedRepr(this.getNode().getTypeBound())
      or
      exists(Content f | this = TReadStoreNode(_, _, _, f, _) | result = f.getContainerType())
    }

    DataFlowCallable getEnclosingCallable() {
      result = this.getNode().getEnclosingCallable()
      or
      exists(Node n | this = TReadStoreNode(_, n, _, _, _) | result = n.getEnclosingCallable())
    }

    string toString() {
      exists(Node n | this = TNormalNode(n) | result = n.toString())
      or
      exists(DataFlowCall call | this = TReadStoreNode(call, _, _, _, _) |
        result = "(inside) " + call.toString()
      )
    }

    DataFlowLocation getLocation() {
      exists(Node n | this = TNormalNode(n) | result = n.getLocation())
      or
      exists(DataFlowCall call | this = TReadStoreNode(call, _, _, _, _) |
        result = call.getLocation()
      )
    }
  }

  /** Provides various `NodeExt` wrappers around corresponding normal nodes. */
  private module NodeExts {
    class ReturnNodeExtExt extends NodeExt {
      private ReturnNodeExt ret;

      ReturnNodeExtExt() { this = TNormalNode(ret) }

      override ReturnNodeExt getNode() { result = ret }
    }

    class ParameterNodeExt extends NodeExt {
      private ParameterNode p;

      ParameterNodeExt() { this = TNormalNode(p) }

      override ParameterNode getNode() { result = p }
    }

    class ArgumentNodeExt extends NodeExt {
      private ArgumentNode arg;

      ArgumentNodeExt() { this = TNormalNode(arg) }

      override ArgumentNode getNode() { result = arg }
    }

    /**
     * A `Node` at which a cast can occur such that the type should be checked.
     */
    class CastingNodeExt extends NodeExt {
      CastingNodeExt() {
        exists(Node n | n = this.getNode() |
          n instanceof ParameterNode or
          n instanceof CastNode or
          n instanceof OutNode or
          n.(PostUpdateNode).getPreUpdateNode() instanceof ArgumentNode
        )
      }
    }
  }

  import NodeExts

  private newtype TContentOption =
    TContentNone() or
    TContentSome(Content f)

  private class ContentOption extends TContentOption {
    Content getContent() { this = TContentSome(result) }

    predicate hasContent() { exists(this.getContent()) }

    string toString() {
      result = this.getContent().toString()
      or
      not this.hasContent() and
      result = ""
    }
  }

  /**
   * A call context to restrict the targets of virtual dispatch, prune local flow,
   * and match the call sites of flow into a method with flow out of a method.
   *
   * There are four cases:
   * - `TAnyCallContext()` : No restrictions on method flow.
   * - `TSpecificCall(DataFlowCall call)` : Flow entered through the
   *    given `call`. This call improves the set of viable
   *    dispatch targets for at least one method call in the current callable
   *    or helps prune unreachable nodes in the current callable.
   * - `TSomeCall()` : Flow entered through a parameter. The
   *    originating call does not improve the set of dispatch targets for any
   *    method call in the current callable and was therefore not recorded.
   * - `TReturn(Callable c, DataFlowCall call)` : Flow reached `call` from `c` and
   *    this dispatch target of `call` implies a reduced set of dispatch origins
   *    to which data may flow if it should reach a `return` statement.
   */
  abstract class CallContext extends TCallContext {
    abstract string toString();

    /** Holds if this call context is relevant for `callable`. */
    abstract predicate relevantFor(DataFlowCallable callable);
  }

  class CallContextAny extends CallContext, TAnyCallContext {
    override string toString() { result = "CcAny" }

    override predicate relevantFor(DataFlowCallable callable) { any() }
  }

  abstract class CallContextCall extends CallContext { }

  class CallContextSpecificCall extends CallContextCall, TSpecificCall {
    override string toString() {
      exists(DataFlowCall call | this = TSpecificCall(call) | result = "CcCall(" + call + ")")
    }

    override predicate relevantFor(DataFlowCallable callable) {
      recordDataFlowCallSite(getCall(), callable)
    }

    DataFlowCall getCall() { this = TSpecificCall(result) }
  }

  class CallContextSomeCall extends CallContextCall, TSomeCall {
    override string toString() { result = "CcSomeCall" }

    override predicate relevantFor(DataFlowCallable callable) {
      exists(ParameterNode p | p.getEnclosingCallable() = callable)
    }
  }

  class CallContextReturn extends CallContext, TReturn {
    override string toString() {
      exists(DataFlowCall call | this = TReturn(_, call) | result = "CcReturn(" + call + ")")
    }

    override predicate relevantFor(DataFlowCallable callable) {
      exists(DataFlowCall call | this = TReturn(_, call) and call.getEnclosingCallable() = callable)
    }
  }

  /**
   * A call context that is relevant for pruning local flow.
   */
  abstract class LocalCallContext extends TLocalFlowCallContext {
    abstract string toString();

    /** Holds if this call context is relevant for `callable`. */
    abstract predicate relevantFor(DataFlowCallable callable);
  }

  class LocalCallContextAny extends LocalCallContext, TAnyLocalCall {
    override string toString() { result = "LocalCcAny" }

    override predicate relevantFor(DataFlowCallable callable) { any() }
  }

  class LocalCallContextSpecificCall extends LocalCallContext, TSpecificLocalCall {
    LocalCallContextSpecificCall() { this = TSpecificLocalCall(call) }

    DataFlowCall call;

    DataFlowCall getCall() { result = call }

    override string toString() { result = "LocalCcCall(" + call + ")" }

    override predicate relevantFor(DataFlowCallable callable) { relevantLocalCCtx(call, callable) }
  }

  private predicate relevantLocalCCtx(DataFlowCall call, DataFlowCallable callable) {
    exists(Node n | n.getEnclosingCallable() = callable and isUnreachableInCall(n, call))
  }

  /**
   * Gets the local call context given the call context and the callable that
   * the contexts apply to.
   */
  LocalCallContext getLocalCallContext(CallContext ctx, DataFlowCallable callable) {
    ctx.relevantFor(callable) and
    if relevantLocalCCtx(ctx.(CallContextSpecificCall).getCall(), callable)
    then result.(LocalCallContextSpecificCall).getCall() = ctx.(CallContextSpecificCall).getCall()
    else result instanceof LocalCallContextAny
  }

  /**
   * A node from which flow can return to the caller. This is either a regular
   * `ReturnNode` or a `PostUpdateNode` corresponding to the value of a parameter.
   */
  class ReturnNodeExt extends Node {
    ReturnNodeExt() {
      this instanceof ReturnNode or
      parameterValueFlowsToPreUpdate(_, this)
    }

    /** Gets the kind of this returned value. */
    ReturnKindExt getKind() {
      result = TValueReturn(this.(ReturnNode).getKind())
      or
      exists(ParameterNode p, int pos |
        parameterValueFlowsToPreUpdate(p, this) and
        p.isParameterOf(_, pos) and
        result = TParamUpdate(pos)
      )
    }
  }

  /**
   * An extended return kind. A return kind describes how data can be returned
   * from a callable. This can either be through a returned value or an updated
   * parameter.
   */
  abstract class ReturnKindExt extends TReturnKindExt {
    /** Gets a textual representation of this return kind. */
    abstract string toString();

    /** Gets a node corresponding to data flow out of `call`. */
    abstract Node getAnOutNode(DataFlowCall call);
  }

  class ValueReturnKind extends ReturnKindExt, TValueReturn {
    private ReturnKind kind;

    ValueReturnKind() { this = TValueReturn(kind) }

    ReturnKind getKind() { result = kind }

    override string toString() { result = kind.toString() }

    override Node getAnOutNode(DataFlowCall call) { result = getAnOutNode(call, this.getKind()) }
  }

  class ParamUpdateReturnKind extends ReturnKindExt, TParamUpdate {
    private int pos;

    ParamUpdateReturnKind() { this = TParamUpdate(pos) }

    int getPosition() { result = pos }

    override string toString() { result = "param update " + pos }

    override PostUpdateNode getAnOutNode(DataFlowCall call) {
      exists(ArgumentNode arg |
        result.getPreUpdateNode() = arg and
        arg.argumentOf(call, this.getPosition())
      )
    }
  }

  /** A callable tagged with a relevant return kind. */
  class ReturnPosition extends TReturnPosition0 {
    private DataFlowCallable c;
    private ReturnKindExt kind;

    ReturnPosition() { this = TReturnPosition0(c, kind) }

    /** Gets the callable. */
    DataFlowCallable getCallable() { result = c }

    /** Gets the return kind. */
    ReturnKindExt getKind() { result = kind }

    /** Gets a textual representation of this return position. */
    string toString() { result = "[" + kind + "] " + c }
  }

  pragma[noinline]
  private DataFlowCallable returnNodeGetEnclosingCallable(ReturnNodeExt ret) {
    result = ret.getEnclosingCallable()
  }

  pragma[noinline]
  ReturnPosition getReturnPosition(ReturnNodeExtExt ret) {
    exists(ReturnNodeExt ret0 |
      ret0 = ret.getNode() and
      result = TReturnPosition0(returnNodeGetEnclosingCallable(ret0), ret0.getKind())
    )
  }

  bindingset[cc, callable]
  predicate resolveReturn(CallContext cc, DataFlowCallable callable, DataFlowCall call) {
    cc instanceof CallContextAny and callable = viableCallable(call)
    or
    exists(DataFlowCallable c0, DataFlowCall call0 |
      call0.getEnclosingCallable() = callable and
      cc = TReturn(c0, call0) and
      c0 = prunedViableImplInCallContextReverse(call0, call)
    )
  }

  bindingset[call, cc]
  DataFlowCallable resolveCall(DataFlowCall call, CallContext cc) {
    exists(DataFlowCall ctx | cc = TSpecificCall(ctx) |
      if reducedViableImplInCallContext(call, _, ctx)
      then result = prunedViableImplInCallContext(call, ctx)
      else result = viableCallable(call)
    )
    or
    result = viableCallable(call) and cc instanceof CallContextSomeCall
    or
    result = viableCallable(call) and cc instanceof CallContextAny
    or
    result = viableCallable(call) and cc instanceof CallContextReturn
  }

  newtype TSummary =
    TSummaryVal() or
    TSummaryTaint() or
    TSummaryReadVal(Content f) or
    TSummaryReadTaint(Content f) or
    TSummaryTaintStore(Content f)

  /**
   * A summary of flow through a callable. This can either be value-preserving
   * if no additional steps are used, taint-flow if at least one additional step
   * is used, or any one of those combined with a store or a read. Summaries
   * recorded at a return node are restricted to include at least one additional
   * step, as the value-based summaries are calculated independent of the
   * configuration.
   */
  class Summary extends TSummary {
    string toString() {
      result = "Val" and this = TSummaryVal()
      or
      result = "Taint" and this = TSummaryTaint()
      or
      exists(Content f |
        result = "ReadVal " + f.toString() and this = TSummaryReadVal(f)
        or
        result = "ReadTaint " + f.toString() and this = TSummaryReadTaint(f)
        or
        result = "TaintStore " + f.toString() and this = TSummaryTaintStore(f)
      )
    }

    /** Gets the summary that results from extending this with an additional step. */
    Summary additionalStep() {
      this = TSummaryVal() and result = TSummaryTaint()
      or
      this = TSummaryTaint() and result = TSummaryTaint()
      or
      exists(Content f | this = TSummaryReadVal(f) and result = TSummaryReadTaint(f))
      or
      exists(Content f | this = TSummaryReadTaint(f) and result = TSummaryReadTaint(f))
    }

    /** Gets the summary that results from extending this with a read. */
    Summary readStep(Content f) { this = TSummaryVal() and result = TSummaryReadVal(f) }

    /** Gets the summary that results from extending this with a store. */
    Summary storeStep(Content f) { this = TSummaryTaint() and result = TSummaryTaintStore(f) }

    /** Gets the summary that results from extending this with `step`. */
    bindingset[this, step]
    Summary compose(Summary step) {
      this = TSummaryVal() and result = step
      or
      this = TSummaryTaint() and
      (step = TSummaryTaint() or step = TSummaryTaintStore(_)) and
      result = step
      or
      exists(Content f |
        this = TSummaryReadVal(f) and step = TSummaryTaint() and result = TSummaryReadTaint(f)
      )
      or
      this = TSummaryReadTaint(_) and step = TSummaryTaint() and result = this
    }

    /** Holds if this summary does not include any taint steps. */
    predicate isPartial() {
      this = TSummaryVal() or
      this = TSummaryReadVal(_)
    }
  }

  pragma[noinline]
  DataFlowType getErasedNodeTypeBound(Node n) { result = getErasedRepr(n.getTypeBound()) }
}
