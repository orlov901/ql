import csharp
import DataFlow
import semmle.code.csharp.dataflow.internal.DataFlowPrivate

class ConfigAny extends Configuration {
  ConfigAny() { this = "ConfigAny" }

  override predicate isSource(Node source) {
    source instanceof PostUpdateNode
    implies
    source.asExpr() = any(Expr e | e instanceof ObjectCreation or e instanceof ArrayCreation)
  }

  override predicate isSink(Node sink) {
    sink instanceof PostUpdateNode
    implies
    sink.asExpr() = any(Expr e | e instanceof ObjectCreation or e instanceof ArrayCreation)
  }
}

query predicate edges(PathNode a, PathNode b) { a.getASuccessor() = b }
