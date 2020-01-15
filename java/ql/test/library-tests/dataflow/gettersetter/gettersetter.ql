import java
import semmle.code.java.dataflow.internal.DataFlowImplCommon
import semmle.code.java.dataflow.internal.DataFlowImplSpecific::Public
import semmle.code.java.dataflow.internal.DataFlowImplSpecific::Private

from NodeExt n1, Content f, NodeExt n2, string k
where
  read(n1, f, n2) and k = "Read"
  or
  store(n1, f, n2) and k = "Store"
select k, n1, n2, f
