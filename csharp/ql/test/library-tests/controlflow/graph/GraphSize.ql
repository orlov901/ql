import csharp
import Common

select count(SourceControlFlowNode node, SourceControlFlowNode successor,
    ControlFlow::SuccessorType t | successor = node.getASuccessorByType(t))
