package aprove.verification.oldframework.Bytecode.Processors.ToMethodSummary;

import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.JBCProblem.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Processors.ToComplexity.*;
import aprove.verification.oldframework.Bytecode.Processors.ToMethodSummary.MethodSummaryBuilder.*;
import aprove.verification.oldframework.Bytecode.Processors.ToSCC.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class GraphEdgesToComplexityForMethodSummary extends JBCGraphEdgesComplexityProblem {

    private MethodSummaryBuilder.Task task;

    public GraphEdgesToComplexityForMethodSummary(JBCGraph fullG, Node startN, Set<Edge> edges, SCCAnnotations sccAnn,
            CollectionMap<Node, AbstractVariableReference> relevantRefs,
            Task task) {
        super(fullG, startN, edges, sccAnn, relevantRefs, ConsideredPaths.ALL_PATHS_FROM_START);
        this.task = task;
    }

    @Override
    public String export(Export_Util o) {
        return task + o.linebreak() + super.export(o);
    }

    public MethodSummaryBuilder.Task getTask() {
        return task;
    }
}
