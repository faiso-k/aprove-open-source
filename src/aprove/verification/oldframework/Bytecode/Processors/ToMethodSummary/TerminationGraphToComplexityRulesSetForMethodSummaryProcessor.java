package aprove.verification.oldframework.Bytecode.Processors.ToMethodSummary;

import java.util.Set;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.JBCProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Processors.ToComplexity.*;
import aprove.verification.oldframework.Bytecode.Processors.ToSCC.*;

public class TerminationGraphToComplexityRulesSetForMethodSummaryProcessor
        extends TerminationGraphToComplexityRuleSetProcessor {

    @ParamsViaArgumentObject
    public TerminationGraphToComplexityRulesSetForMethodSummaryProcessor(Arguments args) {
        super(args);
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof TerminationGraphForMethodSummary;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        TerminationGraphForMethodSummary termGraph = (TerminationGraphForMethodSummary) obl;
        return processInternal(termGraph, termGraph.getTask().getGoal(), termGraph.getTask().getGoalTerm());
    }

    @Override
    protected void onEdgesEmpty(JBCTerminationGraphProblem obl) {
        ((TerminationGraphForMethodSummary) obl).getTask().finish(SimplePolynomial.ONE);
    }

    @Override
    protected JBCGraphEdgesComplexityProblem getNewObligation(JBCGraph termGraph, Node startNode, Set<Edge> edges,
            SCCAnnotations sccAnnotations, JBCTerminationGraphProblem obl) {
        MethodSummaryBuilder.Task methodSummaryTask = ((TerminationGraphForMethodSummary) obl).getTask();
        return new GraphEdgesToComplexityForMethodSummary(termGraph, startNode, edges, sccAnnotations, obl.getRelevanceInfo(), methodSummaryTask);
    }

}
