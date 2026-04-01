package aprove.verification.oldframework.Bytecode.Processors.ToMethodSummary;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.JBCProblem.*;
import aprove.verification.oldframework.Bytecode.Processors.ToComplexity.*;
import aprove.verification.oldframework.Bytecode.Processors.ToSCC.*;
import aprove.verification.oldframework.CostEquationSystem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.WeightedIntTrs.*;

public class JBCGraphEdgesToIntTrsForMethodSummaryProcessor extends JBCGraphEdgesToIntTrsProcessor {

    @ParamsViaArgumentObject
    public JBCGraphEdgesToIntTrsForMethodSummaryProcessor(Arguments args) {
        super(args);
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof GraphEdgesToComplexityForMethodSummary;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        GraphEdgesToComplexityForMethodSummary edges = (GraphEdgesToComplexityForMethodSummary) obl;
        UsedFieldsAnalysis ufa = getUfa(edges.getSCCAnnotations());

        RulesTransformer rulesTransformer = new RulesTransformer(edges, ufa);
        TRSFunctionApplication start = rulesTransformer.getStart(true, false);
        String mName = edges.getStartNode().getState().getTerminationGraph().getStartGraph().getStartNode().getState().getCurrentStackFrame().getMethod().getName();

        AbstractWeightedIntTermSystem<?> newObl;
        Implication imp;
        switch(args.targetSystem) {
        case IntTrs: {
            Set<WeightedRule> rules = rulesTransformer.transformEdges(x -> x.filterUnneededConditions().toWeightedRules());
            newObl = new WeightedIntTrsForMethodSummary(rules, start, mName, edges.getTask(), computeStartTermArgMap(edges, rulesTransformer.getStart(false, false)));
            if (args.propagateLowerBounds()) {
                imp = SoundUpperUnsoundLowerBound.forConcreteBounds();
            } else {
                imp = UpperBound.forConcreteBounds();
            }
            break;
        }
        case CES: {
            Set<CostEquation> equations = rulesTransformer.transformEdges(x -> x.filterUnneededConditions().toCostEquation());
            newObl = new CESForMethodSummary(mName, start, equations, edges.getTask(), computeStartTermArgMap(edges, rulesTransformer.getStart(false, false)));
            imp = SoundUpperUnsoundLowerBound.forConcreteBounds();
            break;
        }
        default:
            assert false;
            return null;
        }

        return ResultFactory.proved(newObl, BothBounds.create(), new JBCGraphEdgesToCpxIntTrsProof(newObl.getRules().size(), edges.getEdgesToEncode().size()));
    }

    private Map<Integer, ComplexityGoalTerm> computeStartTermArgMap(JBCGraphEdgesComplexityProblem edges,
            TRSFunctionApplication start) {
        Map<Integer, ComplexityGoalTerm> startTermArgMap = new LinkedHashMap<>();
        List<TRSTerm> args = start.getArguments();
        for (int i=0; i<args.size(); i++) {
            TRSTerm t = args.get(i);
            if (t instanceof TRSVariable) {
                final int ind = i;
                ComplexityGoalTerm.fromString(((TRSVariable)t).getName()).ifPresent(
                    term -> startTermArgMap.put(ind, term)
                );
            }
        }
        return startTermArgMap;
    }

}
