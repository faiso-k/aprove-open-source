/*
 * Created on 16.07.2004
 *

 */
package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.input.Programs.strategy_OLD.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Terms.*;


/**
 * @author rabe
 *
 */
public class TheoremProverProcessorFactory {

    /**
     * Returns subtree for induction by data structure
     * @param inductionVariables Map of induction variables
     * @return Processor subtree for induction by data structure
     */
    public static UserStrategy getInductionByDataStructure(AlgebraVariable inductionVariable, boolean pure) {

        String name;
        if (inductionVariable != null) {
            name = inductionVariable.getName();
        } else {
            name = "";
        }
        Processor proc = new InductionByDataStructureProcessor(name);
        ProcessorStrategy processorStrategy = new ProcessorStrategy(proc);

        if( pure ) {
            return processorStrategy;
        } else {
            return new Sequence(processorStrategy, new Repeat(new ProcessorStrategy(new SymbolicEvaluationUnderHypothesisProcessor())));
        }
    }

    public static UserStrategy getInductionByAlgorithm(AlgebraFunctionApplication inductionAlgorithm, boolean pure) {
        InductionByAlgorithmProcessor.Arguments arguments = new InductionByAlgorithmProcessor.Arguments();
        arguments.inductionAlgorithm = TheoremProverProcessorFactory.toStringOr(inductionAlgorithm, "");
        Processor proc = new InductionByAlgorithmProcessor(arguments);
        ProcessorStrategy processorStrategy = new ProcessorStrategy(proc);

        if( pure ) {
            return processorStrategy;
        } else {
            return new Sequence(processorStrategy, new Repeat(new ProcessorStrategy(new SymbolicEvaluationUnderHypothesisProcessor())));
        }
    }

    public static UserStrategy getInductionByAlgorithmCoverSet(
            List<Position> positions,
            Boolean skipLAHypothesisHeuristic,
            Boolean evaluateHypothesis,
            boolean pure) {

        InductionByAlgorithmCoverSetProcessor.Arguments args = new InductionByAlgorithmCoverSetProcessor.Arguments();
        args.positions = TheoremProverProcessorFactory.toStringOr(positions, "[]");
        args.skipLAHypothesisHeuristic = skipLAHypothesisHeuristic;
        args.evaluateHypothesis = evaluateHypothesis;
        Processor proc = new InductionByAlgorithmCoverSetProcessor(args);
        ProcessorStrategy processorStrategy = new ProcessorStrategy(proc);

        if( pure ) {
            return processorStrategy;
        }
        else {
            return new Sequence(processorStrategy, new Repeat(new ProcessorStrategy(new SymbolicOutermostLAEvaluationUnderHypothesisProcessor(skipLAHypothesisHeuristic))));
        }
    }

    public static UserStrategy getINDFMLHeuristicProcessor(
            String techniques,
            Boolean useCoverSets,
            Boolean merging,
            Boolean skipLAHypothesisHeuristic,
            Boolean evaluateHypothesis) {

        INDFMLHeuristicProcessor.Arguments args = new INDFMLHeuristicProcessor.Arguments();
        args.techniques = techniques;
        args.useCoverSets = useCoverSets;
        args.merging = merging;
        args.skipLAHypothesisHeuristic = skipLAHypothesisHeuristic;
        args.evaluateHypothesis = evaluateHypothesis;
        Processor proc = new INDFMLHeuristicProcessor(args);

        return new ProcessorStrategy(proc);
    }

    public static UserStrategy getRipplingProcessor(String direction) {
        Processor proc = new RipplingProcessor(direction);
        return new ProcessorStrategy(proc);
    }

    public static UserStrategy getLemmaApplicationProcessor(LemmaApplicationVisitors mode, Parameter orderConfig, int minimalHeuristic, int sequenceLength) {
        throw new UnsupportedOperationException("Fix me!");
//
//          try{
//
//              if (orderConfig == null){
//                  orderConfig = new Parameter();
//              }
//              else{
//                // replace Link seems not to be safe
//                // because the isDefined flag might not be set otherwise
//                orderConfig.removeKey("MinimalHeuristic");
//                orderConfig.addLink("MinimalHeuristic", ((Integer)minimalHeuristic).toString(), null);
//              }
//
//            orderConfig.removeKey("Mode");
//            orderConfig.addLink("Mode", mode.toString(), null);
//
//            if (mode == LemmaApplicationVisitors.MAX){
//                orderConfig.removeKey("SequenceLength");
//                orderConfig.addLink("SequenceLength", ((Integer)sequenceLength).toString(), null);
//            }
//
//            Pair<Processor,Parameter> pair = ParameterManager.getProcessorAndParameter("LemmaApplication", orderConfig);
//
//               ProcessorStrategy processorStrategy = new ProcessorStrategy(pair.getKey());
//            processorStrategy.setParameterForRepresentation(orderConfig);
//
//            return processorStrategy;
//
//             }catch(Exception e) {
//            e.printStackTrace();
//        }
//
//        return null;
    }

    public static UserStrategy getSymbolicEvalutionUnderHypothesisProcessor() {
        return new ProcessorStrategy(new SymbolicEvaluationUnderHypothesisProcessor());
    }

    public static UserStrategy getSymbolicOutermostLAEvaluationUnderHypothesisProcessor(Boolean hypothesesOutermostApplication) {
        Processor proc = new SymbolicOutermostLAEvaluationUnderHypothesisProcessor(hypothesesOutermostApplication);
        return new ProcessorStrategy(proc);
    }

    private static String toStringOr(Object objOrNull, String ifNull) {
        if (objOrNull != null) {
            return objOrNull.toString();
        } else {
            return ifNull;
        }
    }
}
