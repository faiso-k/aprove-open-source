package aprove.verification.dpframework.Heuristics.Processors;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.Parameters.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.DPProblem.Processors.*;

public class OldNonTermHeuristic extends Processor.ProcessorSkeleton {

    /**
     * maximal number of narrowings with one rule
     */
    private final int totalLimit;
    /**
     * maximal number of narrowings to the left with one rule (to be more precise with rule^{-1})
     */
    private final int leftLimit;
    /**
     * maximal number of narrowings to the right with one rule
     */
    private final int rightLimit;

    private final boolean reverse;

    private final NonTerminationProcessor.Heuristic heuristic;

    private UserStrategy strategy = null;

    @ParamsViaArgumentObject
    public OldNonTermHeuristic(Arguments arguments) {
        this.leftLimit = arguments.leftLimit;
        this.rightLimit = arguments.rightLimit;
        this.totalLimit = arguments.totalLimit;
        this.reverse = arguments.reverse;
        this.heuristic = arguments.heuristic;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return true;
    }

    private UserStrategy getStrategy() {
        if (this.strategy == null) {
            this.strategy = StrategyTranslator.strategyFragment(
                    "Maybe(QDPQReduction[KeepMinimality = False]):"+
                    (this.reverse ? "Maybe(QDPMNOC[Reversed = True, TestDepth = 0]):" : "")+
                    "QDPLoopFinder[TotalLimit = "+this.totalLimit+", LeftLimit = "+this.leftLimit+
                    ", RightLimit = "+this.rightLimit+", Heuristic = "+this.heuristic+"]");
        }
        return this.strategy;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        return ResultFactory.justANewStrategy(this.getStrategy().getExecutableStrategy(oblNode, rti));
    }

    public static class Arguments{
        public int leftLimit;
        public int rightLimit;
        public int totalLimit;
        public boolean reverse = true;
        public NonTerminationProcessor.Heuristic heuristic = NonTerminationProcessor.Heuristic.NORMAL;
    }

}
