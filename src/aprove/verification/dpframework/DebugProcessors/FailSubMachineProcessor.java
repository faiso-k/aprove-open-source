package aprove.verification.dpframework.DebugProcessors;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Processor.*;

/**
 * Debug processor to show the extent to which our processors
 * are instantiated only once per occurrence in a strategy,
 * also for submachines.
 *
 * @author Carsten Fuhs
 */
public class FailSubMachineProcessor extends ProcessorSkeleton {

    /**
     * The strategy for the subMachine.
     */
    private final String strategy;

    @ParamsViaArgumentObject
    public FailSubMachineProcessor(Arguments arguments) {
        this.strategy = arguments.strategy;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return true;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode,
            Abortion aborter, RuntimeInformation rti) throws AbortionException {

        BasicObligationNode subNode = new BasicObligationNode(obl);
        UserStrategy userStrategy = new VariableStrategy(this.strategy);
        StrategyExecutionHandle handle =
            Machine.theMachine.startSubMachine(
                userStrategy,
                rti.getProgram(),
                subNode,
                null,
                aborter.getClocks(),
                false);

        HandleChecker.check(handle, aborter);

        // okay, we have the result after the strategy
        ExecutableStrategy result = handle.getResult();
        return ResultFactory.unsuccessful("Definitely Maybe.");
    }

    public static class Arguments {
        /** Sub-strategy to be invoked. */
        public String strategy = "fail";
    }
}
