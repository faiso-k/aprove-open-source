package aprove.verification.dpframework.Heuristics.Processors;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;

/**
 * Heuristics to decide which strategy to use for the given input obligation.
 */
@NoParams
public class RunDefaultStrategyForObligation extends Processor.ProcessorSkeleton {

    @Override
    public Result process(final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException {
        final String stratName = obl.getStrategyName();
        if (stratName == null) {
            throw new RuntimeException("Do not know which strategy to select for obligations of type "
                + obl.getClass().getSimpleName() + "!");
        }
        return ResultFactory.justANewStrategy(new VariableStrategy(stratName).getExecutableStrategy(oblNode, rti));
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return true;
    }
}
