package aprove.verification.dpframework.Heuristics.Processors;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.Heuristics.*;

@AcceptsStrategies(value = {"s1", "s2"}, optional = true)
public class IfHeuristic extends Processor.ProcessorSkeleton {

    private final Condition cond;
    private final UserStrategy sub1;
    private final UserStrategy sub2;

    @ParamsViaArgumentObject
    public IfHeuristic(Arguments arguments) {
        this.cond = arguments.condition;
        this.sub1 = arguments.s1;
        this.sub2 = arguments.s2;
        if (this.sub1 == null) {
            throw new IllegalArgumentException("No strategy given!");
        }
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        UserStrategy result;
        if (this.cond.check(obl, aborter, rti)) {
            result = this.sub1;
        } else {
            result = this.sub2;
        }
        if (result == null) {
            return ResultFactory.unsuccessful();
        }
        ExecutableStrategy execStrategy = result.getExecutableStrategy(oblNode, rti);
        return ResultFactory.justANewStrategy(execStrategy);
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return this.cond.isApplicable(obl);
    }

    public static class Arguments {
        public Condition condition;
        public UserStrategy s1 = null;
        public UserStrategy s2 = null;

        public void setSub1(String name) {
            this.s1 = new VariableStrategy(name);
        }

        public void setSub2(String name) {
            this.s2 = new VariableStrategy(name);
        }
    }
}
