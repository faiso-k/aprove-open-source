package aprove.strategies.ExecutableStrategies;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.oldframework.Logic.*;


public abstract class ExecCombine extends ExecutableStrategy {

    protected Combine.Options options;
    protected final List<ExecutableStrategy> strategies;
    protected final Set<BasicObligationNode> positions;
    protected BasicObligationNode pos;

    public ExecCombine(List<ExecutableStrategy> strategies, RuntimeInformation rti, Combine.Options options) {
        super(rti);
        this.options = options;
        this.strategies = new LinkedList<ExecutableStrategy>(strategies);
        this.positions = new LinkedHashSet<BasicObligationNode>();
    }

    protected boolean canBeAborted() {
        TruthValue currentRes = getCurrentResult();
        return currentRes != null && currentRes.isOptimal();
    }

    protected TruthValue getCurrentResult() {
        if (pos != null) {
            return pos.getTruthValue();
        } else {
            return null;
        }
    }
}
