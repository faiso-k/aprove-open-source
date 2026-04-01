/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.strategies.Abortions.*;

public class StrategyLevel {

    private final InfRule[] strategy;
    private final boolean repeat;
    private final String name;

    public StrategyLevel(String name, InfRule[] strategy, boolean repeat) {
        this.name = name;
        this.strategy = strategy;
        this.repeat = repeat;
    }

    public InfRule[] getStrategy() {
        return this.strategy;
    }

    public boolean isRepeat() {
        return this.repeat;
    }

    @Override
    public String toString() {
        return this.name;
    }

    public void prepare(List<Implication> cs, InductionCalculusProof proof, Abortion aborter) throws AbortionException {
    }

}
