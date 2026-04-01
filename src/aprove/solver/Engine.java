package aprove.solver;

import java.math.*;

import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public abstract class Engine implements SATCheckerFactory {

    // TODO maybe move this one to SatEngine
    @Override
    public SATChecker getSATChecker() {
        throw new UnsupportedOperationException();
    }
    // Does this engine support full Diophantine Logic?
    public boolean supportsDL() {
        return false;
    }

    /**
     * Interesting for those engines that can be used for finding Polos,
     * Matros, ...
     *
     * @param ranges
     * @return
     */
    public SearchAlgorithm getSearchAlgorithm(final DefaultValueMap<String, BigInteger> ranges) {
        throw new UnsupportedOperationException("This kind of engine is not applicable for " +
                "solving SimplePolyConstraints/Diophantine constraints.");
    }

    @Override
    public String toString() {
        return this.getClass().getSimpleName();
    }
}