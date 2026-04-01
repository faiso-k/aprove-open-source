package aprove.verification.dpframework;

import aprove.prooftree.Obligations.*;
import aprove.strategies.ExecutableStrategies.*;

public interface Result  {

    /**
     * returns the strategy that represents the strategy-result
     * of a processor
     */
    ExecutableStrategy getStrategy();

    /**
     * returns the obligation that should be added into the
     * obligation tree. Maybe null for failed processors or
     * strategy processors.
     * @return
     */
    ObligationNodeChild getObligationChild();

    /**
     * asserts that the strategy result is a Success at a single position
     * and returns that position.
     *
     * A useful shorthand for whenever you get a Result from a processor
     * but need the one ObligationNode it produced, as long as you are sure
     * that's what it did.
     */
    BasicObligationNode getSuccessPosition();

}
