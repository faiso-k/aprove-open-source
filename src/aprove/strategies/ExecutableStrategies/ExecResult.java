package aprove.strategies.ExecutableStrategies;

import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.*;

/**
 * When executed, attaches a result to the proof tree.
 *
 * Execution then continues with the strategy contained in the result.
 *
 * This class is useful if you have multiple results, and want to introduce
 * some of them to the proof tree "later", e.g. when calculations on previous
 * results failed.
 *
 * Note that you are not permitted to attach nodes to the main proof tree
 * outside of the Machine thread, i.e. inside a Processor. Use this class instead!
 *
 * For an example, see {@link aprove.verification.dpframework.HaskellProblem.Processors.NarrowingProcessor}
 */
public class ExecResult extends ExecutableStrategy {

    private final BasicObligationNode obl;
    private final Result result;

    public ExecResult(final RuntimeInformation rti, final BasicObligationNode obl, final Result result) {
        super(rti);
        this.obl = obl;
        this.result = result;
    }

    // Note: This method MUST NEVER return null, see ExecProcessorStrategy.finish()
    @Override
    ExecutableStrategy exec() {
        // evalulate result
        final ObligationNodeChild child = this.result.getObligationChild();
        if (child != null) {
            this.obl.addTechnique(child, this.rti.checkProofs());
        }
        final ExecutableStrategy strategy = this.result.getStrategy();
        if (strategy == null) {
            System.err.println("Result contained null strategy! Very bad!");
            return new Fail("null result");
        }
        return strategy;
    }

    @Override
    void stop(final String reason) {
        // Nothing to do.
    }

    @Override
    public String toString() {
        return "EResult(" + this.obl + ", "+ this.result + ")";
    }

}
