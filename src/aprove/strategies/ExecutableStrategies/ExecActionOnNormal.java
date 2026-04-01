package aprove.strategies.ExecutableStrategies;

import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.strategies.UserStrategies.*;

/**
 * Executable strategy to provide feedback for machine learning techniques.
 * After the child strategy is either Fail or Success provide feedback via
 * triggerAction().
 */
public abstract class ExecActionOnNormal extends ExecutableStrategy {

    private ExecutableStrategy exStr;
    private final BasicObligationNode workingCopy;

    public ExecActionOnNormal(UserStrategy str, BasicObligationNode obl,
            RuntimeInformation rti) {
        super(rti);
        this.workingCopy =
            Options.strategyWorksOnCopies ? new BasicObligationNode(obl) : obl;
        this.exStr = str.getExecutableStrategy(this.workingCopy, rti);
    }

    @Override
    ExecutableStrategy exec() {
        if (this.exStr.isNormal()) {
            this.triggerAction(!this.exStr.isFail());
            return this.exStr;
        } else {
            ExecutableStrategy newEx = this.exStr.exec();
            if (newEx == null) {
                return null;
            } else {
                this.exStr = newEx;
                return this;
            }
        }
    }

    @Override
    void stop(String reason) {
        this.exStr.stop(reason);
    }

    @Override
    public String toString() {
        String oblR = "someObl"; // pos.getRepresentation();
        return "EActionOnNormal(" + oblR + ", " + this.exStr + ")";
    }

    /**
     * Called by exec() when the child strategy is either successful or fails.
     * @param successful
     */
    protected abstract void triggerAction(boolean successful);
}
