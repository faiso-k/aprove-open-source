package aprove.strategies.ExecutableStrategies;

import aprove.prooftree.Obligations.*;
import aprove.strategies.UserStrategies.*;

/**
 * A small, basic implementation that just wraps another ExecutableStrategy.
 *
 * Used when you want to override certain functionality,
 * or just need a EYourName(...) to appear in strategy output.
 */
public class ExecSimple extends ExecutableStrategy {

    private final String name;

    protected ExecutableStrategy exStr;
    private String stopReason = null;

    public ExecSimple(String name, ExecutableStrategy exStr, RuntimeInformation rti) {
        super(rti);
        this.name = name;
        this.exStr = exStr;
    }

    public ExecSimple(String name, UserStrategy str, BasicObligationNode pos, RuntimeInformation rti) {
        this(name, str.getExecutableStrategy(pos, rti), rti);
    }

    @Override
    ExecutableStrategy exec() {
        if (this.exStr.isNormal()) {
            return this.exStr;
        }

        if (this.stopReason != null) {
            this.exStr.stop(this.stopReason);
            return new Fail(this.stopReason);
        }

        ExecutableStrategy newEx = this.exStr.exec();
        if (newEx == null) {
            return null;
        } else {
            this.exStr = newEx;
            return this;
        }
    }

    /**
     * Call this method to stop execution cleanly and return fail
     * at the next opportunity.
     *
     * Contrary to stop() and exec(), this method may be called from any thread,
     * any time.
     */
    protected void asyncStop(String reason) {
        if (reason == null) {
            throw new NullPointerException("reason");
        }
        this.stopReason = reason;
        // The following line synchronizes with the machine thread,
        // so we do not need explicit volatile/synchronization for stopReason.
        this.rti.execute();
    }

    @Override
    void stop(String reason) {
        this.exStr.stop(reason);
    }

    @Override
    public String toString() {
        return this.name + "("+this.exStr+")";
    }


}
