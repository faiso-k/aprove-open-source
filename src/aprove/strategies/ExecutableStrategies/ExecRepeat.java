package aprove.strategies.ExecutableStrategies;

import java.util.*;

import aprove.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.UserStrategies.*;

public class ExecRepeat extends ExecutableStrategy {

    private ExecutableStrategy exStr;
    private final UserStrategy str;
    private final boolean breadth;
    private final BasicObligationNode pos;
    private final Integer upper;  // an integer >= lower, or null for no limit
    private final int lower;      // an integer >= 0

    public ExecRepeat(ExecutableStrategy exStr, UserStrategy str, BasicObligationNode pos, int lower, Integer upper, boolean breadth, RuntimeInformation rti) {
        super(rti);
        this.exStr = exStr;
        this.pos = pos;
        this.str = str;
        this.breadth = breadth;
        this.upper = upper;
        this.lower = lower;
        if (Globals.useAssertions) {
            assert (lower >= 0);
            assert (upper == null || lower <= upper);
        }
    }

    public ExecRepeat(UserStrategy str, BasicObligationNode pos,
            int lower, Integer upper, boolean breadth,
            RuntimeInformation rti) {
        this(str.getExecutableStrategy(pos, rti), str, pos, lower, upper, breadth, rti);
    }

    @Override
    ExecutableStrategy exec() {
        // Have we reached our upper limit? If so, we're all done.
        if (this.upper != null && this.upper.intValue() == 0) {
            return new Success(this.pos);
        }

        // As long as our inner strategy is still working, work it.
        if (!this.exStr.isNormal()) {
            ExecutableStrategy newEx = this.exStr.exec();
            if (newEx == null) {
                // Hmm, nothing to see here. Sleep and call us later.
                return null;
            } else {
                this.exStr = newEx;
                // Okay, something changed. Call us again Real Soon so we can evaluate again.
                return this;
            }

        // Otherwise, our inner strategy is done, we have to do something.
        } else {
            if (this.exStr.isFail()) {
                if (this.lower == 0) {
                    // If we failed but ran often enough, it's a success on the last ObligationNode we applied on.
                    return new Success(this.pos);
                } else {
                    return new Fail("Repeat() did not reach lower bound", (Fail) this.exStr);
                }

            // Hmm, success. Produce a new instance of ourself on the new problem(s).
            } else {
                Success succ = (Success) this.exStr;
                List<BasicObligationNode> positions = succ.getPositions();
                int lower = Math.max(0, this.lower-1);
                // no check for upper on negative values, as upper >= lower > 0;
                Integer upper = this.upper == null ? null : this.upper - 1;
                UserStrategy repeatStr = new Repeat(this.str, lower, upper, this.breadth);

                // Okay, now let's see...
                if (positions.size() == 1) {
                    return repeatStr.getExecutableStrategy(positions.get(0), this.rti);
                }else if (positions.size() == 0) {
                    // Nothing left to do? Okay, then we're Success(), too.
                    return succ;
                }

                // Hmm. Many results. Set up several sub-strategies, then wrap them into the appropriate ExecAll()
                List<ExecutableStrategy> exStrs = new ArrayList<ExecutableStrategy>(positions.size());
                for (BasicObligationNode pos : positions) {
                    exStrs.add(repeatStr.getExecutableStrategy(pos, this.rti));
                }
                return this.breadth ? new ExecAllParallel(exStrs, this.rti) : new ExecAllSequential(exStrs, this.rti);
            }
        }
    }

    @Override
    void stop(String reason) {
        this.exStr.stop(reason);
    }

    @Override
    public String toString() {
        return "ERepeat*_"+(this.breadth ? "B" : "D")+"("+this.exStr+", "+this.str+", "+"someObl"+")";
    }

}
