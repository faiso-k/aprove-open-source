package aprove.strategies.ExecutableStrategies;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.strategies.UserStrategies.*;

/**
 * Execute a first that starts one single strategy. If the strategy successes we use its result
 * further. If the strategy fails we take the next one.
 * If run with low priority we only start new strategies if the PrioQ has a free slot. Otherwise
 * we result in a fail.
 */
public class ExecFirst extends ExecutableStrategy {

    private ExecutableStrategy executedStr;
    private final ListIterator<UserStrategy> remStrs; // the remaining strategies that need to be processed
    private final List<UserStrategy> allStrats; // only needed for output;
    private final BasicObligationNode obl; // the obligation that we want to simplify
    private BasicObligationNode workingCopy; // the obligation on that we currently work (may be obl, depending on workOnCopies)
    private final boolean workOnCopies;


    private final boolean useExecStrats;
    private final List<ExecutableStrategy> allExecStrats;
    private final ListIterator<ExecutableStrategy> remExecStrs;

    public ExecFirst(List<UserStrategy> strategies, BasicObligationNode obl, RuntimeInformation rti) {
        super(rti);
        this.allStrats = strategies;
        this.workOnCopies = Options.strategyWorksOnCopies;
        this.executedStr = Fail.Fail;
        this.remStrs = strategies.listIterator();
        this.obl = obl;

        this.useExecStrats = false;
        this.allExecStrats = null;
        this.remExecStrs = null;
    }

    /**
     * creates an executable first strategy, with executable strategies inside.
     * This can be used to run on other different positions.
     * @param execStrs The strategies to execute
     * @param obl The obligation to back up to
     * @param rti RuntimeInformation
     */
    public static ExecFirst createFromExec(List<ExecutableStrategy> execStrs, BasicObligationNode obl, RuntimeInformation rti) {
        return new ExecFirst(obl, rti, execStrs);
    }

    private ExecFirst(BasicObligationNode obl, RuntimeInformation rti, List<ExecutableStrategy> execStrategies) {
        super(rti);

        this.allStrats = Collections.emptyList();
        this.workOnCopies = false;
        this.executedStr = Fail.Fail;
        this.remStrs = this.allStrats.listIterator();
        this.obl = obl;

        this.useExecStrats = true;
        this.allExecStrats = execStrategies;
        this.remExecStrs = this.allExecStrats.listIterator();
    }


    @Override
    ExecutableStrategy exec() {
        if (!this.executedStr.isNormal()) {
            ExecutableStrategy newE = this.executedStr.exec();
            if (newE == null) {
                return null;
            } else {
                this.executedStr = newE;
                return this;
            }
        }

        // okay, so we have evaluated our first strategy
        if (this.executedStr.isFail()) {
            this.executedStr = this.next();
            if (this.executedStr == null) {
                return new Fail("Empty First()");
            } else {
                return this;
            }
        } else {
            // we have success, so maybe merge the results
            if (this.workOnCopies) {
                this.obl.merge(this.workingCopy);
            } else {
                assert(this.obl == this.workingCopy);
            }
            return this.executedStr;
        }
    }


    private ExecutableStrategy next() {
        if (this.workOnCopies) {
            this.workingCopy = new BasicObligationNode(this.obl);
        } else {
            this.workingCopy = this.obl;
        }

        if (this.useExecStrats) {
            if (this.remExecStrs.hasNext()) {
                return this.remExecStrs.next();
            } else {
                return null;
            }
        } else {
            if (this.remStrs.hasNext()) {
                return this.remStrs.next().getExecutableStrategy(this.workingCopy, this.rti);
            } else {
                return null;
            }
        }
    }


    @Override
    void stop(String reason) {
        this.executedStr.stop(reason);
    }


    @Override
    public String toString() {
        String res = "EFirst("+this.executedStr;

        if (this.useExecStrats) {
            Iterator<ExecutableStrategy> i = this.allExecStrats.listIterator(this.remExecStrs.nextIndex());
            while (i.hasNext()) {
                res += ", "+i.next();
            }
        }
        else {
            Iterator<UserStrategy> i = this.allStrats.listIterator(this.remStrs.nextIndex());
            while (i.hasNext()) {
                res += ", "+i.next();
            }
        }

        return res+", "+"someObl"+")";
    }

}
