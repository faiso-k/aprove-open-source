package aprove.strategies.ExecutableStrategies;

import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.oldframework.Logic.*;

public class ExecSolve extends ExecutableStrategy {

    public static enum AcceptableResult {
        WANT_YES {
            @Override
            boolean isAcceptable(final TruthValue result) {
                return result == YNM.YES;
            }
        },
        WANT_NO {
            @Override
            boolean isAcceptable(final TruthValue result) {
                return result == YNM.NO;
            }
        },
        WANT_ANY {
            @Override
            boolean isAcceptable(final TruthValue result) {
                return result.isCompletelyKnown();
            }
        };
        abstract boolean isAcceptable(TruthValue result);
    }

    private ExecutableStrategy exStr;
    private final BasicObligationNode obl;
    private final BasicObligationNode workingCopy;
    private final AcceptableResult acceptable;

    public ExecSolve(final UserStrategy str, final AcceptableResult acceptable, final BasicObligationNode obl, final RuntimeInformation rti) {
        super(rti);
        this.workingCopy = Options.strategyWorksOnCopies ? new BasicObligationNode(obl) : obl;
        this.exStr = str.getExecutableStrategy(this.workingCopy, rti);
        this.obl = obl;
        this.acceptable = acceptable;
    }


    /**
     * Creates a Solve Strategy, that waits for the obl-node to get a truth value,
     * but goes on with the ExecutableStrategy supplied, which must not necessarily work there.
     *
     * The workingCopy is always set to the obl node, i.e. there is no pruning of the proof tree.
     * @param exStr The ExecutableStrategy that shall continue
     * @param obl A node to wait for
     * @param rti
     */
    public ExecSolve(final ExecutableStrategy exStr, final BasicObligationNode obl, final RuntimeInformation rti) {
        super(rti);

        this.workingCopy = obl;
        this.exStr = exStr;
        this.obl = obl;
        this.acceptable = AcceptableResult.WANT_ANY;
    }

    @Override
    ExecutableStrategy exec() {
        if (this.workingCopy.isTruthValueKnown()) {
            // check whether we have the desired result
            this.stop("truth value is known");
            if (this.acceptable.isAcceptable(this.workingCopy.getTruthValue())) {
                if (this.obl != this.workingCopy) {
                    this.obl.merge(this.workingCopy);
                }
                return Success.EMPTY;
            } else {
                // wrong result
                return new Fail("Bad result in Solve()");
            }
        } else {
            if (this.exStr.isNormal()) {
                return new Fail("Solve(): Done but no truth value produced!");
            } else {
                final ExecutableStrategy newEx = this.exStr.exec();
                if (newEx == null) {
                    return null;
                } else {
                    this.exStr = newEx;
                    return this;
                }
            }
        }
    }

    @Override
    void stop(final String reason) {
        this.exStr.stop(reason);
    }

    @Override
    public String toString() {
        final String oblR = "someObl"; // pos.getRepresentation();
        return "ESolve(" + this.acceptable + ", "+oblR+", "+this.exStr+")";
    }

}
