package aprove.verification.theoremprover.TerminationProcedures;

import java.util.logging.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.TRSProblem.*;

/**
 * A TRS processor expects a TRS as input.
 * @author nowonder
 * @version $Id$
 */
public abstract class TRSProcessor extends Processor.ProcessorSkeleton {

    protected static Logger log = Logger.getLogger("aprove.verification.theoremprover.TerminationProcedures.TRSProcessor");

    protected abstract Result processProgram(TRS trs, Abortion aborter) throws AbortionException;

    @Override
    public final Result process(BasicObligation input, BasicObligationNode position, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        return this.processProgram((TRS)input, aborter);
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (!(obl instanceof TRS)) {
            return false;
        }
        TRS trs = (TRS) obl;
        if (trs.isConditional()) { // no conditional
            return false;
        }
        if (!trs.getProgram().isDeterministic()) { // and no free vars on lhs
            return false;
        }
        if (trs.isEquational() && !this.isEquationalAble()) {
            return false;
        }
        return true;
    }

    public abstract boolean isEquationalAble();

}
