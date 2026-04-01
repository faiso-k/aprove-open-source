/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.itpf;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import immutables.*;

public interface IItpfRule extends Immutable {

    public static enum ApplicationMode {
        SingleStep, Multistep;
    }

    /**
     * Computes the result of this processor applied to a formula.
     * @param idp - the idp problem the formula belongs to
     * @param formula - the formula
     * @param aborter - the aborter, that should be checked many times against timeouts/aborts, ...
     * @return The result of this processor
     * @throws AbortionException
     */
    public Itpf process(IDPProblem idp, Itpf formula, ApplicationMode mode, Abortion aborter) throws AbortionException;

    /**
     * this is a fast test whether this processor can in general handle the
     * given IDP.
     */
    public boolean isApplicable(IDPProblem idp);

    /**
     * this is a fast test whether this processor can in general handle a
     * given ITPS-formula.
     */
    public boolean isApplicable(IDPProblem idp, Itpf formula, ApplicationMode mode);

    public Exportable getDescription(NameLength length);

    public abstract class ItpfRuleSkeleton implements IItpfRule {
    }
}
