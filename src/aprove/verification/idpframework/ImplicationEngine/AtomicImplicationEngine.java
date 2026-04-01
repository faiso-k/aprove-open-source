package aprove.verification.idpframework.ImplicationEngine;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.Itpf.*;

/**
 *
 * @author MP
 */
public interface AtomicImplicationEngine {

    /**
     * Not explicitely quantified variables are considered to be universally quantified.
     * @param precondition
     * @param conclusion
     * @param aborter
     * @return True if it can be shown that the precondition implies the conclusion (not complete)
     * @throws AbortionException
     */
    public boolean checkImplication(IDPProblem idp, List<ItpfQuantor> quantification, ItpfConjClause precondition, ItpfAtom conclusion, boolean positive, Abortion aborter) throws AbortionException;

}
