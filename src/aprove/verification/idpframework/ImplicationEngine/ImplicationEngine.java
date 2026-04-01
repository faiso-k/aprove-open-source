package aprove.verification.idpframework.ImplicationEngine;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;

/**
 *
 * @author MP
 */
public interface ImplicationEngine extends AtomicImplicationEngine {

    /**
     * Not explicitely quantified variables are considered to be universally quantified.
     * @param precondition
     * @param conclusion
     * @param aborter TODO
     * @return True if it can be shown that the precondition implies the conclusion (not complete)
     * @throws AbortionException TODO
     */
    public boolean checkImplication(IDPProblem idp, List<ItpfQuantor> quantification, Disjunction<ItpfConjClause> precondition, Disjunction<ItpfConjClause> conclusion, Abortion aborter) throws AbortionException;

    /**
     * Not explicitely quantified variables are considered to be universally quantified.
     * @param precondition
     * @param conclusion
     * @param aborter TODO
     * @return True if it can be shown that the precondition implies the conclusion (not complete)
     * @throws AbortionException TODO
     */
    public boolean checkImplication(IDPProblem idp, List<ItpfQuantor> quantification, Disjunction<ItpfConjClause> precondition, ItpfAtom conclusion, boolean positive, Abortion aborter) throws AbortionException;

    /**
     * Not explicitely quantified variables are considered to be universally quantified.
     * @param precondition
     * @param conclusion
     * @param aborter TODO
     * @return True if it can be shown that the precondition implies the conclusion (not complete)
     * @throws AbortionException TODO
     */
    public boolean checkImplication(IDPProblem idp, List<ItpfQuantor> quantification, ItpfConjClause precondition, Disjunction<ItpfConjClause> conclusion, Abortion aborter) throws AbortionException;

    public static abstract class ImplicationEngineSkeleton implements ImplicationEngine {

        @Override
        public boolean checkImplication(final IDPProblem idp, final List<ItpfQuantor> quantification,
            final Disjunction<ItpfConjClause> precondition,
            final Disjunction<ItpfConjClause> conclusion, final Abortion aborter) throws AbortionException {

            for (final ItpfConjClause preconditionClause : precondition) {
                if (!this.checkImplication(idp, quantification, preconditionClause, conclusion, aborter)) {
                    return false;
                }
            }

            return true;
        }

        @Override
        public boolean checkImplication(final IDPProblem idp, final List<ItpfQuantor> quantification,
            final Disjunction<ItpfConjClause> precondition,
            final ItpfAtom conclusion,
            final boolean positive, final Abortion aborter) throws AbortionException {
            for (final ItpfConjClause preconditionClause : precondition) {
                if (!this.checkImplication(idp, quantification, preconditionClause, conclusion, positive, aborter)) {
                    return false;
                }
            }
            return false;
        }

        @Override
        public boolean checkImplication(final IDPProblem idp,
            final List<ItpfQuantor> quantification,
            final ItpfConjClause precondition,
            final ItpfAtom conclusion,
            final boolean positive,
            final Abortion aborter) throws AbortionException {
            return this.checkImplication(idp, quantification, precondition,
                new Disjunction<ItpfConjClause>(idp.getItpfFactory().createClause(
                    conclusion, positive, ITerm.EMPTY_SET)), aborter);
        }

    }
}
