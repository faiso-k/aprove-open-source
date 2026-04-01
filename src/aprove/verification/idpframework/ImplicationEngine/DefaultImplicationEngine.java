package aprove.verification.idpframework.ImplicationEngine;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;

/**
 * @author MP
 */
public class DefaultImplicationEngine extends ImplicationEngine.ImplicationEngineSkeleton {

    private static PolyImplicationEngine POLY_ENGINE =
        new PolyImplicationEngine();

    @Override
    public boolean checkImplication(final IDPProblem idp,
        final List<ItpfQuantor> quantification,
        final ItpfConjClause precondition,
        final Disjunction<ItpfConjClause> conclusion,
        final Abortion aborter) throws AbortionException {

        for (final ItpfConjClause conclusionClause : conclusion) {
            if (precondition.getLiterals().entrySet().containsAll(conclusionClause.getLiterals().entrySet())) {
                return true;
            }
        }


        if (this.checkOnlyPoly(conclusion)) {
            return DefaultImplicationEngine.POLY_ENGINE.checkImplication(idp, quantification,
                precondition, conclusion, aborter);
        }
        return false;
    }

    private boolean checkOnlyPoly(final Iterable<ItpfConjClause> clauses) {
        for (final ItpfConjClause clause : clauses) {
            for (final ItpfAtom atom : clause.getLiterals().keySet()) {
                if (!atom.isPoly()) {
                    return false;
                }
            }
        }

        return true;
    }

}
