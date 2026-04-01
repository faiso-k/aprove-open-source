package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination;

import java.util.*;

import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.*;
import aprove.verification.oldframework.Logic.*;

/**
 * Consists of a remaining IRSwTProblem and a set of edges that have been removed.
 * @author cryingshadow
 * @version $Id$
 */
public class CooperationUnknown extends CooperationTerminating {

    /**
     * The rules that have been removed.
     */
    private final Collection<IGeneralizedRule> dropped;

    /**
     * The remaining problem.
     */
    private final IRSwTProblem resultIntTRS;

    /**
     * @param r The ranking function.
     * @param left The remaining problem.
     * @param solved The rules that have been removed.
     */
    public CooperationUnknown(
        Map<TRSFunctionApplication, List<SimplePolynomial>> r,
        IRSwTProblem left,
        Collection<IGeneralizedRule> solved
    ) {
        super(r);
        this.resultIntTRS = left;
        this.dropped = solved;
    }

    /**
     * @return The rules that have been removed.
     */
    public Collection<IGeneralizedRule> getDropped() {
        return this.dropped;
    }

    /**
     * @return The remaining problem.
     */
    public IRSwTProblem getRemaining() {
        return this.resultIntTRS;
    }

    @Override
    public Result toResult() {
        // TODO Auto-generated method stub
        return
            ResultFactory.proved(
                this.resultIntTRS,
                YNMImplication.EQUIVALENT,
                new SafetyIntTRSPoloRedPairProof(this.getRanking(), this.dropped)
            );
    }

    @Override
    public String toString() {
        return "UNKNOWN";
    }

}
