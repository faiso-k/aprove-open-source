package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.NegativePolynomials.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * QDP Polo processor. Tries to orient P and all usable rules of P non-strictly
 * and at least one rule of P strictly, then deletes the strictly oriented
 * rules from P.
 *
 * @author Rene Thiemann
 * @version $Id$
 *
 * @deprecated use ReductionPairProcessor and QDPNegPoloSolver instead!
 */
@Deprecated
public class QDPNegPoloProcessor extends QDPProblemProcessor {

    private final int range;
    private final int restriction;
    private final boolean allstrict;

    @ParamsViaArgumentObject
    public QDPNegPoloProcessor(Arguments arguments) {
        this.range = arguments.range;
        this.restriction = arguments.restriction;
        this.allstrict = arguments.allstrict;
    }

    @Override
    protected Result processQDPProblem(QDPProblem qdp, Abortion aborter)
            throws AbortionException {

        Pair<? extends ExportableOrder<TRSTerm>, Set<Rule>> result;
        NegPOLOSolver solver = new DynamicNegPOLOSolver(this.range, this.restriction, true, aborter);
        result = solver.solve(qdp, this.allstrict);

        if (result == null) {
            return ResultFactory.unsuccessful();
        } else {
            return QDPReductionPairProcessor.getResult(result.x, result.y, qdp,
                    null);
        }
    }

    @Override
    public boolean isQDPApplicable(QDPProblem qdp) {
        return qdp.getMinimal() || qdp.QsupersetOfLhsR();
    }

    public static class Arguments {
        public int range = 1;
        public int restriction = 2;
        public boolean allstrict = false;
    }
}
