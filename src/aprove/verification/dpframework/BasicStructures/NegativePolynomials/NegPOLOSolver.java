/*
 * Created on 18.03.2005
 */
package aprove.verification.dpframework.BasicStructures.NegativePolynomials;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.PiDPProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public interface NegPOLOSolver {

    Pair<? extends ExportableOrder<TRSTerm>, Set<Rule>> solve(QDPProblem qdp, boolean allStrict) throws AbortionException;
    QActiveOrder solve(Set<Rule> P, Map<Rule, QActiveCondition> active, boolean allStrict) throws AbortionException;
    Pair<? extends ExportableOrder<TRSTerm>, Set<GeneralizedRule>> solve(PiDPProblem pidp, boolean allStrict) throws AbortionException;

    public final boolean reverse = false;

}
