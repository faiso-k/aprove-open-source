package aprove.verification.dpframework.Orders.Utility.GPOLO.Heuristics;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Just say true. This way, each and every number in a
 * polynomial interpretation may become non-natural.
 *
 * @author fuhs
 * @version $Id$
 */
public class AlwaysRat implements RatHeuristic {

    @Override
    public boolean allowRat() {
        return true;
    }

    @Override
    public boolean allowRat(FunctionSymbol f) {
        return true;
    }

    @Override
    public boolean allowRatCoeff(FunctionSymbol f, int i) {
        return true;
    }

    @Override
    public boolean allowRatConst(FunctionSymbol f) {
        return true;
    }

    @Override
    public void setPR(Set<? extends GeneralizedRule> p, Set<? extends GeneralizedRule> r) {
    }
}
