package aprove.verification.dpframework.Heuristics.Conditions;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;

public class SizeFilter extends AbstractITRSCondition {

    private final int limit;

    @ParamsViaArgumentObject
    public SizeFilter(final Arguments arguments) {
        this.limit = arguments.limit;
    }

    @Override
    public boolean checkITRS(final ITRSProblem itrs, final Abortion aborter) {
        int size = 0;
        for (final GeneralizedRule rule : itrs.getR()) {
            size += rule.toString().length();
        }

        if (Globals.DEBUG_MARC) {
            System.err.println("ITRS size (current limit): " + size + " (" + this.limit + ")");
        }
        return size <= this.limit;
    }

    @Override
    public boolean isITRSApplicable(final ITRSProblem itrs) {
        return true;
    }

    public static class Arguments {
        public int limit = 0;
    }
}
