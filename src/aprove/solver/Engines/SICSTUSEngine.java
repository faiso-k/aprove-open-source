package aprove.solver.Engines;

import java.math.*;

import aprove.solver.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.SicstusPrologFileSearch.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class SICSTUSEngine extends Engine {

    // always only compile prolog program, always only interpret it, or
    // first try to compile it and then interpret only if necessary?
    private SicstusMode mode = SicstusMode.BOTH;

    // introduce extra predicates to keep the clauses short?
    // improves the chances that compiling the clauses works,
    // but extra predicates might be bad for efficiency.
    private boolean shortClauses = true;

    @Override
    public SearchAlgorithm getSearchAlgorithm(DefaultValueMap<String, BigInteger> ranges) {
        SicstusMode mode = this.getMode();
        boolean shortClauses = this.getShortClauses();
        return SicstusPrologFileSearch.create(ranges, mode, shortClauses);
    }

    /**
     * @param mode the mode to set
     */
    public void setMode(SicstusMode mode) {
        this.mode = mode;
    }

    /**
     * @return the mode
     */
    public SicstusMode getMode() {
        return this.mode;
    }

    /**
     * @return Returns the shortClauses.
     */
    public boolean getShortClauses() {
        return this.shortClauses;
    }

    /**
     * @param shortClauses The shortClauses to set.
     */
    public void setShortClauses(boolean shortClauses) {
        this.shortClauses = shortClauses;
    }
}
