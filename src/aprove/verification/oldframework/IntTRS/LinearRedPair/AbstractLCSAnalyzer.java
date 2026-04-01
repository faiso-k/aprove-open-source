package aprove.verification.oldframework.IntTRS.LinearRedPair;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.IntTRS.LinearRedPair.LinearRedPairProcessor.*;
import aprove.verification.oldframework.Utility.*;

/**
 * An implementation represents an analyzing-method for a system of LCSs.
 * So a concrete implementation must know how to build the right constraints,
 * how to solve them (SMT-Solver / LP / whatever) and how to interpret the result.
 *
 * @author Matthias Hoelzel
 */
public abstract class AbstractLCSAnalyzer {
    /** System of LCSs to be solved */
    protected final ArrayList<LCS> lcsSystem;

    /** The proof. */
    protected final LinearRankingProof proof;

    /** Generates new names */
    protected final FreshNameGenerator ng;

    /**
     * Constructor
     * @param lcss System of LCSs to be solved,
     *        note that this constructor copies the list
     * @param lrProof the proof we are going to create
     * @param gen NameGenerator
     */
    public AbstractLCSAnalyzer(final List<LCS> lcss,
 final LinearRankingProof lrProof, final FreshNameGenerator gen) {
        assert gen != null && lcss != null : "NULL?!?";
        this.proof = lrProof;
        this.ng = gen;
        this.lcsSystem = new ArrayList<LCS>(lcss);
    }

    /**
     * Solves the system and returns another (maybe simplified) system.
     * @return list of LCS to be solved instead
     * @throws AbortionException can be aborted
     */
    public abstract List<LCS> solve() throws AbortionException;

    /**
     * Should return true IFF the system could be simplified in some way.
     * Don't use this method, if you have used solve() before!
     * @return boolean
     */
    public abstract boolean hasChanged();

    /**
     * Returns the list of dropped LCSs.
     * @return list of LCSs
     */
    public abstract List<LCS> getDroppedRules();
}
