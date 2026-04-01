package aprove.verification.dpframework.Utility.NonLoop.NonLoopSearch;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.nontermination.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Tim Enger
 */

public interface NonLoopSearch {

    /**
     * Start the search.
     *
     * @return If a non-terminating {@link ProofedRule} is found, a {@link Pair}
     *         is returned, else <tt>null</tt>. The {@link Pair} consists of
     *         <ul>
     *         <li> <tt>pair.x</tt>: a non-terminating {@link ProofedRule}
     *         <li> <tt>pair.y</tt>: in case of
     *         <ul>
     *         <li>non-terminating {@link NarrowRule}: the matcher (
     *         <tt>pair.y.x</tt> ) and the semi-unifier (<tt>pair.y.y</tt>) is
     *         returned.</li>
     *         <li>a non-terminating {@link PatternRule}: <tt>pair.y</tt> is
     *         <tt>null</tt>.</li>
     *         </ul>
     *         </ul>
     * @throws AbortionException
     */
    public NonLoopProof findNonLoop() throws AbortionException;

    /**
     * @return A short description of this search method.
     */
    public String getDescription();

}
