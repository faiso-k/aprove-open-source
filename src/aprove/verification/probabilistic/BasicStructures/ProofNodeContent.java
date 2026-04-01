package aprove.verification.probabilistic.BasicStructures;

import java.util.*;

import org.apache.commons.math3.fraction.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A ProofNodeContent(t, p, List(Triple(s, sub, val))) contains...
 *
 * t - The term that is contained at this node in the tree
 * p - The probability of this node in the tree
 * List(Triple(s, sub, val)) - A list containing all possible ways to count and what value each way currently has
 * (s, sub, val) - the baseterm and pumping substitution we want to count. If sub is empty, then we count occurrences of the base term.
 *                 val is the current value for the corresponding way to count.
 * val - is a pair of two values for counting all occurrences (first component) and of counting only orthogonal occurrences (second component).
 *       If we are not allowed to count all occurrences (Tree is not nvd and looping term is not linear), then it is set to -1.
 */
public class ProofNodeContent extends Triple<TRSTerm, BigFraction, List<Triple<TRSTerm, TRSSubstitution, Pair<BigFraction, BigFraction>>>> {

    public ProofNodeContent() {
        super();
    }

    public ProofNodeContent(final TRSTerm x, final BigFraction y, final List<Triple<TRSTerm, TRSSubstitution, Pair<BigFraction, BigFraction>>> z) {
        super(x, y, z);
    }

}
