package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Represents the propositional encoding of a SimplePolynomial:
 * - a list of formulae (aka a circuit)
 * - a maximum possible value
 *
 * Also used to represent the propositional encoding of exotic
 * expressions (arctic or tropical). There the first bit in the
 * encapsulated formula tuple is the "infinity bit"
 * (cf. Koprowski, Waldmann, RTA'08), and only the following
 * bits are the "finite bits".
 *
 * Likewise, the list of formulas can be used to encode binary,
 * but also unary numbers. This class is essentially just a
 * rather generic wrapper.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class PolyCircuit {

    private List<Formula<None>> formulae;
    private BigInteger max;

    public PolyCircuit(List<Formula<None>> formulae, BigInteger max) {
        this.formulae = formulae;
        this.max = max;
    }

    public PolyCircuit(List<Formula<None>> formulae, long max) {
        this.formulae = formulae;
        this.max = BigInteger.valueOf(max);
    }

    /**
     * @return Returns the formulae.
     */
    public List<Formula<None>> getFormulae() {
        return this.formulae;
    }

    /**
     * @return Returns the max.
     */
    public BigInteger getMax() {
        return this.max;
    }

    /**
     * Calling the method only makes sense if this encodes an exotic
     * number (where the first bit is the infinity bit).
     *
     * TODO build a dedicated class ExoticPolyCircuit that encapsulates a
     * regular "finite" PolyCircuit and a Formula<None> for the infinity bit
     * -- the context-dependent semantics of the first bit are kinda nasty
     *
     * @return the finite version of this
     */
    public PolyCircuit toFinitePolyCircuit() {
        int oldSize = this.formulae.size();
        List<Formula<None>> res = new ArrayList<Formula<None>>(oldSize-1);
        boolean first = true;
        for (Formula<None> f : this.formulae) {
            if (first) {
                first = false;
            } else {
                res.add(f);
            }
        }
        PolyCircuit result = new PolyCircuit(res, this.max);
        return result;
    }

    @Override
    public String toString() {
        return "([" + this.formulae.size() + "], " + this.max + ")";
    }


    /**
     * Induces an ordering on PolyCircuits via their possible maximum values.
     *
     * Note: this comparator imposes orderings that are inconsistent with equals.
     */
    public static class PolyCircuitComparator implements Comparator<PolyCircuit> {

        public static final PolyCircuitComparator theComparator = new PolyCircuitComparator();

        @Override
        public int compare (PolyCircuit pc1, PolyCircuit pc2) {
            return pc1.max.compareTo(pc2.max);
        }
    }

}
