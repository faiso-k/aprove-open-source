/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A VariableConverterPoT is able to extract the value of some Diophantine
 * variable out of the integer array provided by the sat searcher (which
 * includes the values for propositional variables).
 * @author cotto
 */
public class VariableConverterPoT {
    /**
     * The solution found by the sat searcher.
     */
    private Set<Integer> solution;

    /**
     * Each variable of the polynomial constraints correspond to a coefficient
     * and a exponent, these circuits are stored here.
     */
    private final Map<GPolyVar, Pair<PolyCircuit, PolyCircuit>> map =
        new LinkedHashMap<GPolyVar, Pair<PolyCircuit, PolyCircuit>>();

    /**
     * For each variable a' ranging over natural numbers give the original
     * variable a possibly ranging over rational numbers. Also provide a
     * correction factor so that a = a' * correction.
     */
    private Map<GPolyVar, Pair<GPolyVar, PoT>> transformed;

    /**
     * This ring operates on PoTs.
     */
    private final Ring<PoT> ring;

    /**
     * Create the converter which works with the given ring.
     * @param ringParam A ring that operates on PoTs.
     */
    public VariableConverterPoT(final Ring<PoT> ringParam) {
        this.ring = ringParam;
    }

    /**
     * Set the solution.
     * @param solutionParam A solution that was found by a sat searcher.
     */
    public void setSolution(final int[] solutionParam) {
        this.solution = new LinkedHashSet<Integer>(solutionParam.length);
        for (final int element : solutionParam) {
            if (element > 0) {
                // only remember the variables set to 1.
                this.solution.add(element);
            }
        }
    }

    /**
     * @return a map which assigns a PoT value to every known variable.
     */
    public Map<GPolyVar, PoT> getMap() {
        final Map<GPolyVar, PoT> result = new LinkedHashMap<GPolyVar, PoT>(this.map.size());

        for (final Map.Entry<GPolyVar, Pair<PolyCircuit, PolyCircuit>> entry : this.map.entrySet()) {
            final GPolyVar var = entry.getKey();
            PoT pot = this.convert(entry.getValue());
            final Pair<GPolyVar, PoT> correction = this.transformed.get(var);
            GPolyVar newVar;
            if (correction != null) {
                // there is a correction, e.g.
                // var = a', correction.x = a, a = a' * correction.y.
                pot = this.ring.times(pot, correction.y);
                newVar = correction.x;
            } else {
                // no correction needed, e.g. for boolean variables b_i.
                newVar = var;
            }
            result.put(newVar, pot);
        }
        return result;
    }

    /**
     * @param pair Two circuits defining the coefficient and exponent part.
     * @return the PoT value that corresponds to the values of the given
     * circuits.
     */
    private PoT convert(final Pair<PolyCircuit, PolyCircuit> pair) {
        if (Globals.useAssertions) {
            assert (this.solution != null);
            assert (pair != null);
        }
        // FIXME
        assert (false);
        /*
         * See commit 340870fd8a98d6a144fd329b178c657cd4bfcc9f
         *
         * IndefiniteBinarizer.create(null, null) always triggers a NPE.
         */

        // This binarizer cannot be used to binarize anything, just to unbinarize.
        final IndefiniteBinarizer<String> bin = IndefiniteBinarizer.create(null, null);
        final BigInteger result1 = bin.natBig(pair.x.getFormulae(), this.solution);
        final BigInteger result2 = bin.natBig(pair.y.getFormulae(), this.solution);
        final PoT result = PoT.create(result1, result2);
        return result;
    }

    /**
     * The variable var from the constraints is encoded as a pair of circuits.
     * @param var The variable from the constraints.
     * @param pair the coefficient and exponent of the encoded variable.
     */
    public void put(final GPolyVar var, final Pair<PolyCircuit, PolyCircuit> pair) {
        this.map.put(var, pair);
    }

    /**
     * Store the map of transformed variables so that one is able to compute
     * a out of a'.
     * @param transformedParam The map giving information about real value of
     * the variables.
     */
    public void setTransformed(final Map<GPolyVar, Pair<GPolyVar, PoT>> transformedParam) {
        this.transformed = transformedParam;
    }

    /**
     * Clear the data that is not needed anymore.
     */
    public void clear() {
        if (this.solution != null) {
            this.solution.clear();
        }
        if (this.transformed != null) {
            this.transformed.clear();
        }
    }
}
