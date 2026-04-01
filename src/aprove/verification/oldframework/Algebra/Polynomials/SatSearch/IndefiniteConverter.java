package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Instances of IndefiniteConverter are used to convert between
 * indefinite coefficients of polynomials and PolyCircuits.
 * PolyCircuits that encode indefinites are stored once they have
 * been generated so that the <code>bin</code> method can be invoked
 * with one and the same argument for several times. This behavior
 * also allows for the reverse conversion.
 *
 * Furthermore, there are static methods for obtaining propositional
 * tuples from natural numbers and for obtaining the number encoded
 * by a tuple of propositional variables given a logical
 * interpretation for it.
 *
 * @author fuhs
 *
 * @param <T> type of indefinites to be converted to propositional logic
 *  (usually, but not necessarily, String)
 */
public interface IndefiniteConverter<T> {

    /**
     * @param indef - indefinite for which we want to add a
     *  propositional representation.
     * @param pc - the propositional representation of indef
     */
    void put(T indef, PolyCircuit pc);


    /**
     * @param n to be represented in propositional logic
     * @return a representation of <code>n</code> in
     *  propositional logic
     */
    List<Formula<None>> bin(int n);


    /**
     * @param n to be represented in propositional logic
     * @return a representation of <code>n</code> in
     *  propositional logic
     */
    List<Formula<None>> bin(BigInteger n);


    /**
     * Returns the corresponding representation of an indefinite coefficient
     * of a polynomial which consists of as many propositional variables as
     * bits are needed for range. For a given indefinite, the result will
     * always be the same (it will be cached once it has been computed), so the
     * range passed to bin should be constant for a given value of indef.
     *
     * Necessary global side constraints for the range are taken care of
     * automatically, but you must explicitly get them from this
     * IndefiniteConverter in the end.
     *
     * @param indef the indefinite to be represented in propositional logic
     * @param range the range of the indefinite, at least 1
     * @return the representation of <code>indef</code> by <code>bits</code>
     *  propositional variables
     */
    PolyCircuit bin(T indef, BigInteger range);

    /**
     * Computes the natural number that corresponds to the tuple formulae
     * as given in the interpretation.
     *
     * Semantics of a formula tuple depends on the internal representation
     * of numbers via prop. logic (unary, binary, ...).
     *
     * @param formulae the list of formulae which are supposed to represent
     *  an indefinite coefficient.
     * @param interpretation contains those formulae that are interpreted
     *  as true
     * @return the corresponding natural number
     */
    BigInteger natBig(List<? extends Formula<None>> formulae,
                      Set<Integer> interpretation);



    /**
     * Creates additional conjuncts to add to the result formula ensuring only valid combinations can be used.
     * Determines the correct form using the range for a given variable and the POLOSAT configuration.
     *
     * @note kabasci: Moved from AbstractSPCToCircuitConverter, as needs more functionality with shifts. WAS:
     * Helper method for allowing arbitrary natural ranges for
     * Diophantine variables, not only 2^k - 1. Generates clauses
     * that prohibit values greater than range.
     *
     * @param range - maximum range allowed for vars;
     *  may be at most 2^vars.size() - 1
     * @param variables - tuple of variables (formulae) that is supposed
     *  to represent some Diophantine variable
     *  @param arithmeticFactory - The arithmetic factory to be used for creating constraints of sorts.
     * @return conjuncts for enforcing that I(vars) <= range for
     *  any model I of the circuit in construction
     */
    //List<Formula<None>> excludeUpperBits(BigInteger range, List<Formula<None>> vars, ArithmeticFactory arithmeticFactory);

    /**
     * @return the internal map from indefinite coefficients
     *  to propositional variables; <b>modify it only if you
     *  know what you are doing!</b>
     */
    Map<T, PolyCircuit> getIndefsToVars();

    /**
     * @return side constraints (proto-conjunction) that need to be fulfilled
     *  in addition to the formula that has been built so far; may be needed due to
     *  <ul>
     *   <li> ranges that are not of the shape 2^k - 1 (for binary representation)
     *   <li> prefix condition (for unary representation)
     *  </ul>
     */
    List<Formula<None>> getSideConstraints();
}
