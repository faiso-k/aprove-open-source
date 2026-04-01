package aprove.verification.oldframework.Algebra.LimitPolynomials;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;


/**
 * A set of Variables mapped to LimitPolynomials.
 * Since currently LimitPolynomials are only to be used in linear settings (theory unclear in general case)
 * they cannot be multiplied with one another, but only with LimitPolynomials.
 * @author kabasci
 *
 */
public class LimitVarPolynomial {

    /**
     * Term Variables -> associated interpreted LimitPolynomial
     */
    Map<TRSVariable, LimitPolynomial> varMonomials = new LinkedHashMap<TRSVariable, LimitPolynomial>();

    /**
     * LimitPoylnomial of the interpretation of the ground part of a term
     */
    LimitPolynomial constantPart = LimitPolynomial.ZERO;

    /**
     * Creates a LimitVarPolynomial without a variable in it.
     * @param simpleInit The LimitPolynomial of this polynomial.
     */
    public LimitVarPolynomial(LimitPolynomial simpleInit) {
        this.constantPart = simpleInit;
    }

    /**
     * Creates a LimitVarPolynomial representing the mentioned variable.
     * @param var The Variable this LimitVarPolynomial should represent.-
     */
    public LimitVarPolynomial(TRSVariable var) {
        this.varMonomials.put(var, LimitPolynomial.ONE);
    }

    /**
     * Create a new LimitVarPolynomial using the constant part and variable-Polynomial map provided.
     * No deep copy is performed!
     * @param constantPart
     * @param varMap
     */
    LimitVarPolynomial(LimitPolynomial constantPart, Map<TRSVariable, LimitPolynomial> varMap) {
        this.constantPart = constantPart;
        this.varMonomials = varMap;
    }

    /**
     * Returns the constant part of the LimitVarPolynomial
     * @return
     */
    public LimitPolynomial getConstantPart() {
        return this.constantPart;
    }


    /**
     * Returns the part of a certain Variable of the LimitVarPolynomial (remember that LimitVarPolynomials have to be linear)
     * @param v
     * @return
     */
    public LimitPolynomial getVariablePart(TRSVariable v) {
        return this.varMonomials.get(v);
    }

    /**
     * Returns the set of all variables for which this LimitVarPolynomial is defined.
     *
     */
    public Set<TRSVariable> getVariables()  {
        return this.varMonomials.keySet();
    }


    /**
     * Multiplies all LimitPolynomials a variable is mapped to and the constant part with a LimitPolynomial.
     * @param poly
     * @return
     */
    public LimitVarPolynomial multiplyBy(LimitPolynomial poly) {

        Map<TRSVariable, LimitPolynomial> newVarMonomials = new LinkedHashMap<TRSVariable, LimitPolynomial>();
        LimitPolynomial newConstantPart = this.constantPart.times(poly);

        for (Map.Entry<TRSVariable, LimitPolynomial> e: this.varMonomials.entrySet()) {
            newVarMonomials.put(e.getKey(), e.getValue().times(poly));
        }

        return new LimitVarPolynomial(newConstantPart, newVarMonomials);


    }

    /**
     * Adds a List of LimitVarPolynomials
     * @param addends The LimitVarPolynomials to add
     * @return
     */
    public static LimitVarPolynomial plus(List<LimitVarPolynomial> addends) {

        Map<TRSVariable, List<LimitPolynomial>> newVarMonomials = new LinkedHashMap<TRSVariable, List<LimitPolynomial>>();
        Map<TRSVariable, LimitPolynomial> newVarMonomialsFlattened = new LinkedHashMap<TRSVariable, LimitPolynomial>();
        List<LimitPolynomial> newConstantParts = new ArrayList<LimitPolynomial>();
        LimitPolynomial newConstantPartFlattened;

        // Put all monomials to a given variable in a collection fist; this saves quite some deep copies since we do not call add for every two polynomials
        for (LimitVarPolynomial lvp: addends) {
            newConstantParts.add(lvp.constantPart);
            for (Map.Entry<TRSVariable, LimitPolynomial> e: lvp.varMonomials.entrySet()) {
                if (!newVarMonomials.containsKey(e.getKey())) {
                    newVarMonomials.put(e.getKey(), new ArrayList<LimitPolynomial>());
                }
                newVarMonomials.get(e.getKey()).add(e.getValue());
            }
        }

        for (TRSVariable v: newVarMonomials.keySet()) {
            newVarMonomialsFlattened.put(v, LimitPolynomial.plus(newVarMonomials.get(v)));
        }

        newConstantPartFlattened = LimitPolynomial.plus(newConstantParts);

        return new LimitVarPolynomial(newConstantPartFlattened, newVarMonomialsFlattened);

    }

    /**
     * Subtracts two LimitVarPolynomials
     * @param other The LVP to subtract
     * @return
     */
    public LimitVarPolynomial minus(LimitVarPolynomial other) {

        final ArrayList<LimitVarPolynomial> l = new ArrayList<LimitVarPolynomial>();
        l.add(this);
        l.add(other.multiplyBy(LimitPolynomial.MINUS_ONE));
        return LimitVarPolynomial.plus(l);

    }


    /**
     * Compares a LimitVarPolynomial to zero, if this can be computed. Returns true iff. the LVP is >0.
     * @return
     */
    public boolean gtZero() {
        // In order to be greater than Zero, all variable parts must be GE zero, and the constant part must be > 0.

        boolean result = this.constantPart.gtZero();

        for (LimitPolynomial m: this.varMonomials.values()) {
            result &= m.geZero();
        }

        return result;

    }

    /**
     * Compares a LimitVarPolynomial to zero, if this can be computed. Returns true iff. the LVP is >=0.
     * @return
     */
    public boolean geZero() {
        // In order to be >=0, all variable parts must be GE zero, and the constant part must be >= 0.

        boolean result = this.constantPart.geZero();

        for (LimitPolynomial m: this.varMonomials.values()) {
            result &= m.geZero();
        }

        return result;

    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();

        sb.append(this.constantPart.toString());

        for (Map.Entry<TRSVariable, LimitPolynomial> e: this.varMonomials.entrySet()) {
               sb.append(" + [");

               sb.append(e.getValue().toString());
               sb.append("]");
               sb.append(e.getKey().toString());

        }

        return sb.toString();
    }





}
