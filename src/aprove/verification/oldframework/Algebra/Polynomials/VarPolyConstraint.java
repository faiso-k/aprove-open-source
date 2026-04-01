package aprove.verification.oldframework.Algebra.Polynomials;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Verifier.*;
import immutables.*;

/**
 * @author Carsten Fuhs
 * @version $Id$
 *
 * A VarPolyConstraint encodes a VarPolynomial in relation with 0
 * where the relation is one of { =, >=, > }.
 * Use null for the unsatisfiable VarPolyConstraint.
 *
 * Many methods of the class rely on the assumption that only instantiations
 * of variables with /non-negative/ integers is considered (whose natural
 * ordering is well founded).
 */
public class VarPolyConstraint implements Immutable {

    public static final VarPolyConstraint VALID_VPC = new VarPolyConstraint(VarPolynomial.ZERO,
            ConstraintType.GE);

    // the VarPolynomial on the LHS of the constraint
    private final VarPolynomial varPoly;

    // the type of the Constraint
    private final ConstraintType type;

    private int hashValue; // cache for the hash value
    private boolean hashValid; // has the hash value already been computed?

    private static final boolean ABS_POS = true; // for RedLog

    /**
     * Generate a new VarPolyConstraint, using the parameters as values
     * for the attributes.
     *
     * @param varPoly  the (non-null) VarPolynomial to occur on the LHS
     * @param type  the relation in which varPoly is with 0, not null
     */
    public VarPolyConstraint(VarPolynomial varPoly, ConstraintType type) {
        if (Globals.useAssertions) {
            assert(varPoly != null && type != null);
        }
        this.varPoly = varPoly;
        this.type = type;
        this.hashValid = false;
    }


    /**
     * Convenience method to return all coefficient SimplePolynomials
     * contained by this as a Set of SimplePolyConstraints with suitable
     * ConstraintTypes. Effectively, these are the constraints that are
     * solved in order to show that this is solvable.
     *
     * The current implementation is also known as "absolute positiveness
     * criterion", which is equivalent to the "partial derivative criterion".
     *
     * @return all coefficient SimplePolynomials contained by <code>this</code>
     *  as a Set of SimplePolyConstraints with suitable ConstraintTypes such
     *  that if these SPCs are satified, then so is <code>this</code>
     */
    public Set<SimplePolyConstraint> createCoefficientConstraints() {
        Set<SimplePolyConstraint> result = new LinkedHashSet<SimplePolyConstraint>(this.varPoly.numberOfAddends());
        this.addCoefficientConstraints(result);
        return result;
    }

    /**
     * Add all coefficient SimplePolynomials contained by this
     * with suitable ConstraintTypes to a Set of SimplePolyConstraints.
     * Effectively, these are the constraints that need to be solved
     * in order to show that this is solvable.
     *
     * Also known as "absolute positiveness criterion", which is
     * equivalent to the "partial derivative criterion".
     *
     * @param result - non-null set of coefficient SimplePolynomialConstraint
     *  to which constraints are added such that these constraints being
     *  satisfied implies <code>this</code> being satisfied
     *
     */
    public void addCoefficientConstraints(Set<SimplePolyConstraint> result) {
        SimplePolynomial constant = this.varPoly.getConstantPart();
        ConstraintType typ = this.type;
        result.add(new SimplePolyConstraint(constant, typ));
        if (typ == ConstraintType.GT) { // wieso ist das hier?
            typ = ConstraintType.GE;
        }
        for (SimplePolynomial simplePoly : this.varPoly.getCoefficientsOfVariables()) {
            result.add( new SimplePolyConstraint(simplePoly, typ));
        }
    }

    /**
     * Prerequisite: this.type must be GE, otherwise trying to create
     * searchstrict constraints does not make much sense anyway.<p>
     *
     * Return the coefficient SimplePolynomials contained by this as a
     * Set of SimplePolyConstraints with suitable ConstraintTypes,
     * distinguishing between constraints which will always be non-strict
     * and those which may be oriented strictly by searchstrict.
     *
     * @return Pair of Sets of SimplePolyConstraints where<br>
     *  component x: contains the constraints that will always have type GE<br>
     *  component y: contains the constraints that have type GE here, but which
     *               might get type GT due to searchstrict later
     */
    public Pair<Set<SimplePolyConstraint>, SimplePolyConstraint> createSearchStrictCoefficientConstraints() {
        if (Globals.useAssertions) {
            assert(this.type == ConstraintType.GE);
        }

        // some of the SimplePolyConstraints will always have type GE
        Set<SimplePolyConstraint> gePart = new LinkedHashSet<SimplePolyConstraint>();

        // the others might get type GT (be oriented strictly) later
        // by searchstrict

        SimplePolynomial constant = this.varPoly.getConstantPart();
        SimplePolyConstraint searchStrictPart = new SimplePolyConstraint(constant, ConstraintType.GE);
        for (SimplePolynomial simplePoly : this.varPoly.getCoefficientsOfVariables()) {
            gePart.add( new SimplePolyConstraint(simplePoly, ConstraintType.GE) );
        }
        return new Pair<Set<SimplePolyConstraint>, SimplePolyConstraint>(gePart, searchStrictPart);
    }

    /**
     * Convert polyConstraint to an equivalent VarPolyConstraint using
     * vars as variables.
     *
     * @param polyConstraint  to be converted
     * @param vars  the variables of polyConstraint
     * @return a VarPolyConstraint that is equivalent to polyConstraint with
     *  vars as variables
     */
    public static VarPolyConstraint toVarPolyConstraint(PolyConstraint polyConstraint,
                                                        Set<String> vars) {
        VarPolynomial varPoly = VarPolynomial.toVarPolynomial(polyConstraint.getPolynomial(), vars);
        ConstraintType newType = null;
        switch (polyConstraint.getType()) {
        case AbstractConstraint.EQ :
            newType = ConstraintType.EQ;
            break;
        case AbstractConstraint.GE :
            newType = ConstraintType.GE;
            break;
        case AbstractConstraint.GR :
            newType = ConstraintType.GE;
            varPoly = varPoly.minus(VarPolynomial.ONE);
            break;
        }
        return new VarPolyConstraint(varPoly, newType);
    }


    /**
     * Convenience methode to convert a Set of PolyConstraints and variables to
     * the corresponding Set of VarPolyConstraints
     *
     * @param polyConstraintWithVars  the PolyConstraints and their
     *  variables which are to be converted
     * @return the corresponding equivalent Set of VarPolyConstraints
     */
    public static Set<VarPolyConstraint> toVarPolyConstraints(Set<Pair<PolyConstraint, Set<String>>> polyConstraintsWithVars) {
        Set<VarPolyConstraint> result = new LinkedHashSet<VarPolyConstraint>();
        for (Pair<PolyConstraint, Set<String>> pair : polyConstraintsWithVars) {
            result.add( VarPolyConstraint.toVarPolyConstraint(pair.x, pair.y));
        }
        return result;
    }

    /**
     * Convenience methode to convert a Map from PolyConstraints to their
     * variables to the corresponding Set of VarPolyConstraints
     *
     * @param polyConstraintToVars  the Map from PolyConstraints
     *  to their variables which is to be converted
     * @return the corresponding equivalent Set of VarPolyConstraints
     */
    public static Set<VarPolyConstraint> toVarPolyConstraints(Map<PolyConstraint, Set<String>> polyConstraintsToVars) {
        Set<VarPolyConstraint> result = new LinkedHashSet<VarPolyConstraint>();
        for (Map.Entry<PolyConstraint, Set<String>> entry : polyConstraintsToVars.entrySet()) {
            result.add( VarPolyConstraint.toVarPolyConstraint(entry.getKey(), entry.getValue()));
        }
        return result;
    }


    public VarPolynomial getPolynomial() {
        return this.varPoly;
    }

    public ConstraintType getType() {
        return this.type;
    }

    /**
     * @param x - a variable
     * @return this with its polynomial derived with respect to x
     */
    public VarPolyConstraint deriveWRT(String x) {
        VarPolynomial newPoly = this.varPoly.deriveWRT(x);
        return new VarPolyConstraint(newPoly, this.type);
    }


    /**
     * Convenience method to obtain a specialized version of this
     *
     * @param values - specialization, i.e., mapping from abstract coefficients
     *  to concrete values
     * @return a specialized version of this
     */
    public VarPolyConstraint specialize(Map<String, BigInteger> values) {
        VarPolynomial newPoly = this.varPoly.specialize(values);
        return new VarPolyConstraint(newPoly, this.type);
    }

    /**
     * @return true if this is found to be valid (method is correct, but
     *  not complete), otherwise false
     */
    public boolean isValid() {
        // break the issue down to the corresponding SimplePolyConstraints
        Set<SimplePolyConstraint> simplePolyConstraints;
        simplePolyConstraints = this.createCoefficientConstraints();
        for (SimplePolyConstraint simplePolyConstraint : simplePolyConstraints) {
            if (! simplePolyConstraint.isValid()) {
                return false;
            }
        }
        return true;
    }

    /**
     * Return true if this is found to be (existentially) usatisfiable.
     * Method is correct, but incomplete.
     *
     * @return true if this is found to be unsatisfiable, i.e., this cannot
     *  hold for any instantiation of the variables and possible abstract
     *  coefficients by natural numbers (method is correct, but not
     *  complete), otherwise false
     */
    public boolean isUnsatisfiable() {
        // this is unsatisfiable if ...
        // * it is of type GE, the poly is completely negative and the constant is negative  or
        // * it is of type GT and the poly is completely negative (regardless of whether
        //                                   there is a non-zero constant addend)  or
        // * it is of type EQ, either completely positive or completely negative and the poly has a constant addend that cannot become 0
        switch (this.type) {
        case GE : {
            return this.varPoly.getConstantPart().getNumericalAddend().signum() < 0 &&
                    this.varPoly.allNegative();
        }
        case GT : {
            return this.varPoly.allNegative();
        }
        case EQ : {
            return this.varPoly.getConstantPart().getNumericalAddend().signum() != 0 &&
                    (this.varPoly.allNegative() || this.varPoly.allPositive());
        }
        default :
            throw new RuntimeException("Unknown type " + this.type);
        }
    }


    @Override
    public int hashCode() {
        if (this.hashValid) {
            return this.hashValue;
        }
        this.computeHashValue();
        return this.hashValue;
    }

    private void computeHashValue() {
        this.hashValue = this.varPoly.hashCode() + 2*this.type.hashCode();
        this.hashValid = true;
    }

    @Override
    public boolean equals(Object o) {
        VarPolyConstraint constraint;

        if (! (o instanceof VarPolyConstraint)) {
            return false;
        }
        constraint = (VarPolyConstraint) o;

        // profit from our cached hash value
        if (constraint.hashCode() != this.hashCode()) {
            return false;
        }
        return ( constraint.type.equals( this.type ) &&
                 constraint.varPoly.equals( this.varPoly ) );
    }

    @Override
    public String toString() {
        return this.varPoly.toString()+" "+this.type+" 0";
    }


    /**
     * @return a RedLog representation of this (can be used with the
     *  computer algebra system "Reduce")
     * @see #toRedLog(Set)
     */
    public String toRedLog() {
        // the current implementation of toString() should do the trick
        return this.toString();
    }


    /**
     * Export the conjunction of <code>vpcs</code> in such a way that
     * it is a valid Reduce program which can be used as input for Reduce.
     *
     * @param vpcs  non-null
     * @return
     */
    public static String toRedLogProgram(Set<VarPolyConstraint> vpcs) {
        // - get fresh name for constraint
        Set<String> varNames = new LinkedHashSet<String>();
        for (VarPolyConstraint vpc : vpcs) {
            VarPolynomial poly = vpc.varPoly;
            varNames.addAll(poly.getCoefficients());
            if (! VarPolyConstraint.ABS_POS) {
                varNames.addAll(poly.getVariables());
            }
        }
        String constraintName = "alpha";
        String cand = constraintName;
        int i = 0;
        while (varNames.contains(cand)) {
            cand = constraintName + i;
            ++i;
        }
        constraintName = cand;

        // - the actual constraint
        String constraint = VarPolyConstraint.toRedLog(vpcs);

        // - assemble result
        StringBuilder b = new StringBuilder();
        b.append("load redlog; rlset ofsf; ");
        b.append(constraintName);
        b.append(" := ");
        b.append(constraint);
        b.append("; on rlqeaprecise; on time; off nat; rlqea ");
        b.append(constraintName);
        b.append(';');
        return b.toString();
    }

    /**
     * Export the conjunction of <code>vpcs</code> in such a way that RedLog
     * (a part of the computer algebra system Reduce) can handle it.
     *
     * @param vpcs  non-null
     * @return
     */
    public static String toRedLog(Set<VarPolyConstraint> vpcs) {

        // - get existentially quantified variables
        // - get universally quantified variables
        Set<String> exVars = new LinkedHashSet<String>();
        Set<String> univVars = new LinkedHashSet<String>();
        for (VarPolyConstraint vpc : vpcs) {
            VarPolynomial poly = vpc.varPoly;
            exVars.addAll(poly.getCoefficients());
            if (! VarPolyConstraint.ABS_POS) {
                univVars.addAll(poly.getVariables());
            }
        }

        // - enforce that these two sets are disjoint (maybe rename
        //   some universally quantified variables; maybe throw
        //   IllegalArgumentException)
        boolean disjoint = Collections.disjoint(exVars, univVars);
        if (!disjoint) {
            throw new IllegalArgumentException("Sets of existential variables "
                    + exVars + " and universal variables " + univVars
                    + " must be disjoint!");
        }

        StringBuilder res = new StringBuilder();

        // - export quantifier prefix
        VarPolyConstraint.appendRegLogQuantifierPrefix(exVars, true, res);
        if (! VarPolyConstraint.ABS_POS) {
            VarPolyConstraint.appendRegLogQuantifierPrefix(univVars, false, res);
        }

        // - ex. quant. vars must be >= 0
        for (String a : exVars) {
            res.append(a);
            res.append(" >= 0 and ");
        }

        // - maybe require ex. quant. vars to be <= 2*10^9
        //   (or some other finite, but very high value)
        /*
        final int MAX_SOLUTION = 2000000000;
        for (String a : exVars) {
            res.append(MAX_SOLUTION);
            res.append(" >= ");
            res.append(a);
            res.append(" and ");
        }
        */

        // - if univ. quant vars are all >= 0 ...
        boolean hasUnivVars = ! univVars.isEmpty();
        if (hasUnivVars) {
            // will need implication only if there is a premise
            res.append('(');
            boolean first = true;
            for (String x : univVars) {
                if (first) {
                    first = false;
                }
                else {
                    res.append(" and ");
                }
                res.append(x);
                res.append(" >= 0");
            }
            res.append(" impl ");
        }

        // - ... then require actual conjunction of atoms
        res.append('(');
        boolean first = true;
        for (VarPolyConstraint vpc : vpcs) {
            if (first) {
                first = false;
            }
            else {
                res.append(" and ");
            }
            if (VarPolyConstraint.ABS_POS) {
                SimplePolynomial constant = vpc.varPoly.getConstantPart();
                res.append(constant.toString());
                res.append(' ');
                res.append(vpc.type);
                res.append(" 0");

                Set<SimplePolynomial> varCoeffs = vpc.varPoly.getCoefficientsOfVariables();
                ConstraintType simpleType = vpc.type == ConstraintType.GT ? ConstraintType.GE : vpc.type;
                for (SimplePolynomial varCoeff : varCoeffs) {
                    res.append(" and ");
                    res.append(varCoeff.toString());
                    res.append(' ');
                    res.append(simpleType);
                    res.append(" 0");
                }
            }
            else {
                res.append(vpc.toRedLog());
            }
        }
        res.append(')');

        // - close impl and "all" quantifier paren
        if (hasUnivVars) {
            res.append("))");
        }

        // - close paren of "ex" quantifier prefix
        res.append(')');

        return res.toString();
    }

    /**
     * Appends quantifier prefix for all vars to buffer.
     *
     * @param vars
     * @param existential - existential or universal quantifier?
     * @param buffer - side effect: output is appended here
     */
    private static void appendRegLogQuantifierPrefix(Iterable<String> vars,
            boolean existential, StringBuilder buffer) {
        String keyword = existential ? "ex" : "all";
        buffer.append(keyword);
        buffer.append("({");
        boolean first = true;
        for (String a : vars) {
            if (first) {
                first = false;
            }
            else {
                buffer.append(',');
            }
            buffer.append(a);
        }
        buffer.append("}, ");
    }
}
