/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.dpframework.DPProblem.SMT_LIA.SMTLIB;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.SMT_LIA.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Monoids.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Logic.*;

/**
 * Abstract implementation of the ISMTChecker interface using SMTLIB-compatible
 * solvers.
 *
 * For a full implementation, just the call to the solver must be implemented.
 *
 * @author noschinski
 */
public abstract class AbstractChecker implements ISMTChecker {

    /* Just needed for the flattening visitor over polynomials in the
     * LIAConstraints. */
    private final Ring<BigIntImmutable>
        ring = new BigIntImmutableRing();
    private final CMonoid<GMonomial<GPolyVar>>
        monoid = new GMonomialMonoid<GPolyVar>();
    private final GPolyFlatRing<BigIntImmutable, GPolyVar>
        flatring = new SimpleGPolyFlatRing<BigIntImmutable, GPolyVar>(this.ring, this.monoid);
    private final FlatteningVisitor<BigIntImmutable, GPolyVar>
        flattener = new FlatteningVisitor<BigIntImmutable, GPolyVar>(this.flatring);

    /**
     * Converts atomar constraint to an SMTLIB term.
     *
     * @param s Append term to this StringBuilder
     * @param c Constraint to convert
     * @param varMapper
     */
    private void buildAtom(StringBuilder s, LIAConstraint c, SMTLIBVarMapper<GPolyVar> varMapper) {
        GPoly<BigIntImmutable, GPolyVar> left = c.getLeft();
        GPoly<BigIntImmutable, GPolyVar> right = c.getRight();

        SMTLIBConverterVisitor<BigIntImmutable, GPolyVar> converter;

        /* SMTLIB input allows only n_1*x_1 + ... nk_*x_k as input for QF_LIA, so we
         * need to flatten the polynomial. Obviously, flattening gives the form above
         * only for linear polynomials - but constraints with non-linear polynomials
         * are invalid input. */
        this.flattener.applyTo(left);
        this.flattener.applyTo(right);

        s.append("(");
        s.append(c.getRelation().getRepr());
        s.append(" ");

        converter = new SMTLIBConverterVisitor<BigIntImmutable, GPolyVar>(varMapper);

        converter.applyTo(left);
        s.append(converter.getSource());

        s.append(" ");

        converter.clearSource();
        converter.applyTo(right);
        s.append(converter.getSource());

        s.append(")");

    }

    /**
     * Creates a satisfiability test in SMTLIB format.
     *
     * The output of this method can be fed to any SMT solver supporting the
     * SMTLIB input format.
     *
     * @param formula Formula to test for satisifability
     * @param varMapper
     * @return SMTLIB source for the test.
     */
    private String buildBenchmark(ImmutableBoolOp<LIAConstraint> formula, SMTLIBVarMapper<GPolyVar> varMapper) {
        StringBuilder s = new StringBuilder();
        s.append("(benchmark foo\n");
        s.append(":logic QF_LIA\n");

        StringBuilder ss = new StringBuilder();
        this.buildSubformula(ss, formula, varMapper);

        for (GPolyVar v : varMapper.getVariables()) {
            s.append(":extrafuns ((");
            s.append(varMapper.getName(v));
            s.append(" Int))\n");
        }

        s.append(":formula\n");
        s.append(ss);

        s.append(")");

        return s.toString();
    }

    /**
     * Represent formula in SMTLIB format.
     *
     * Builds a representation of the formula as a SMTLIB formula as described in
     * "Concrete Syntax for formulas" in the SMT-LIB standard 1.2
     *
     * @param s Append formula to this StringBuilder
     * @param varMapper
     */
    private void buildSubformula(StringBuilder s,
            ImmutableBoolOp<LIAConstraint> formula, SMTLIBVarMapper<GPolyVar> varMapper) {

        if (formula.isNegation()) {
            s.append("(not ");
            this.buildSubformula(s, formula.getSubformulas().get(0), varMapper);
            s.append(")");
        } else if (formula.isAtom()) {
            this.buildAtom(s, formula.getLiteral(), varMapper);
        } else if (formula.isObviouslyFalse()) {
            s.append("false");
        } else if (formula.isObviouslyTrue()) {
            s.append("true");
        } else {
            if (formula.isConjunction()) {
                s.append("(and");
            } else {
                s.append("(or");
            }

            for (ImmutableBoolOp<LIAConstraint> sf : formula.getSubformulas()) {
                s.append(" ");
                this.buildSubformula(s, sf, varMapper);
            }

            s.append(")");

        }
    }

    /**
     * Call SMTLIB solver.
     *
     * @param benchmark Input in SMTLIB format
     * @param aborter Use to abort the solver early.
     * @return YES, if the benchmark is satisfiable, NO if the benchmark is unsatisfiable,
     *    MAYBE in all other cases (including errors).
     * @throws AbortionException
     */
    protected abstract YNM callSolver(String benchmark, Abortion aborter) throws AbortionException;

    /**
     * Test satisifiability of formula.
     *
     * Calls an external SMTLIB-compatible solver to determine the satisfiability
     * of formula. Formula must be over quantifier free linear integer arithmetic (QF_LIA).
     *
     * @param aborter Use to abort the solver early.
     * @throws AbortionException
     */
    @Override
    public YNM isSatisfiable(final ImmutableBoolOp<LIAConstraint> formula, final Abortion aborter)
            throws AbortionException {
        SMTLIBVarMapper<GPolyVar> varMapper = new SMTLIBVarMapper<GPolyVar>();
        String smtlib_bm = this.buildBenchmark(formula, varMapper);
        return this.callSolver(smtlib_bm, aborter);
    }


}
