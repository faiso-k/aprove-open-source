package aprove.verification.oldframework.IRSwT.Engines.FormulaGenerators;

import java.util.*;

import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IRSwT.Engines.Formulae.*;
import aprove.verification.oldframework.IRSwT.Engines.Formulae.Atom.*;
import aprove.verification.oldframework.Utility.*;

/**
 * A quite simple formula generator!
 *
 * To understand what a formula generator does, read
 * the javadoc of AbstractFormulaGenerator!
 *
 * This just uses the non-negative linear combination of the phi-atoms
 * to generate a system of equalities and inequalities implying that
 * the given polynomial is >= 0. This system will contain non-linear arithmetic
 * iff the input polynomial has non-linear coefficient terms.
 *
 * @author Matthias Hoelzel
 *
 */
public class SimpleFormulaGenerator extends AbstractFormulaGenerator {
    /**
     * The transformed atoms. Here we only store the left sides.
     */
    LinkedHashSet<VarPolynomial> phiPrime;

    /**
     * Some name generator!
     */
    FreshNameGenerator fng;

    /**
     * Constructor!
     * @param atoms the phi
     * @param poly the p
     * @param gen name generator
     */
    public SimpleFormulaGenerator(final Set<Atom> atoms, final VarPolynomial poly, final FreshNameGenerator gen) {
        super(atoms, poly);
        this.phiPrime = new LinkedHashSet<>();
        this.fng = gen;
    }

    @Override
    protected AbstractFormula<Atom> calculateFormula() {
        // 1. Process atoms
        this.processAtoms();

        // 2. Compute formula
        return this.computePsi();
    }

    /**
     * Finds a set of polynomials that are >= 0.
     */
    private void processAtoms() {
        for (final Atom a : this.phi) {
            final VarPolynomial left = a.getLeftPoly();
            final VarPolynomial right = a.getRightPoly();
            switch (a.getType()) {
            case ATOM_EQ:
                this.phiPrime.add(left.minus(right));
                this.phiPrime.add(right.minus(left));
                break;
            case ATOM_GE:
                this.phiPrime.add(left.minus(right));
                break;
            case ATOM_GT:
                this.phiPrime.add(left.minus(right).minus(VarPolynomial.ONE));
                break;
            case ATOM_LE:
                this.phiPrime.add(right.minus(left));
                break;
            case ATOM_LT:
                this.phiPrime.add(right.minus(left).minus(VarPolynomial.ONE));
                break;
            default:
                assert false : "Default?!?";
            }
        }
    }

    /**
     * Compute a psi as described in the javadoc of AbstractFormulaGenerator!
     * @return the psi
     */
    private AbstractFormula<Atom> computePsi() {
        final LinkedList<VarPolynomial> coefficients = new LinkedList<>();

        final String constantCoeff = this.fng.getFreshName("d", false);
        VarPolynomial combination = VarPolynomial.createCoefficient(constantCoeff);
        coefficients.add(combination);

        for (final VarPolynomial left : this.phiPrime) {
            final String coeffName = this.fng.getFreshName("d", false);
            final VarPolynomial coeffPoly = VarPolynomial.createCoefficient(coeffName);
            coefficients.add(coeffPoly);
            combination = combination.plus(left.times(coeffPoly));
        }
        final VarPolynomial diff = this.p.minus(combination);

        final AbstractFormula<Atom> eqZeroFormula = this.forceEQZero(diff);
        final AbstractFormula<Atom> geZeroFormula = this.forceGEZero(coefficients);

        final AbstractFormula<Atom> result = new AndFormula<>(eqZeroFormula, geZeroFormula);
        return result;
    }

    /**
     * Builds a formula that expresses that every polynomials is >= 0
     * @param coefficients collection of polynomials
     * @return a formula over atoms of type Atom
     */
    private AbstractFormula<Atom> forceGEZero(final Collection<VarPolynomial> coefficients) {
        AbstractFormula<Atom> result = new TrueFormula<>();
        for (final VarPolynomial vp : coefficients) {
            final Atom at = new Atom(vp, AtomType.ATOM_GE, VarPolynomial.ZERO);
            final AtomFormula<Atom> form = new AtomFormula<>(at);

            result = new AndFormula<>(result, form);
        }

        return result;
    }

    /**
     * Builds a formula that expresses that the given polynomial equals 0.
     * @param poly the given polynomial
     * @return a formula over atoms of type Atom
     */
    private AbstractFormula<Atom> forceEQZero(final VarPolynomial poly) {
        AbstractFormula<Atom> result = new TrueFormula<>();
        for (final SimplePolynomial simple : poly.getVarMonomials().values()) {
            final VarPolynomial simplePoly = VarPolynomial.create(simple);
            final Atom at = new Atom(simplePoly, AtomType.ATOM_EQ, VarPolynomial.ZERO);
            final AtomFormula<Atom> atForm = new AtomFormula<>(at);

            result = new AndFormula<>(result, atForm);
        }

        return result;
    }
}
