package aprove.verification.oldframework.IRSwT.Engines.FormulaGenerators;

import java.util.*;

import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IRSwT.Engines.Formulae.*;

/**
 * A formula generator should reformulate given statement of the form
 * /\phi -> p >= 0 (*)
 * into a statement psi s.t. all models of psi imply (*).
 * Here p = p(x_1, .., x_n, c_1, .., c_k), psi = psi(c_1, .., (c_k, d_1, .., d_l)) and
 * PHI set of formulae over x_1, .., x_n,
 * where x_1, .., x_n are rule variables while c_1,.. c_k are fresh coefficient variables.
 * @author Matthias Hoelzel
 */
public abstract class AbstractFormulaGenerator {
    /**
     * Set of preconditions.
     */
    protected Set<Atom> phi;

    /**
     * Some polynomial we want to be >= 0.
     */
    protected VarPolynomial p;

    /**
     * The result formula.
     */
    private AbstractFormula<Atom> psi;

    /**
     * Constructor!
     * @param atoms the phi
     * @param poly the p
     */
    public AbstractFormulaGenerator(final Set<Atom> atoms, final VarPolynomial poly) {
        this.phi = atoms;
        this.p = poly;
        this.psi = null;
    }

    /**
     * Calculate the formula psi!
     * @return a formula
     */
    public final AbstractFormula<Atom> generateFormula() {
        if (this.psi == null) {
            this.psi = this.calculateFormula();
        }
        return this.psi;
    }

    /**
     * Calculate the formula psi! To be implemented by a concrete formula generator!
     * @return a formula
     */
    protected abstract AbstractFormula<Atom> calculateFormula();
}
