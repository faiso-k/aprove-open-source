/**
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;

/**
 * A SMTLIBConverterVisitor generates a presentation of the GPoly in SMTLIB format
 *
 * @author noschinski
 * @version $Id$
 *
 * @param <C> The type of the coefficients.
 * @param <V> The type of the variables.
 */
public class SMTLIBConverterVisitor<C extends GPolyCoeff & SMTLIBFormatter, V extends GPolyVar>
    extends GPolyVisitor<C, V> {

    /**
     * Representation of the polynomial in SMTLIB format.
     */
    private StringBuffer source;

    /**
     * Maps variables to a textual representation in the generated source string.
     */
    final private SMTLIBVarMapper<V> varMapper;

    /**
     * Build a FlatteningVisitor that operates based on the given rings and the
     * monoid.
     * @param polyRingParam A ring for flat polynomials.
     */
    public SMTLIBConverterVisitor(SMTLIBVarMapper<V> varMapper) {
        this.source = new StringBuffer();
        this.varMapper = varMapper;
    }

    /**
     * Truncates the getSource() output.
     *
     * @see getSource
     */
    public void clearSource() {
        this.source = new StringBuffer();
    }

    /**
     * Returns the textual SMTLIB representation of the polynomial.
     *
     * The return value is only useful, after the visitor's applyTo method
     * was called.
     *
     * Note: The source string is not truncated between mulitple applyTo calls;
     * this must be done manually by calling clearSource().
     */
    public String getSource() {
        return this.source.toString();
    }

    @Override
    public void fcaseConcatNode(ConcatNode<C, V> c) {
        C coeff = c.getCoeff();
        VarPartNode<V> vp = c.getVarPartNode();
        if (coeff == null && vp == null) {
            /* This node represents "1" */
            this.source.append(" 1");
        } else if (coeff == null) {
            /* A null coefficient represents the One in the ring C */
            SMTLIBConverterVarPartVisitor<V> vpv =
                new SMTLIBConverterVarPartVisitor<V>(this.varMapper);
            vpv.applyTo(vp);
            this.source.append(vpv.getSource());
        } else if (vp.getVar() == null && vp.isLeaf()) {
            /* No variables */
            this.source.append(" ");
            this.source.append(coeff.toSMTLIB());
        } else {
            this.source.append(" (* ");
            this.source.append(coeff.toSMTLIB());
            this.source.append(" ");

            SMTLIBConverterVarPartVisitor<V> vpv =
                new SMTLIBConverterVarPartVisitor<V>(this.varMapper);
            vpv.applyTo(vp);

            this.source.append(vpv.getSource());
            this.source.append(")");
        }
    }

    @Override
    public void fcasePlusNode(PlusNode<C, V> p) {
        this.source.append(" (+");
    }

    /**
     * Add the two children of the PlusNode using the given polynomial ring.
     * @param p The PlusNode being visited.
     * @param left The possibly new left child.
     * @param right The possibly new right child.
     * @return p with flat representation.
     */
    @Override
    public PlusNode<C, V> casePlusNode(
            final PlusNode<C, V> p,
            final GPoly<C, V> left,
            final GPoly<C, V> right) {
        this.source.append(")");
        return p;
    }

    @Override
    public void fcaseMinusNode(MinusNode<C, V> m) {
        this.source.append(" (-");
    }

    @Override
    public MinusNode<C, V> caseMinusNode(
            final MinusNode<C, V> m,
            final GPoly<C, V> left,
            final GPoly<C, V> right) {
        this.source.append(")");
        return m;
    }

    @Override
    public void fcaseTimesNode(TimesNode<C, V> t) {
        this.source.append(" (*");
    }

    @Override
    public TimesNode<C, V> caseTimesNode(
            final TimesNode<C, V> t,
            final GPoly<C, V> left,
            final GPoly<C, V> right) {
        this.source.append(")");
        return t;
    }
}
