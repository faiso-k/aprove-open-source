package aprove.verification.oldframework.PropositionalLogic.TheoryPropositions;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * An atomic Diophantine constraint:   p ~ q<br>
 *   - p, q are multivariate polynomials where all addends
 *     have only positive factors<br>
 *   - ~ \in {>, >=, =}
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class Diophantine implements TheoryProposition, Immutable {

    private final SimplePolynomial left;
    private final SimplePolynomial right;
    private final ConstraintType relation;
    private final int hashValue;

    private Diophantine(final SimplePolynomial left, final SimplePolynomial right,
            final ConstraintType relation) {
        if (Globals.useAssertions) {
            assert left != null;
            assert right != null;
            assert relation != null;
            assert left.allPositive();
            assert right.allPositive();
        }
        this.left = left;
        this.right = right;
        this.relation = relation;
        this.hashValue = left.hashCode() + 31 * right.hashCode() + 87 * relation.hashCode();
    }

    /**
     * @param left - non-null, must not contain negative coefficients
     * @param right - non-null, must not contain negative coefficients
     * @param relation
     * @return a fresh Diophantine proposition "left relation right"
     */
    public static Diophantine create(final SimplePolynomial left, final SimplePolynomial right,
            final ConstraintType relation) {
        return new Diophantine(left, right, relation);
    }

    /**
     * @param leftMinusRight - non-null
     * @param relation
     * @return a fresh Diophantine proposition that is equivalent to
     *  "leftMinusRight relation 0"
     */
    public static Diophantine create(final SimplePolynomial leftMinusRight,
            final ConstraintType relation) {
        final Pair<SimplePolynomial, SimplePolynomial> pair = leftMinusRight.toPositivePair();
        return new Diophantine(pair.x, pair.y, relation);
    }


    /**
     * @param spc - non-null
     * @return a fresh Diophantine proposition that is equivalent to spc
     * @deprecated using this method is not recommended because
     *  there is no such thing as an SPC with constraint type GT.
     *  hence, rather use create(SP, CT)
     */
    @Deprecated
    public static Diophantine create(final SimplePolyConstraint spc) {
        // TODO maybe do some preprocessing to make a wise choice
        // between >= and >.
        final Pair<SimplePolynomial, SimplePolynomial> pair = spc.getPolynomial().toPositivePair();
        return new Diophantine(pair.x, pair.y, spc.getType());
    }


    /**
     * @return the left hand side of this
     */
    public SimplePolynomial getLeft() {
        return this.left;
    }

    /**
     * @return the right hand side of this
     */
    public SimplePolynomial getRight() {
        return this.right;
    }

    /**
     * @return the relation between the lhs and the rhs of this
     */
    public ConstraintType getRelation() {
        return this.relation;
    }

    public Diophantine substitute(final Map<String, SimplePolynomial> substitution) {
        Diophantine result = null;
        try {
            result = this.substitute(substitution, AbortionFactory.create());
        } catch (final AbortionException e) {
            throw new RuntimeException(e);
        }
        return result;
    }

    public Diophantine substitute(final Map<String, SimplePolynomial> substitution,
        final Abortion aborter) throws AbortionException {
        final Pair<SimplePolynomial, SimplePolynomial> p =
            this.left.substitute(substitution, aborter).minus(
                this.right.substitute(substitution, aborter)).toPositivePair();
        return Diophantine.create(p.x, p.y, this.relation);
    }

    public SimplePolyConstraint toSimplePolyConstraint() {
        SimplePolynomial poly = this.left.minus(this.right);
        return new SimplePolyConstraint(poly, this.relation);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        return this.hashValue;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(final Object other) {
        if (this == other) {
            return true;
        }
        if (!(other instanceof Diophantine)) {
            return false;
        }
        final Diophantine dio = (Diophantine) other;
        if (this.hashValue != dio.hashValue) {
            return false;
        }
        if (this.relation.equals(dio.relation) && this.left.equals(dio.left)
                && this.right.equals(dio.right)) {
            return true;
        }
        return false;
    }

    @Override
    public String toString() {
        String relSym;
        switch (this.relation) {
        case EQ:
            relSym = " = ";
            break;
        case GE:
            relSym = " >= ";
            break;
        case GT:
            relSym = " > ";
            break;
        default:
            throw new RuntimeException(this.relation +
                    " unknown as of now, check code!");
        }
        return this.left + relSym + this.right;
    }

    public SMTLIBIntCMP toSMTLIB() {
        final SMTLIBIntValue leftSMT, rightSMT;
        leftSMT = this.left.toSMTLIB();
        rightSMT = this.right.toSMTLIB();
        switch (this.relation) {
        case EQ :
            return SMTLIBIntEquals.create(leftSMT, rightSMT);
        case GE :
            return SMTLIBIntGE.create(leftSMT, rightSMT);
        case GT :
            return SMTLIBIntGT.create(leftSMT, rightSMT);
        default:
            throw new RuntimeException(this.relation +
            " unknown as of now, check code!");
        }
    }

}
