/**
 * @author CKuknat
 */

package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Convert the given Formula over OrderPolyConstraint<MbyN>s atoms to two sets of
 * SimplePolyConstraints where the second set is used for SEARCHSTRICT.
 * ATTENTION: This visitor may only be used on formulae that can be transformed
 * to the two sets. For weird formulae this visitor returns weird results.
 * @author CKuknat
 */
public class FormulaToOPCsVisitor implements
        FormulaVisitor<Object, OPCAtom<MbyN>> {
    /**
     * The result.
     */
    private final Pair<Set<OPCAtom<MbyN>>, Set<OPCAtom<MbyN>>> pair;

    /**
     * This will be set if a NOT node was seen on the path.
     */
    private boolean behindNot = false;

    /**
     * Initialize the resulting pair.
     */
    public FormulaToOPCsVisitor() {
        Set<OPCAtom<MbyN>> a = new LinkedHashSet<OPCAtom<MbyN>>();
        Set<OPCAtom<MbyN>> b = new LinkedHashSet<OPCAtom<MbyN>>();
        this.pair =
 new Pair<Set<OPCAtom<MbyN>>, Set<OPCAtom<MbyN>>>(
                    a, b);
    }

    /**
     * An and node is being visited.
     * @param f The and node.
     * @return null.
     */
    @Override
    public Object caseAnd(final AndFormula<OPCAtom<MbyN>> f) {
        for (Formula<OPCAtom<MbyN>> arg : f.getArgs()) {
            arg.apply(this);
        }
        return null;
    }

    /**
     * A constant is being visited.
     * @param f The constant.
     * @throws UnsupportedOperationException
     */
    @Override
    public Object caseConstant(final Constant<OPCAtom<MbyN>> f) {
        throw new UnsupportedOperationException();
    }

    /**
     * An iff node is being visited.
     * @param f the iff node.
     * @throws UnsupportedOperationException
     */
    @Override
    public Object caseIff(final IffFormula<OPCAtom<MbyN>> f) {
        throw new UnsupportedOperationException();
    }

    /**
     * An ite note is being visited.
     * @param f the ite node.
     * @throws UnsupportedOperationException
     */
    @Override
    public Object caseIte(final IteFormula<OPCAtom<MbyN>> f) {
        throw new UnsupportedOperationException();
    }

    /**
     * A not node is being visited. Remember this so that the diophantine
     * constraints below this node will be regarded as searchstrict constraints.
     * @param f the not node.
     * @return null.
     */
    @Override
    public Object caseNot(final NotFormula<OPCAtom<MbyN>> f) {
        if (Globals.useAssertions) {
            assert (!this.behindNot);
        }
        this.behindNot = true;
        f.getArg().apply(this);
        if (Globals.useAssertions) {
            assert (this.behindNot);
        }
        this.behindNot = false;
        return null;
    }

    /**
     * An or node is being visited.
     * @param f the or node.
     * @throws UnsupportedOperationException
     */
    @Override
    public Object caseOr(final OrFormula<OPCAtom<MbyN>> f) {
        throw new UnsupportedOperationException();
    }

    /**
     * An atom is being visited. Stick this OrderPolyConstraint<MbyN> constraint into the
     * correct set of simple poly constraints.
     * @param f the atom node.
     * @return null.
     */
    @Override
    public Object caseTheoryAtom(final TheoryAtom<OPCAtom<MbyN>> f) {

        OPCAtom<MbyN> constraint = f.getProposition();
        ConstraintType ct = ((OPCAtom<MbyN>) constraint).getConstraintType();
        if (this.behindNot || ct == ConstraintType.GT) {
            if (ct == ConstraintType.GT) {
                this.pair.x.add(constraint);
            } else {
                // OPCAtom<MbyN> strictConstraint = new
                // OPCAtom<MbyN>(constraint.getLeftPoly(),
                // constraint.getRightPoly(), ConstraintType.GT);
                this.pair.y.add(constraint);
            }
        } else {
            this.pair.x.add(constraint);
        }
        return null;
    }

    /**
     * A variable is being visited.
     * @param f The variable.
     * @throws UnsupportedOperationException
     */
    @Override
    public Object caseVariable(final Variable<OPCAtom<MbyN>> f) {
        throw new UnsupportedOperationException();
    }

    /**
     * A xor node is being visited.
     * @param f the xor node.
     * @throws UnsupportedOperationException
     */
    @Override
    public Object caseXor(final XorFormula<OPCAtom<MbyN>> f) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Object caseAtLeast(AtLeastFormula<OPCAtom<MbyN>> f) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Object caseAtMost(AtMostFormula<OPCAtom<MbyN>> f) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Object caseCount(CountFormula<OPCAtom<MbyN>> f) {
        throw new UnsupportedOperationException();
    }

    /**
     * @return the pair containing the simple poly constraints.
     */
    public Pair<Set<OPCAtom<MbyN>>, Set<OPCAtom<MbyN>>>
        getPair() {
        return this.pair;
    }

}
