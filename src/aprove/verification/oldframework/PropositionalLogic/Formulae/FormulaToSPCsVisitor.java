/**
 * @author cotto
 * @version $Id$
 */

package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Convert the given Formula over Diophantine atoms to two sets of
 * SimplePolyConstraints where the second set is used for SEARCHSTRICT.
 * ATTENTION: This visitor may only be used on formulae that can be transformed
 * to the two sets. For weird formulae this visitor returns weird results.
 * @author cotto
 */
public class FormulaToSPCsVisitor
    implements FormulaVisitor<Object, Diophantine> {
    /**
     * The result.
     */
    private final Pair<Set<SimplePolyConstraint>,
        Set<SimplePolyConstraint>> pair;

    /**
     * This will be set if a NOT node was seen on the path.
     */
    private boolean behindNot = false;

    private Set<String> variables;

    /**
     * Initialize the resulting pair.
     */
    public FormulaToSPCsVisitor() {
        Set<SimplePolyConstraint> a = new LinkedHashSet<SimplePolyConstraint>();
        Set<SimplePolyConstraint> b = new LinkedHashSet<SimplePolyConstraint>();
        this.pair =
            new Pair<Set<SimplePolyConstraint>, Set<SimplePolyConstraint>>(
                    a, b);
        this.variables = new LinkedHashSet<String>();
    }

    /**
     * An and node is being visited.
     * @param f The and node.
     * @return null.
     */
    @Override
    public Object caseAnd(final AndFormula<Diophantine> f) {
        for (Formula<Diophantine> arg : f.args) {
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
    public Object caseConstant(final Constant<Diophantine> f) {
        throw new UnsupportedOperationException();
    }

    /**
     * An iff node is being visited.
     * @param f the iff node.
     * @throws UnsupportedOperationException
     */
    @Override
    public Object caseIff(final IffFormula<Diophantine> f) {
        throw new UnsupportedOperationException();
    }

    /**
     * An ite note is being visited.
     * @param f the ite node.
     * @throws UnsupportedOperationException
     */
    @Override
    public Object caseIte(final IteFormula<Diophantine> f) {
        throw new UnsupportedOperationException();
    }

    /**
     * A not node is being visited. Remember this so that the diophantine
     * constraints below this node will be regarded as searchstrict constraints.
     * @param f the not node.
     * @return null.
     */
    @Override
    public Object caseNot(final NotFormula<Diophantine> f) {
        if (Globals.useAssertions) {
            assert (!this.behindNot);
        }
        this.behindNot = true;
        f.arg.apply(this);
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
    public Object caseOr(final OrFormula<Diophantine> f) {
        throw new UnsupportedOperationException();
    }

    /**
     * An atom is being visited. Stick this diophantine constraint into the
     * correct set of simple poly constraints.
     * @param f the atom node.
     * @return null.
     */
    @Override
    public Object caseTheoryAtom(final TheoryAtom<Diophantine> f) {
        Diophantine dio = f.getProposition();
        SimplePolynomial poly = dio.getLeft().minus(dio.getRight());
        this.variables.addAll(poly.getIndefinites());
        ConstraintType ct = dio.getRelation();
        if (this.behindNot) {
            SimplePolyConstraint spc =
                new SimplePolyConstraint(poly, ConstraintType.GE);
            this.pair.y.add(spc);
        } else {
            SimplePolyConstraint spc = new SimplePolyConstraint(poly, ct);
            this.pair.x.add(spc);
        }
        return null;
    }

    /**
     * A variable is being visited.
     * @param f The variable.
     * @throws UnsupportedOperationException
     */
    @Override
    public Object caseVariable(final Variable<Diophantine> f) {
        throw new UnsupportedOperationException();
    }

    /**
     * A xor node is being visited.
     * @param f the xor node.
     * @throws UnsupportedOperationException
     */
    @Override
    public Object caseXor(final XorFormula<Diophantine> f) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Object caseAtLeast(AtLeastFormula<Diophantine> f) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Object caseAtMost(AtMostFormula<Diophantine> f) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Object caseCount(CountFormula<Diophantine> f) {
        throw new UnsupportedOperationException();
    }

    /**
     * @return the pair containing the simple poly constraints.
     */
    public Pair<Set<SimplePolyConstraint>, Set<SimplePolyConstraint>>
        getPair() {
        return this.pair;
    }

    public Set<String> getVariables() {
        return this.variables;
    }

}
