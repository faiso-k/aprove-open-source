package aprove.verification.dpframework.Orders;

import java.math.*;
import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Matrices.*;
import aprove.verification.oldframework.Algebra.Matrices.Interpretation.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * Actually represents a matrix order.
 *
 * @author Patrick Kabasci
 * @version $Id: MATRO.java,v 1.8 2008/11/17 17:43:32 cotto Exp $
 */
public class PolComplexityMATRO extends AbstractMATRO {


    private final TermInterpretor interpretor;
    private final Map<Constraint<TRSTerm>, Collection<Constraint<TRSTerm>>> hardCodedRelations;

    private PolComplexityMATRO(final SymbolRepresentations representation, final TermInterpretor ti, final Map<String, BigInteger> result, final Map<Constraint<TRSTerm>, Collection<Constraint<TRSTerm>>> hardCodedRelations, final ActiveResolver activeResolver) {
        super(representation, activeResolver);
        this.interpretor =  new TermInterpretor (ti, result);
        this.hardCodedRelations = hardCodedRelations;
    }

    /**
     * Create a new matrix ordering based on a matrix representation.
     *
     * @param representation
     *            matrix representation of function symbols
     */
    public static PolComplexityMATRO create(final SymbolRepresentations representation, final TermInterpretor ti, final Map<String, BigInteger> result, final Map<Constraint<TRSTerm>, Collection<Constraint<TRSTerm>>> hardCodedRelations, final ActiveResolver activeResolver) {
        return new PolComplexityMATRO(representation, ti, result, hardCodedRelations, activeResolver);
    }

    @Override
    public boolean areEquivalent(final TRSTerm s, final TRSTerm t) {
        final Matrix leftM = this.interpretor.interpretTerm(s, 1, null, s, t.getDepth() > s.getDepth()? -(t.getDepth() - s.getDepth()):0);
        final Matrix rightM = this.interpretor.interpretTerm(t,  1, null, t, s.getDepth() > t.getDepth()? -(s.getDepth() - s.getDepth()):0);
        return leftM.isGE(rightM) && !this.inRelation(s,t);
    }

    @Override
    public boolean inRelation(final TRSTerm s, final TRSTerm t) {
        final Constraint<TRSTerm> hre = Constraint.create(s,t,OrderRelation.GE);
        if (this.hardCodedRelations.containsKey(hre)) {

            boolean inRel = true;
            for (final Constraint<TRSTerm> cons: this.hardCodedRelations.get(hre)) {
                inRel = inRel && this.inRelation(cons.getLeft(), cons.getRight());
            }
            return inRel;
        } else {

            final Matrix leftM = this.interpretor.interpretTerm(s, 1, null, s, t.getDepth() > s.getDepth()? -(t.getDepth() - s.getDepth()):0);
            final Matrix rightM = this.interpretor.interpretTerm(t,  1, null, t, s.getDepth() > t.getDepth()? -(s.getDepth() - t.getDepth()):0);
            // Only [0,0] is regarded.
            return leftM.isGE(rightM) && (new VarPolyConstraint(leftM.get(0, 0).minus(rightM.get(0, 0)), ConstraintType.GT)).isValid();
        }
    }

    @Override
    public boolean solves(final Constraint<TRSTerm> c) {
        final TRSTerm s = c.x;
        final TRSTerm t = c.y;
        final Matrix leftM = this.interpretor.interpretTerm(s, 1, null, s, t.getDepth() > s.getDepth()? -(t.getDepth() - s.getDepth()):0);
        final Matrix rightM = this.interpretor.interpretTerm(t,  1, null, t, s.getDepth() > t.getDepth()? -(s.getDepth() - t.getDepth()):0);

        switch (c.getType()) {
        case GE:
            return leftM.isGE(rightM);
        case GR:
            return leftM.isGE(rightM) && (new VarPolyConstraint(leftM.get(0, 0).minus(rightM.get(0, 0)), ConstraintType.GT).isValid());
        case GENGR:
            return leftM.isGE(rightM) && !((new VarPolyConstraint(leftM.get(0, 0).minus(rightM.get(0, 0)), ConstraintType.GT).isValid()));
        case EQ:
            return leftM.isGE(rightM) && rightM.isGE(leftM);
        case NGE:
            return !leftM.isGE(rightM);
        default:
            throw new RuntimeException();
        }

    }

}

