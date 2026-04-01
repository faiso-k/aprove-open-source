package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import immutables.*;

public interface Constraint extends Immutable, TRSVisitable, Exportable {

    boolean isAtom();

    boolean isTermAtom();

    boolean isReducesTo();

    boolean isPredicate();

    boolean isImplication();

    boolean isConstraintSet();

    boolean isPolyAtom();

    boolean isUsableAtom();

    Object setTag(InfRuleID infRule, Object tag);

    Object getTag(InfRuleID infRule);

    Set<GPolyVar> getPolyVariables();

    boolean collectMatchMap(Constraint constraint, Map<TRSVariable, TRSTerm> map);

    /**
     * if sigma is the solution of the ConstraintUnifyProblem
     * and its domain is a subset of yes then
     * the implication (this * sigma ==> con * sigma) holds.
     * @param multiSet TODO
     */
    //    boolean collectUnifyProblemForImplication(Vector<Variable> yes,Vector<Variable> no,List<ConstraintUnifyProblem> cups,Constraint con, boolean multiSet);

    /**
     * if sigma is the solution of the ConstraintUnifyProblem
     * then this * sigma = con * sigma holds.
     * @param multiSet TODO
     */
    //    boolean collectUnifyProblemForEquivalenz(List<ConstraintUnifyProblem> cups,Constraint con);

    public static abstract class ConstraintSkeleton extends TRSVisitable.TRSVisitableSkeleton implements Constraint {

        private final Map<InfRuleID, Object> tags;

        public ConstraintSkeleton() {
            this.tags = new LinkedHashMap<InfRuleID, Object>();
        }

        @Override
        public boolean isAtom() {
            return false;
        }

        @Override
        public boolean isTermAtom() {
            return false;
        }

        @Override
        public boolean isPredicate() {
            return false;
        }

        @Override
        public boolean isReducesTo() {
            return false;
        }

        @Override
        public boolean isImplication() {
            return false;
        }

        @Override
        public boolean isConstraintSet() {
            return false;
        }

        @Override
        public boolean isPolyAtom() {
            return false;
        }

        @Override
        public boolean isUsableAtom() {
            return false;
        }

        @Override
        public Object setTag(InfRuleID infRule, Object tag) {
            return this.tags.put(infRule, tag);
        }

        @Override
        public Object getTag(InfRuleID infRule) {
            return this.tags.get(infRule);
        }

    }

}
