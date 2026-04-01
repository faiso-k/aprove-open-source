package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.BasicStructures.*;

public class Predicate extends TermAtom.TermAtomSkeleton implements HasTRSTerms, HasVariables {
    public static enum Kind {
        AbstractRelation, AbstractRelationEQ, NonInfConstantCompare
    } // unused: ,IntGreater,IntGreaterEqual,IntEqual,IntLess,IntLessEqual

    Kind kind;
    final GeneralizedRule origRule;
    protected final RelDependency uLeft;
    protected final RelDependency uRight;

    public Kind getKind() {
        return this.kind;
    }

    protected Predicate(TRSTerm s, TRSTerm t, Kind kind, GeneralizedRule origRule, RelDependency uLeft, RelDependency uRight)
    {
        super(s, t);
        this.kind = kind;
        this.origRule = origRule;
        this.uLeft = uLeft;
        this.uRight = uRight;
    }

    public static Predicate create(
        TRSTerm s,
        TRSTerm t,
        Kind kind,
        GeneralizedRule origRule,
        RelDependency uLeft,
        RelDependency uRight)
    {
        return new Predicate(s, t, kind, origRule, uLeft, uRight);
    }

    /**public static Predicate create(Term s, Term t) {
        return Predicate.create(s,t,Kind.OrderGreaterThan);
    }**/

    @Override
    public boolean isPredicate() {
        return true;
    }

    public GeneralizedRule getOrigRule() {
        return this.origRule;
    }

    public RelDependency getULeft() {
        return this.uLeft;
    }

    public RelDependency getURight() {
        return this.uRight;
    }

    @Override
    public TRSVisitable visit(DPConstraintVisitor dpcv) {
        dpcv.fcaseTermAtom(this);
        dpcv.fcasePredicate(this);
        return dpcv.casePredicate(this);
    }

    @Override
    public TRSVisitable applySubstitution(TRSSubstitution subs, boolean idpMode) {
        return Predicate.create(
            this.getLeft().applySubstitution(subs),
            this.getRight().applySubstitution(subs),
            this.getKind(),
            this.origRule,
            this.uLeft,
            this.uRight);
    }

    /**
    @Override
    public boolean collectUnifyProblemForImplication(Vector<Variable> yes,Vector<Variable> no,List<ConstraintUnifyProblem> cups,Constraint con, boolean multiSet) {
        if (!con.isPredicate()) {
            cups.clear();
            return false;
        }
        return super.collectUnifyProblemForImplication(yes,no,cups, con, multiSet);
    }

    @Override
    public boolean collectUnifyProblemForEquivalenz(List<ConstraintUnifyProblem> cups,Constraint con) {
        if (!con.isPredicate()) {
            cups.clear();
            return false;
        }
        return super.collectUnifyProblemForEquivalenz(cups,con);
    }
    **/

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder sb = new StringBuilder();
        sb.append(this.getLeft().export(o));
        if (this.kind == Kind.AbstractRelation) {
            sb.append(o.nonStrictRelativ());
        } else if (this.kind == Kind.AbstractRelationEQ) {
            sb.append(o.strictRelativ());
        } else if (this.kind == Kind.NonInfConstantCompare) {
            sb.append(o.nonStrictRelativ());
            sb.append("NonInfC");
        }
        if (this.kind != Kind.NonInfConstantCompare) {
            sb.append(this.getRight().export(o));
        }
        return sb.toString();
    }

    @Override
    public boolean collectMatchMap(Constraint constraint, Map<TRSVariable, TRSTerm> map) {
        if (constraint.isPredicate()) {
            Predicate p = (Predicate) constraint;
            if (!p.getKind().equals(this.kind)) {
                return false;
            }
            this.getLeft().extendMatchingSubstitution(map, p.getLeft());
            this.getRight().extendMatchingSubstitution(map, p.getRight());
            return true;
        }
        return false;
    }

    public TRSVisitable replaceAll(TRSTerm replace, TRSTerm replacement) {
        return Predicate.create(
            this.getLeft().replaceAll(replace, replacement),
            this.getRight().replaceAll(replace, replacement),
            this.getKind(),
            this.origRule,
            this.uLeft,
            this.uRight);
    }

    public Predicate change(TRSTerm newLeft, TRSTerm newRight, RelDependency uLeft, RelDependency uRight) {
        if (newLeft == null || this.left.equals(newLeft)) {
            newLeft = this.left;
        }
        if (newRight == null || this.right.equals(newRight)) {
            newRight = this.right;
        }
        if (uLeft == null) {
            uLeft = this.uLeft;
        }
        if (uRight == null) {
            uRight = this.uRight;
        }
        if (this.left == newLeft && this.right == newRight && uLeft == this.uLeft && uRight == this.uRight) {
            return this;
        } else {
            return new Predicate(newLeft, newRight, this.kind, this.origRule, uLeft, uRight);
        }
    }

    @Override
    public TermAtom change(TRSTerm newLeft, TRSTerm newRight) {
        return this.change(newLeft, newRight, null, null);
    }

    @Override
    public Set<GPolyVar> getPolyVariables() {
        return Collections.<GPolyVar>emptySet();
    }

}
