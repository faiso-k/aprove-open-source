package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.BasicStructures.*;

public class ReducesTo extends TermAtom.TermAtomSkeleton implements TermAtom, HasTRSTerms, HasVariables {
    final Count count;
    final Object id;
    final PredefinedFunction<? extends Domain> parentFunc;

    protected ReducesTo(TRSTerm s, TRSTerm t, PredefinedFunction<? extends Domain> parentFunc, Count count, Object id) {
        super(s, t);
        this.count = count;
        this.id = id;
        this.parentFunc = parentFunc;
    }

    /*
    public static ReducesTo create(Term s, Term t,Count count,Object id) {
        return create(s, t, null, count, id);
    }*/

    public static ReducesTo create(
        TRSTerm s,
        TRSTerm t,
        PredefinedFunction<? extends Domain> parentFunc,
        Count count,
        Object id)
    {
        return new ReducesTo(s, t, parentFunc, count, id);
    }

    @Override
    public boolean isReducesTo() {
        return true;
    }

    @Override
    public TRSVisitable applySubstitution(TRSSubstitution subs, boolean idpMode) {
        return ReducesTo.create(
            this.getLeft().applySubstitution(subs),
            this.getRight().applySubstitution(subs),
            this.parentFunc,
            this.count,
            this.id);
    }

    @Override
    public TRSVisitable visit(DPConstraintVisitor dpcv) {
        dpcv.fcaseTermAtom(this);
        dpcv.fcaseReducesTo(this);
        return dpcv.caseReducesTo(this);
    }

    /**
    @Override
    public boolean collectUnifyProblemForImplication(Vector<Variable> yes,Vector<Variable> no,List<ConstraintUnifyProblem> cups,Constraint con, boolean multiSet) {
        if (!con.isReducesTo()) {
            cups.clear();
            return false;
        }
        return super.collectUnifyProblemForImplication(yes,no,cups,con, multiSet);
    }

    @Override
    public boolean collectUnifyProblemForEquivalenz(List<ConstraintUnifyProblem> cups,Constraint con) {
        if (!con.isReducesTo()) {
            cups.clear();
            return false;
        }
        return super.collectUnifyProblemForEquivalenz(cups,con);
    }
    **/

    public Count getCount() {
        return this.count;
    }

    @Override
    public String toString() {
        return this.getLeft().toString()
            + " = "
            + this.getRight().toString()
            + (this.parentFunc != null ? " @ " + this.parentFunc : "")
            + " ["
            + this.getId()
            + "+"
            + this.count
            + "]";
    }

    public Object getId() {
        return this.id;
    }

    public PredefinedFunction<? extends Domain> getParentFunc() {
        return this.parentFunc;
    }

    @Override
    public String export(Export_Util o) {
        return this.getLeft().export(o)
            + o.reducesTo()
            + /*this.count+ o.reducesTo()+*/this.getRight().export(o)
            + (this.parentFunc != null ? " @ " + this.parentFunc : "");
    }

    @Override
    public boolean collectMatchMap(Constraint constraint, Map<TRSVariable, TRSTerm> map) {
        if (constraint.isReducesTo()) {
            ReducesTo p = (ReducesTo) constraint;
            this.getLeft().extendMatchingSubstitution(map, p.getLeft());
            this.getRight().extendMatchingSubstitution(map, p.getRight());
            return true;
        }
        return false;
    }

    public TRSVisitable replaceAll(TRSTerm replace, TRSTerm replacement) {
        return ReducesTo.create(
            this.getLeft().replaceAll(replace, replacement),
            this.getRight().replaceAll(replace, replacement),
            null,
            this.count,
            this.id);
    }

    public ReducesTo change(TRSTerm newLeft, TRSTerm newRight, PredefinedFunction<? extends Domain> parentFunc) {
        if (newLeft == null || this.left.equals(newLeft)) {
            newLeft = this.left;
        }
        if (newRight == null || this.right.equals(newRight)) {
            newRight = this.right;
        }
        if (parentFunc == null) {
            parentFunc = this.parentFunc;
        }
        if (this.left == newLeft && this.right == newRight && parentFunc == this.parentFunc) {
            return this;
        } else {
            return new ReducesTo(newLeft, newRight, parentFunc, this.count, this.id);
        }
    }

    @Override
    public TermAtom change(TRSTerm newLeft, TRSTerm newRight) {
        return this.change(newLeft, newRight, null);
    }

    @Override
    public Set<GPolyVar> getPolyVariables() {
        return Collections.<GPolyVar>emptySet();
    }

}
