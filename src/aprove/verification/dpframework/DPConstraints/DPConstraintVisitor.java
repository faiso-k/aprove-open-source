package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.idp.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

public abstract class DPConstraintVisitor {

    public void fcasePolyAtom(PolyAtom<? extends GPolyCoeff> atom) {
    }

    public TRSVisitable casePolyAtom(PolyAtom<? extends GPolyCoeff> atom) {
        return atom;
    }

    public void fcaseUsableAtom(UsableAtom<? extends GPolyCoeff> atom) {
    }

    public TRSVisitable caseUsableAtom(UsableAtom<? extends GPolyCoeff> atom) {
        return atom;
    }

    public void fcaseTermAtom(TermAtom atom) {
    }

    public void fcaseReducesTo(ReducesTo reducesTo) {
    }

    public TRSVisitable caseReducesTo(ReducesTo reducesTo) {
        return reducesTo;
    }

    public void fcasePredicate(Predicate predicate) {
    }

    public TRSVisitable casePredicate(Predicate predicate) {
        return predicate;
    }

    public void fcaseImplication(Implication implication) {
    }

    public boolean guardQuantor(Implication implication) {
        return false;
    }

    public boolean guardConditions(Implication implication) {
        return true;
    }

    public boolean guardConclusion(Implication implication) {
        return true;
    }

    public TRSVisitable caseImplication(Implication implication) {
        return implication;
    }

    public Set<TRSVariable> caseQuantor(Set<TRSVariable> quantor) {
        return quantor;
    }

    public void fcaseConstraintSet(ConstraintSet constraintSet) {
    }

    public TRSVisitable caseConstraintSet(ConstraintSet constraintSet) {
        return constraintSet;
    }

    public <C extends TRSVisitable> C applyTo(C c) {
        return (C) c.visit(this);
    }
}
