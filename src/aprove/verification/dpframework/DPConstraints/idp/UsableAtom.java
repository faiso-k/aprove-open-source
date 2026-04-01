/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.DPConstraints.idp;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

public class UsableAtom<C extends GPolyCoeff> extends Constraint.ConstraintSkeleton {

    protected final TRSTerm t;
    protected final ConstraintType relation;
    protected final RelDependency orientation;
    protected final GInterpretation<C> polyInterpretation;

    public static <T extends GPolyCoeff> UsableAtom<T> create(
        final TRSTerm t,
        final ConstraintType relation,
        final RelDependency orientation,
        GInterpretation<T> polyInterpretation)
    {
        return new UsableAtom<T>(t, relation, orientation, polyInterpretation);
    }

    private UsableAtom(
        final TRSTerm t,
        final ConstraintType relation,
        final RelDependency orientation,
        GInterpretation<C> polyInterpretation)
    {
        this.polyInterpretation = polyInterpretation;
        this.relation = relation;
        this.t = t;
        this.orientation = orientation;
    }

    @Override
    public boolean collectMatchMap(Constraint constraint, Map<TRSVariable, TRSTerm> map) {
        return false;
    }

    @Override
    public TRSVisitable visit(DPConstraintVisitor dpcv) {
        dpcv.fcaseUsableAtom(this);
        return dpcv.caseUsableAtom(this);
    }

    @Override
    public boolean isAtom() {
        return true;
    }

    @Override
    public boolean isUsableAtom() {
        return true;
    }

    public ConstraintType getRelation() {
        return this.relation;
    }

    @Override
    public TRSVisitable applySubstitution(TRSSubstitution subs, boolean idpMode) {
        return this;
    }

    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        return this.t.getFunctionSymbols();
    }

    @Override
    public Map<TRSVariable, Integer> getVariableCount() {
        return this.t.getVariableCount();
    }

    @Override
    public TRSVisitable replaceIdById(Map<Object, Object> map) {
        return this;
    }

    @Override
    public Set<? extends TRSTerm> getTerms() {
        return Collections.singleton(this.t);
    }

    @Override
    public Set<TRSVariable> getVariables() {
        return this.t.getVariables();
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder result = new StringBuilder();
        // System.err.println("Export: " + lhs);
        result.append("(U");
        result.append(o.sup(this.orientation.toString()));
        result.append("(");
        result.append(this.t.export(o));
        result.append("), ");
        result.append(this.relation.export(o));
        result.append(")");
        return result.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public TRSTerm getT() {
        return this.t;
    }

    public RelDependency getOrientation() {
        return this.orientation;
    }

    @Override
    public Set<GPolyVar> getPolyVariables() {
        return Collections.<GPolyVar>emptySet();
    }

    @Override
    public int hashCode() {
        return this.t.hashCode() + 11 * this.orientation.hashCode();
    }

    @Override
    public boolean equals(Object other) {
        if (other == this) {
            return true;
        }
        if (other instanceof UsableAtom) {
            UsableAtom<?> uo = (UsableAtom<?>) other;
            return (this.t.equals(uo.t)) && (this.orientation.equals(uo.orientation)) && (this.relation.equals(uo.relation));
        } else {
            return false;
        }
    }
}
