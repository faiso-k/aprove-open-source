package aprove.verification.dpframework.DPConstraints.idp;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 *
 * @author mpluecke
 * @version $Id$
 */
public class PolyAtom<C extends GPolyCoeff> extends Constraint.ConstraintSkeleton {

    protected final TermAtom termAtom;

    protected final TRSTerm left;
    protected final TRSTerm right;

    protected final ConstraintType relation;
    protected final GPoly<GPoly<C, GPolyVar>, GPolyVar> lhs;
    protected final GInterpretation<C> polyInterpretation;
    protected final int recommendation;
    protected volatile Boolean isLinear;

    public static <T extends GPolyCoeff> PolyAtom<T> create(
        GPoly<GPoly<T, GPolyVar>, GPolyVar> lhs,
        ConstraintType relation,
        GInterpretation<T> polyInterpretation,
        TermAtom termAtom,
        TRSTerm left,
        TRSTerm right,
        int recommendation)
    {
        return new PolyAtom<T>(lhs, relation, polyInterpretation, termAtom, left, right, recommendation);
    }

    private PolyAtom(
        GPoly<GPoly<C, GPolyVar>, GPolyVar> lhs,
        ConstraintType relation,
        final GInterpretation<C> polyInterpretation,
        final TermAtom termAtom,
        final TRSTerm left,
        final TRSTerm right,
        int recommendation)
    {
        this.lhs = lhs;
        this.polyInterpretation = polyInterpretation;
        this.relation = relation;
        this.termAtom = termAtom;
        this.left = left;
        this.right = right;
        this.recommendation = recommendation;
    }

    @Override
    public boolean collectMatchMap(Constraint constraint, Map<TRSVariable, TRSTerm> map) {
        return this.termAtom != null ? this.termAtom.collectMatchMap(constraint, map) : false;
    }

    @Override
    public TRSVisitable visit(DPConstraintVisitor dpcv) {
        dpcv.fcasePolyAtom(this);
        return dpcv.casePolyAtom(this);
    }

    @Override
    public boolean isAtom() {
        return true;
    }

    @Override
    public boolean isPolyAtom() {
        return true;
    }

    public TermAtom getTermAtom() {
        return this.termAtom;
    }

    public ConstraintType getRelation() {
        return this.relation;
    }

    public GPoly<GPoly<C, GPolyVar>, GPolyVar> getLhs() {
        return this.lhs;
    }

    public TRSVisitable applySubstitution(Substitution subs) {
        return this;
    }

    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        return this.termAtom.getFunctionSymbols();
    }

    @Override
    public Map<TRSVariable, Integer> getVariableCount() {
        return new LinkedHashMap<TRSVariable, Integer>();
    }

    @Override
    public TRSVisitable replaceIdById(Map<Object, Object> map) {
        return this;
    }

    @Override
    public Set<? extends TRSTerm> getTerms() {
        return this.termAtom.getTerms();
    }

    @Override
    public Set<TRSVariable> getVariables() {
        return new LinkedHashSet<TRSVariable>(0);
    }

    public TRSTerm getLeft() {
        return this.left;
    }

    public TRSTerm getRight() {
        return this.right;
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder result = new StringBuilder();
        GPolyWithMinMaxExport<C> export =
            new GPolyWithMinMaxExport<C>(
                this.polyInterpretation.getFvInner(),
                this.polyInterpretation.getFvOuter(),
                this.polyInterpretation.getFactory().getFactory());
        export.applyTo(this.lhs);
        // System.err.println("Export: " + lhs);
        result.append(export.export(o));
        result.append(" ");
        result.append(this.relation.export(o));
        result.append(" ");
        export.applyTo(this.polyInterpretation.getFactory().getFactory().zero());
        result.append(export.export(o));
        return result.toString();
    }

    public OPCAtom<C> asOPCAtom(OrderPolyFactory<C> factory) {
        return new OPCAtom<C>(factory.wrap(this.lhs), null, this.relation);
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public Set<GPolyVar> getPolyVariables() {
        return this.lhs.getVariables();
    }

    public int getRecommendation() {
        return this.recommendation;
    }

    public boolean isLinear() {
        if (this.isLinear == null) {
            synchronized (this) {
                if (this.isLinear == null) {
                    GPoly<GPoly<C, GPolyVar>, GPolyVar> poly = this.getLhs();
                    if (!poly.isFlat(this.polyInterpretation.getOuterRingMonoid())) {
                        this.polyInterpretation.getFvOuter().applyTo(poly);
                    }
                    for (Map.Entry<GMonomial<GPolyVar>, GPoly<C, GPolyVar>> monomial : poly.getMonomials(
                        this.polyInterpretation.getOuterRingMonoid()).entrySet())
                    {
                        Map<GPolyVar, BigInteger> exponents = monomial.getKey().getExponents();
                        if (exponents.isEmpty()) {
                            GPoly<C, GPolyVar> coeff = monomial.getValue();
                            if (!coeff.isFlat(this.polyInterpretation.getInnerRingMonoid())) {
                                this.polyInterpretation.getFvInner().applyTo(coeff);
                            }
                            if (!coeff.isConstant()) {
                                this.isLinear = false;
                                return false;
                            }
                        } else if (monomial.getKey().getExponents().size() == 1) {
                            if (monomial.getKey().getExponents().values().iterator().next().compareTo(BigInteger.ONE) > 0)
                            {
                                this.isLinear = false;
                                return false;
                            }
                            GPoly<C, GPolyVar> coeff = monomial.getValue();
                            if (!coeff.isFlat(this.polyInterpretation.getInnerRingMonoid())) {
                                this.polyInterpretation.getFvInner().applyTo(coeff);
                            }
                            if (!coeff.isConstant()) {
                                this.isLinear = false;
                                return false;
                            }
                        } else if (monomial.getKey().getExponents().size() > 1) {
                            this.isLinear = false;
                            return false;
                        }
                    }
                    this.isLinear = true;
                }
            }
        }
        return this.isLinear;
    }

}
