package aprove.verification.complexity.CpxRntsProblem.Structures;

import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.CpxRntsProblem.Exceptions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;


/**
 * A RNTS rule, consisting of:
 *  - a left-hand side f(v1,..,vn) with different variables v1,..,vn
 *  - a right-hand side (an arbitrary term)
 *  - a polynomial weight (or cost)
 *  - a set of constraints (the guard)
 *
 * @author mnaaf
 *
 */
public class RntsRule
implements
    Immutable,
    Exportable,
    HasRootSymbol,
    HasFunctionSymbols,
    HasVariables,
    HasLHS,
    HasRuleForm
{
    private final TRSFunctionApplication lhs;
    private final TRSTerm rhs;
    private final SimplePolynomial cost;
    private final ImmutableSet<Constraint> constraints;

    private RntsRule(final TRSFunctionApplication l, final TRSTerm r, final SimplePolynomial k, final ImmutableSet<Constraint> c) {
        this.lhs = l;
        this.rhs = r;
        this.cost = k;
        this.constraints = c;
        assert !this.constraints.contains(null);
    }

    public static RntsRule create(
            final TRSFunctionApplication lhs,
            final TRSTerm rhs,
            final ImmutableSet<Constraint> constraints
            ) throws InvalidRntsRuleException
    {
        return create(lhs,rhs,SimplePolynomial.ONE,constraints);
    }

    public static RntsRule createUnsafe(
            final TRSFunctionApplication lhs,
            final TRSTerm rhs,
            final SimplePolynomial cost,
            final ImmutableSet<Constraint> constraints)
    {
        try {
            return create(lhs,rhs,cost,constraints);
        } catch (InvalidRntsRuleException e) {
            throw new RuntimeException(e);
        }
    }

    public static RntsRule create(
            final TRSFunctionApplication lhs,
            final TRSTerm rhs,
            final SimplePolynomial cost,
            final ImmutableSet<Constraint> constraints
            ) throws InvalidRntsRuleException
    {
        for (TRSTerm t : lhs.getArguments()) {
            if (!t.isVariable()) {
                throw new InvalidRntsRuleException(lhs,rhs,constraints,"LHS has non-variable subterm");
            }
        }
        if (!lhs.isLinear()) {
            throw new InvalidRntsRuleException(lhs,rhs,constraints,"LHS is nonlinear");
        }
        for (Constraint c : constraints) {
            if (c.getConstraintTerm().isVariable() || c.getConstraintTerm().getRootSymbol().getArity() != 2) {
                throw new InvalidRntsRuleException(lhs,rhs,constraints,"Constraint has variable or non-binary operator");
            }
            try {
                c.getPolynomialRepresentation();
            } catch (NotRepresentableAsPolynomialException e) {
                throw new InvalidRntsRuleException(lhs,rhs,constraints,"Constraint has no polynomial representation");
            }
        }
        return new RntsRule(lhs,rhs,cost,constraints);
    }

    /**
     * applies the given substitution to lhs,rhs,cost,constraints.
     * @note the image of subs must only contain integer terms, e.g. x / f(y) is not allowed
     * @return new resulting rule
     * @throws NotRepresentableAsPolynomialException if the resulting cost is no longer a polynomial
     */
    public RntsRule applyIntegerSubstitution(TRSSubstitution subs) throws NotRepresentableAsPolynomialException {
        //new lhs must only contain variables
        for (TRSVariable var : this.lhs.getVariables()) {
            assert subs.substitute(var).isVariable();
        }
        //variables may only be substituted by integer terms
        for (TRSVariable var : this.getVariables()) {
            assert CpxIntTermHelper.isIntegerTerm(subs.substitute(var));
        }
        TRSFunctionApplication lhs = this.lhs.applySubstitution(subs);
        TRSTerm rhs = this.rhs.applySubstitution(subs);
        TRSTerm costTerm = this.cost.toTerm().applySubstitution(subs);
        SimplePolynomial cost = CpxIntTermHelper.toSimplePolynomial(costTerm);
        Set<Constraint> guard = new LinkedHashSet<>();
        for (Constraint c : this.constraints) {
            try {
                guard.add(Constraint.create(c.getConstraintTerm().applySubstitution(subs)));
            } catch (NoConstraintTermException e) {
                throw new RuntimeException(e); //internal error
            }
        }
        return createUnsafe(lhs,rhs,cost,ImmutableCreator.create(guard));
    }

    @Override
    public TRSFunctionApplication getLeft() {
        return lhs;
    }

    @Override
    public TRSTerm getRight() {
        return rhs;
    }

    public SimplePolynomial getCost() {
        return cost;
    }

    public ImmutableSet<Constraint> getConstraints() {
        return constraints;
    }

    @Override
    public Set<TRSVariable> getVariables() {
        Set<TRSVariable> res = new HashSet<TRSVariable>();
        res.addAll(lhs.getVariables());
        res.addAll(rhs.getVariables());
        for (Constraint c : constraints) {
            res.addAll(c.getVariables());
        }
        for (String var : cost.getVariables()) {
            res.add(TRSTerm.createVariable(var));
        }
        return res;
    }

    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        Set<FunctionSymbol> res = new HashSet<FunctionSymbol>();
        res.addAll(lhs.getFunctionSymbols());
        res.addAll(rhs.getFunctionSymbols());
        return res;
    }

    @Override
    public FunctionSymbol getRootSymbol() {
        return lhs.getRootSymbol();
    }

    //renames all clashing free variables (rhs,guard). Regular arguments are not modified
    public RntsRule renameFreeVariables(Set<TRSVariable> avoidVars) {
        Set<TRSVariable> usedVars = new LinkedHashSet<>();
        usedVars.addAll(this.getVariables());
        usedVars.addAll(avoidVars);
        FreshVarGenerator fvg = new FreshVarGenerator(usedVars);

        Set<TRSVariable> freeVars = new LinkedHashSet<>();
        freeVars.addAll(this.getVariables());
        freeVars.removeAll(this.lhs.getVariables()); //lhs vars are not free
        freeVars.retainAll(avoidVars); //other free vars can be kept

        Map<TRSVariable,TRSTerm> submap = new LinkedHashMap<>();
        for (TRSVariable var : freeVars) {
            submap.put(var, fvg.getFreshVariable(var, true));
        }
        TRSSubstitution subs = TRSSubstitution.create(ImmutableCreator.create(submap));
        try {
            return this.applyIntegerSubstitution(subs);
        } catch (NotRepresentableAsPolynomialException e) {
            throw new RuntimeException(e); //internal error, only variable renaming
        }
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder s = new StringBuilder();
        s.append(IDPExport.exportTerm(this.lhs, eu, IDPPredefinedMap.DEFAULT_MAP));
        s.append(eu.escape(" -{ "));
        s.append(eu.export(this.cost));
        s.append(eu.escape(" }") + eu.rightarrow() + eu.escape(" "));
        s.append(IDPExport.exportTerm(this.rhs, eu, IDPPredefinedMap.DEFAULT_MAP));
        s.append(eu.escape(" :|: "));
        Iterator<Constraint> iter = this.constraints.iterator();
        while (iter.hasNext()) {
            s.append(IDPExport.exportTerm(iter.next().getConstraintTerm(), eu, IDPPredefinedMap.DEFAULT_MAP));
            if (iter.hasNext()) s.append(eu.escape(", "));
        }
        return s.toString();
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((constraints == null) ? 0 : constraints.hashCode());
        result = prime * result + ((cost == null) ? 0 : cost.hashCode());
        result = prime * result + ((lhs == null) ? 0 : lhs.hashCode());
        result = prime * result + ((rhs == null) ? 0 : rhs.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        RntsRule other = (RntsRule) obj;
        if (constraints == null) {
            if (other.constraints != null)
                return false;
        } else if (!constraints.equals(other.constraints))
            return false;
        if (cost == null) {
            if (other.cost != null)
                return false;
        } else if (!cost.equals(other.cost))
            return false;
        if (lhs == null) {
            if (other.lhs != null)
                return false;
        } else if (!lhs.equals(other.lhs))
            return false;
        if (rhs == null) {
            if (other.rhs != null)
                return false;
        } else if (!rhs.equals(other.rhs))
            return false;
        return true;
    }
}
