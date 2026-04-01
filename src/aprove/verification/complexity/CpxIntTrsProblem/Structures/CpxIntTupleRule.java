package aprove.verification.complexity.CpxIntTrsProblem.Structures;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Algorithms.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.IDPExport.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class CpxIntTupleRule
implements
    Immutable,
    Exportable,
    HasRootSymbol,
    HasFunctionSymbols,
    HasVariables,
    HasLHS
{

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.constraints == null) ? 0 : this.constraints.hashCode());
        result = prime * result + ((this.lhs == null) ? 0 : this.lhs.hashCode());
        result = prime * result + ((this.rhs == null) ? 0 : this.rhs.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        CpxIntTupleRule other = (CpxIntTupleRule) obj;
        if (this.constraints == null) {
            if (other.constraints != null) {
                return false;
            }
        } else if (!this.constraints.equals(other.constraints)) {
            return false;
        }
        if (this.lhs == null) {
            if (other.lhs != null) {
                return false;
            }
        } else if (!this.lhs.equals(other.lhs)) {
            return false;
        }
        if (this.rhs == null) {
            if (other.rhs != null) {
                return false;
            }
        } else if (!this.rhs.equals(other.rhs)) {
            return false;
        }
        return true;
    }

    private final TRSFunctionApplication lhs;
    private final TRSFunctionApplication rhs;
    private final ImmutableList<TRSFunctionApplication> rhss;
    private final ImmutableLinkedHashSet<Constraint> constraints;

    // cached values
    private volatile IGeneralizedRule iGeneralizedRuleCache = null;
    private ImmutableLinkedHashMap<CallArgument, LocalSizeBound> localSizeBounds = null;
    private ImmutableArrayList<CallArgument> callArguments;

    private CpxIntTupleRule(
        final TRSFunctionApplication lhs,
        final TRSFunctionApplication rhs,
        final ImmutableLinkedHashSet<Constraint> constraints)
    {
        this.lhs = lhs;
        this.rhs = rhs;
        ArrayList<TRSFunctionApplication> rhss = new ArrayList<>();
        for (TRSTerm r : rhs.getArguments()) {
            rhss.add((TRSFunctionApplication) r);
        }
        this.rhss = ImmutableCreator.create(rhss);
        this.constraints = constraints;
        assert !this.constraints.contains(null);
    }

    public static LinkedHashSet<CpxIntTupleRule> createRules(final IGeneralizedRule rule)
        throws NoValidCpxIntTupleRuleException
    {
        return CpxIntTupleRule.createRules(rule, null);
    }

    public static LinkedHashSet<CpxIntTupleRule> createRules(
        final IGeneralizedRule rule,
        final ImmutableSet<Constraint> additionalConstraints) throws NoValidCpxIntTupleRuleException
    {
        LinkedHashSet<Constraint> constrs = new LinkedHashSet<>();
        if (additionalConstraints != null) {
            constrs.addAll(additionalConstraints);
        }

        FreshNameGenerator fng;
        {
            LinkedHashSet<String> used = new LinkedHashSet<>();
            for (TRSVariable v : rule.getVariables()) {
                used.add(v.getName());
            }
            if (rule.getCondTerm() != null) {
                for (TRSVariable v : rule.getCondVariables()) {
                    used.add(v.getName());
                }
            }
            fng = new FreshNameGenerator(used, FreshNameGenerator.APPEND_NUMBERS);
        }

        if (rule.getRight().isVariable()) {
            throw new NoValidCpxIntTupleRuleException(rule, "RHS is variable");
        }
        TRSFunctionApplication rrhs = (TRSFunctionApplication) rule.getRight();
        if (!CpxIntTermHelper.isComSymbol(rrhs.getRootSymbol())) {
            rrhs = TRSTerm.createFunctionApplication(FunctionSymbol.create(CpxIntTermHelper.ComPrefix + "1", 1), rrhs);
        }
        TRSFunctionApplication rlhs = rule.getLeft();
        if (!rlhs.isLinear()) {
            // linearize
            LinkedHashSet<TRSVariable> seenVariables = new LinkedHashSet<>();
            ArrayList<TRSTerm> newArgs = new ArrayList<>();
            for (TRSTerm arg : rlhs.getArguments()) {
                assert arg.isVariable();
                TRSVariable v = (TRSVariable) arg;
                if (seenVariables.contains(v)) {
                    TRSVariable vPrime = TRSTerm.createVariable(fng.getFreshName(v.getName(), false));
                    newArgs.add(vPrime);
                    try {
                        constrs.add(Constraint.create(TRSTerm.createFunctionApplication(
                            CpxIntTermHelper.fEq,
                            v,
                            vPrime)));
                    } catch (NoConstraintTermException e1) {
                        throw new RuntimeException(e1);
                    }
                } else {
                    seenVariables.add(v);
                    newArgs.add(v);
                }
            }
            rlhs = TRSTerm.createFunctionApplication(rlhs.getRootSymbol(), newArgs);
        }
        for (TRSTerm e : rlhs.getArguments()) {
            if (!e.isVariable()) {
                throw new NoValidCpxIntTupleRuleException(rule, "LHS has non-variable subterm");
            }
        }
        for (TRSTerm t : rrhs.getArguments()) {
            if (t.isVariable()) {
                throw new NoValidCpxIntTupleRuleException(rule, "An argument of a Com_i symbol is a variable");
            }
            TRSFunctionApplication fa = (TRSFunctionApplication) t;
            for (TRSTerm e : fa.getArguments()) {
                if (!CpxIntTermHelper.isIntegerTerm(e)) {
                    // we might allow this for integer arithmetic
                    throw new NoValidCpxIntTupleRuleException(rule, "Proper Subterm of RHS has non-integer subterm");
                }
            }
        }

        Set<LinkedHashSet<Constraint>> dnf;
        if (rule.getCondTerm() == null) {
            // build a True:
            dnf = new LinkedHashSet<>();
            dnf.add(new LinkedHashSet<Constraint>());
        } else if (rule.getCondTerm().isVariable()) {
            throw new NoValidCpxIntTupleRuleException(rule, "Constraint is variable");
        } else {
            try {
                dnf = CpxIntTermHelper.computeDNF((TRSFunctionApplication) rule.getCondTerm());
            } catch (NoConstraintTermException e) {
                throw new NoValidCpxIntTupleRuleException(rule, "Constraint term is not well-formed.");
            }
        }

        LinkedHashSet<CpxIntTupleRule> rv = new LinkedHashSet<>();
        for (LinkedHashSet<Constraint> rconstraints : dnf) {
            assert !rconstraints.contains(null) : "The set of constraints contains null";
            rconstraints.addAll(constrs);
            rv.add(new CpxIntTupleRule(rlhs, rrhs, ImmutableCreator.create(rconstraints)));
        }
        return rv;
    }

    @Override
    public TRSFunctionApplication getLeft() {
        return this.lhs;
    }

    public TRSFunctionApplication getRight() {
        return this.rhs;
    }

    public ImmutableList<TRSFunctionApplication> getRights() {
        return this.rhss;
    }

    public ImmutableSet<Constraint> getConstraints() {
        return this.constraints;
    }

    @Override
    public Set<TRSVariable> getVariables() {
        LinkedHashSet<TRSVariable> vars = new LinkedHashSet<>();
        vars.addAll(this.lhs.getVariables());
        vars.addAll(this.rhs.getVariables());
        for (Constraint i : this.constraints) {
            vars.addAll(i.getVariables());
        }
        return vars;
    }

    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        LinkedHashSet<FunctionSymbol> fs = new LinkedHashSet<>();
        fs.addAll(this.lhs.getFunctionSymbols());
        fs.addAll(this.rhs.getFunctionSymbols());
        for (Constraint i : this.constraints) {
            fs.addAll(i.getFunctionSymbols());
        }
        return fs;
    }

    @Override
    public FunctionSymbol getRootSymbol() {
        return this.lhs.getRootSymbol();
    }

    @Override
    public String export(final Export_Util eu) {
        return this.toIGeneralizedRule().export(eu);
    }

    public TRSTerm getConstraintTerm() {
        if (this.constraints.isEmpty()) {
            return CpxIntTermHelper.TRUE;
        }
        TRSTerm t = null;
        for (Constraint c : this.constraints) {
            if (t == null) {
                t = c.getConstraintTerm();
            } else {
                t = TRSTerm.createFunctionApplication(CpxIntTermHelper.fLand, t, c.getConstraintTerm());
            }
        }
        if (t == null) {
            return CpxIntTermHelper.TRUE;
        }
        return t;
    }

    /**
     * @param rules - non-null
     * @return a corresponding non-null set of IGeneralizedRules, may be modified
     */
    public static Set<IGeneralizedRule> toIGeneralizedRules(Iterable<CpxIntTupleRule> rules) {
        Set<IGeneralizedRule> res = new LinkedHashSet<>();
        for (CpxIntTupleRule rule : rules) {
            res.add(rule.toIGeneralizedRule());
        }
        return res;
    }

    private IGeneralizedRule toIGeneralizedRule() {
        IGeneralizedRule result = this.iGeneralizedRuleCache;
        if (result == null) {
            synchronized (this) {
                result = this.iGeneralizedRuleCache;
                if (result == null) {
                    result =
                        this.iGeneralizedRuleCache =
                            IGeneralizedRule.create(this.lhs, this.rhs, this.getConstraintTerm());
                }
            }
        }
        return result;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public CpxIntTupleRule applySubstitution(final TRSSubstitution subst) throws NoConstraintTermException {
        TRSFunctionApplication lhs = this.lhs.applySubstitution(subst);
        TRSFunctionApplication rhs = this.rhs.applySubstitution(subst);
        LinkedHashSet<Constraint> constraints = new LinkedHashSet<>();
        for (Constraint constraint : this.constraints) {
            constraints.add(constraint.applySubstitution(subst));
        }
        return new CpxIntTupleRule(lhs, rhs, ImmutableCreator.create(constraints));
    }

    public ConstraintInformation getConstraintInformation() {
        Set<TRSVariable> vars = this.getVariables();
        vars.removeAll(this.lhs.getVariables()); // we might not replace variables on the lhs
        return new ConstraintInformation(this.constraints, vars);
    }

    public CpxIntTupleRule replaceRhs(TRSFunctionApplication newRhs) {
        // maybe also filter constraints?
        return new CpxIntTupleRule(this.lhs, newRhs, this.constraints);
    }

    public CpxIntTupleRule renameVars(final Set<TRSVariable> avoid) {
        final FreshNameGenerator fng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        for (final TRSVariable v : avoid) {
            fng.lockName(v.getName());
        }
        final Set<TRSVariable> clashes = this.getVariables();
        for (final TRSVariable v : clashes) {
            fng.lockName(v.getName());
        }
        clashes.retainAll(avoid);
        final LinkedHashMap<TRSVariable, TRSTerm> rawSigma = new LinkedHashMap<>();
        for (final TRSVariable var : clashes) {
            rawSigma.put(var, TRSTerm.createVariable(fng.getFreshName(var.getName(), false)));
        }
        final TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(rawSigma));
        try {
            return this.applySubstitution(sigma);
        } catch (final NoConstraintTermException e) {
            throw new RuntimeException(e);
        }
    }

    public CpxIntTupleRule getWithRenumberedVariables(final String prefix) {
        final Map<TRSVariable, TRSVariable> map = new HashMap<>();
        final ImmutablePair<? extends TRSFunctionApplication, Integer> numberedLAndInt =
            this.getLeft().renumberVariables(map, prefix, TRSTerm.STANDARD_NUMBER);
        final ImmutablePair<? extends TRSTerm, Integer> numberedRAndInt =
            this.getRight().renumberVariables(map, prefix, numberedLAndInt.y);
        @SuppressWarnings("unused")
        final ImmutablePair<? extends TRSTerm, Integer> numberedCAndInt =
            this.getConstraintTerm().renumberVariables(map, prefix, numberedRAndInt.y);

        final TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(map));
        try {
            return this.applySubstitution(sigma);
        } catch (final NoConstraintTermException e) {
            throw new RuntimeException(e);
        }
    }

    public CpxIntTupleRule chainWithRule(final CpxIntTupleRule rule, final int argument) {
        LinkedHashSet<CpxIntTupleRule> chainedRule;
        TRSFunctionApplication lhs = this.getLeft();
        ImmutableList<TRSFunctionApplication> rhss = this.getRights();
        TRSFunctionApplication rhs = rhss.get(argument);
        FunctionSymbol rhsSym = rhs.getRootSymbol();
        int arity = rhsSym.getArity();
        ImmutableList<TRSTerm> rhsTerms = rhs.getArguments();
        TRSTerm phi = this.getConstraintTerm();
        Set<TRSVariable> vars = this.getVariables();
        assert rhsSym.equals(rule.getLeft().getRootSymbol()); // otherwise we have a strange graph...
        CpxIntTupleRule nextRenamed = rule.renameVars(vars);
        ImmutableList<TRSTerm> nextLhs = nextRenamed.getLeft().getArguments();
        Map<TRSVariable, TRSTerm> rawMu = new LinkedHashMap<>();
        for (int i = 0; i < arity; ++i) {
            TRSTerm xTerm = nextLhs.get(i);
            assert xTerm.isVariable();
            TRSVariable x = (TRSVariable) xTerm;
            assert !rawMu.containsKey(x);
            rawMu.put(x, rhsTerms.get(i));
        }
        TRSSubstitution mu = TRSSubstitution.create(ImmutableCreator.create(rawMu));
        TRSTerm psi = nextRenamed.getConstraintTerm();
        ArrayList<TRSTerm> newRhs = new ArrayList<>();
        for (int i = 0; i < argument; ++i) {
            newRhs.add(rhss.get(i));
        }
        newRhs.addAll(nextRenamed.getRight().applySubstitution(mu).getArguments());
        for (int i = argument + 1, l = rhss.size(); i < l; ++i) {
            newRhs.add(rhss.get(i));
        }
        TRSTerm chainedRhs = TRSTerm.createFunctionApplication(CpxIntTermHelper.getComSymbol(newRhs.size()), newRhs);
        TRSTerm psimu = psi.applySubstitution(mu);
        TRSTerm chainedConstraints = TRSTerm.createFunctionApplication(CpxIntTermHelper.fLand, phi, psimu);
        IGeneralizedRule chainedIGRule = IGeneralizedRule.create(lhs, chainedRhs, chainedConstraints);
        try {
            chainedRule = CpxIntTupleRule.createRules(chainedIGRule);
        } catch (NoValidCpxIntTupleRuleException e) {
            throw new RuntimeException(e); // should not be possible, since both rules were already in proper CpxIntTuple form
        }
        assert chainedRule.size() == 1; // since we only "and" constraints together
        return chainedRule.iterator().next();
    }

    public LocalSizeBound getLocalSizeBound(CallArgument pos, Abortion aborter) throws AbortionException {
        assert this.equals(pos.rule);
        ImmutableLinkedHashMap<CallArgument, LocalSizeBound> lsb = this.getLocalSizeBounds(aborter);
        return lsb.get(pos);
    }

    public synchronized ImmutableLinkedHashMap<CallArgument, LocalSizeBound> getLocalSizeBounds(Abortion aborter)
        throws AbortionException
    {
        if (this.localSizeBounds == null) {
            this.computeLocalSizeBounds(aborter);
        }
        assert this.localSizeBounds != null;
        return this.localSizeBounds;
    }

    /**
     * Turns a CpxIntTupleRule with COM symbols on the right into a set of
     * IGeneralizedRules. A rule of the form f(...) -> COM_k(g_1(...), ...,
     * g_k(...)) | c is turned into k rules f(...) -> g_1(...) | c ... f(...) ->
     * g_k(...) | c NOTE: This is NOT valid for complexity analysis.
     * @return a set of rules (without COM_1 on the right) that is
     * termination-equivalent to this rule, but not complexity-equivalent.
     */
    public Set<IGeneralizedRule> getAsSeveralRules() {
        final Set<IGeneralizedRule> res = new LinkedHashSet<>();
        final TRSTerm cond = this.getConstraintTerm();

        for (final TRSFunctionApplication curRhs : this.getRights()) {
            res.add(IGeneralizedRule.create(this.lhs, curRhs, cond));
        }

        return res;
    }

    public synchronized ImmutableArrayList<CallArgument> getCallArguments() {
        if (this.callArguments == null) {
            ArrayList<CallArgument> args = new ArrayList<>();
            for (int i = 0, li = this.rhss.size(); i < li; ++i) {
                TRSFunctionApplication rhs = this.rhss.get(i);
                for (int j = 0, lj = rhs.getArguments().size(); j < lj; ++j) {
                    CallArgument a = new CallArgument(this, i, j);
                    args.add(a);
                }
            }
            this.callArguments = ImmutableCreator.create(args);
        }
        return this.callArguments;
    }

    private void computeLocalSizeBounds(Abortion aborter) throws AbortionException {
        LinkedHashMap<CallArgument, LocalSizeBound> lsbmap = new LinkedHashMap<>();
        LinkedHashMap<Integer, LinkedHashSet<CallArgument>> sd = new LinkedHashMap<>();

        for (int i = 0, li = this.getLeft().getRootSymbol().getArity(); i < li; ++i) {
            sd.put(i, new LinkedHashSet<CallArgument>());
        }

        for (CallArgument alpha : this.getCallArguments()) {
            LocalSizeBound lsb = LocalSizeBoundComputation.computeLocalSizeBounds(alpha, aborter);
            lsbmap.put(alpha, lsb);
        }
        this.localSizeBounds = ImmutableCreator.create(lsbmap);
    }

    public String export(
        Export_Util eu,
        LinkedHashMap<Position, PositionMarker> lhsMarkers,
        LinkedHashMap<Position, PositionMarker> rhsMarkers)
    {
        return this.toIGeneralizedRule().export(eu, lhsMarkers, rhsMarkers, null);
    }

    public ImmutableLinkedHashMap<Integer, ImmutableLinkedHashSet<CallArgument>> getSizeDependencies(Abortion aborter) {
        LinkedHashMap<Integer, LinkedHashSet<CallArgument>> rv = new LinkedHashMap<>();
        for (int i = 0, l = this.getRootSymbol().getArity(); i < l; ++i) {
            rv.put(i, new LinkedHashSet<CallArgument>());
        }
        for (LocalSizeBound lsb : this.getLocalSizeBounds(aborter).values()) {
            assert lsb != null;
            for (int i : lsb.getA()) {
                LinkedHashSet<CallArgument> t = rv.get(i);
                assert t != null;
                t.add(lsb.getAlpha());
            }
        }
        LinkedHashMap<Integer, ImmutableLinkedHashSet<CallArgument>> rv2 = new LinkedHashMap<>();
        for (Map.Entry<Integer, LinkedHashSet<CallArgument>> e : rv.entrySet()) {
            rv2.put(e.getKey(), ImmutableCreator.create(e.getValue()));
        }
        return ImmutableCreator.create(rv2);
    }

    public CpxIntTupleRule getWithRenamedVariables(Map<TRSVariable, TRSVariable> renamingMap) {
        TRSFunctionApplication newLhs = lhs.renameVariables(renamingMap);
        TRSFunctionApplication newRhs = rhs.renameVariables(renamingMap);
        LinkedHashSet<Constraint> newConstraints = new LinkedHashSet<>();
        for (Constraint c: constraints) {
            try {
                newConstraints.add(Constraint.create(c.getConstraintTerm().renameVariables(renamingMap)));
            } catch (NoConstraintTermException e) {
                // since we just rename variables, this should never ever happen...
                e.printStackTrace();
                throw new RuntimeException(e);
            }
        }
        return new CpxIntTupleRule(newLhs, newRhs, ImmutableCreator.create(newConstraints));
    }

}
