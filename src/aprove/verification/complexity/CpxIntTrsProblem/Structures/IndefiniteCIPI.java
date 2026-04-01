package aprove.verification.complexity.CpxIntTrsProblem.Structures;

import java.math.*;
import java.util.*;
import java.util.Map.*;

import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Algorithms.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Processors.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class IndefiniteCIPI implements Immutable {

    private static class VarGenerator {
        private final FreshNameGenerator fng;

        private final Set<String> existentials = new LinkedHashSet<>();

        public VarGenerator(final FreshNameGenerator fng) {
            this.fng = fng;
        }

        TRSVariable getExistential(final String name) {
            String freshName = this.fng.getFreshName(name, false);
            this.existentials.add(freshName);
            return TRSTerm.createVariable(freshName);
        }

        TRSVariable getUniversal(final String name) {
            String freshName = this.fng.getFreshName(name, false);
            return TRSTerm.createVariable(freshName);
        }
    }

    // If it wasn't such a pain to define algebraic data types in java, I wouldn't use Term here
    private final ImmutableMap<FunctionSymbol, Pair<ImmutableList<TRSVariable>, TRSTerm>> interpretation;
    private final ImmutableSet<String> existentialVars;

    public static enum ShapeTemplates {
        ShapeConstant {
            @Override
            protected Pair<ImmutableList<TRSVariable>, TRSTerm> build(
                Set<Integer> allowedPositions,
                ImmutableList<TRSVariable> argVars,
                VarGenerator vg)
            {
                return new Pair<>(argVars, vg.getExistential("c"));
            }

        },
        ShapeLinear {
            @Override
            protected Pair<ImmutableList<TRSVariable>, TRSTerm> build(
                Set<Integer> allowedPositions,
                ImmutableList<TRSVariable> argVars,
                VarGenerator vg)
            {
                TRSTerm pol = vg.getExistential("c");
                for (int i : allowedPositions) {
                    TRSVariable coeff = vg.getExistential("c");
                    pol = CpxIntTermHelper.addTerms(pol, CpxIntTermHelper.mulTerms(argVars.get(i), coeff));
                }
                return new Pair<>(argVars, pol);
            }

        },
        ShapeQuadraticNotMixed {
            @Override
            protected Pair<ImmutableList<TRSVariable>, TRSTerm> build(
                Set<Integer> allowedPositions,
                ImmutableList<TRSVariable> argVars,
                VarGenerator vg)
            {
                TRSTerm pol = vg.getExistential("c");
                for (int i : allowedPositions) {
                    TRSVariable var = argVars.get(i);
                    TRSVariable coeff1 = vg.getExistential("c");
                    TRSVariable coeff2 = vg.getExistential("c");
                    pol = CpxIntTermHelper.addTerms(pol, CpxIntTermHelper.mulTerms(var, coeff1));
                    pol = CpxIntTermHelper.addTerms(pol, CpxIntTermHelper.mulTerms(CpxIntTermHelper.mulTerms(var, var), coeff2));
                }
                return new Pair<>(argVars, pol);
            }
        },
        ShapeQuadraticMixed {
            @Override
            protected Pair<ImmutableList<TRSVariable>, TRSTerm> build(
                Set<Integer> allowedPositions,
                ImmutableList<TRSVariable> argVars,
                VarGenerator vg)
            {
                TRSTerm pol = vg.getExistential("c");
                for (int i : allowedPositions) {
                    TRSVariable var = argVars.get(i);
                    TRSVariable coeff = vg.getExistential("c");
                    pol = CpxIntTermHelper.addTerms(pol, CpxIntTermHelper.mulTerms(var, coeff));
                }
                for (int i : allowedPositions) {
                    TRSVariable var1 = argVars.get(i);
                    for (int j : allowedPositions) {
                        TRSVariable var2 = argVars.get(j);
                        TRSVariable coeff = vg.getExistential("c");
                        pol = CpxIntTermHelper.addTerms(pol, CpxIntTermHelper.mulTerms(CpxIntTermHelper.mulTerms(var1, var2), coeff));
                    }
                }
                return new Pair<>(argVars, pol);
            }
        },
        ShapeCubicNotMixed {
            @Override
            protected Pair<ImmutableList<TRSVariable>, TRSTerm> build(
                Set<Integer> allowedPositions,
                ImmutableList<TRSVariable> argVars,
                VarGenerator vg)
            {
                TRSTerm pol = vg.getExistential("c");
                for (int i : allowedPositions) {
                    TRSVariable var = argVars.get(i);
                    TRSVariable coeff1 = vg.getExistential("c");
                    TRSVariable coeff2 = vg.getExistential("c");
                    TRSVariable coeff3 = vg.getExistential("c");
                    pol = CpxIntTermHelper.addTerms(pol, CpxIntTermHelper.mulTerms(var, coeff1));
                    pol = CpxIntTermHelper.addTerms(pol, CpxIntTermHelper.mulTerms(CpxIntTermHelper.mulTerms(var, var), coeff2));
                    pol = CpxIntTermHelper.addTerms(pol, CpxIntTermHelper.mulTerms(CpxIntTermHelper.mulTerms(CpxIntTermHelper.mulTerms(var, var), var), coeff3));
                }
                return new Pair<>(argVars, pol);
            }
        },
        ShapeCubicMixedQuadratic {
            @Override
            protected Pair<ImmutableList<TRSVariable>, TRSTerm> build(
                Set<Integer> allowedPositions,
                ImmutableList<TRSVariable> argVars,
                VarGenerator vg)
            {
                TRSTerm pol = vg.getExistential("c");
                for (int i : allowedPositions) {
                    TRSVariable var = argVars.get(i);
                    TRSVariable coeff1 = vg.getExistential("c");
                    TRSVariable coeff2 = vg.getExistential("c");
                    pol = CpxIntTermHelper.addTerms(pol, CpxIntTermHelper.mulTerms(var, coeff1));
                    pol = CpxIntTermHelper.addTerms(pol, CpxIntTermHelper.mulTerms(CpxIntTermHelper.mulTerms(CpxIntTermHelper.mulTerms(var, var), var), coeff2));
                }
                for (int i : allowedPositions) {
                    TRSVariable var1 = argVars.get(i);
                    for (int j : allowedPositions) {
                        TRSVariable var2 = argVars.get(j);
                        TRSVariable coeff = vg.getExistential("c");
                        pol = CpxIntTermHelper.addTerms(pol, CpxIntTermHelper.mulTerms(CpxIntTermHelper.mulTerms(var1, var2), coeff));
                    }
                }
                return new Pair<>(argVars, pol);
            }
        },
        ShapeCubicMixed {
            @Override
            protected Pair<ImmutableList<TRSVariable>, TRSTerm> build(
                Set<Integer> allowedPositions,
                ImmutableList<TRSVariable> argVars,
                VarGenerator vg)
            {
                TRSTerm pol = vg.getExistential("c");
                for (int i : allowedPositions) {
                    TRSVariable var = argVars.get(i);
                    TRSVariable coeff1 = vg.getExistential("c");
                    pol = CpxIntTermHelper.addTerms(pol, CpxIntTermHelper.mulTerms(var, coeff1));
                }
                for (int i : allowedPositions) {
                    TRSVariable var1 = argVars.get(i);
                    for (int j : allowedPositions) {
                        TRSVariable var2 = argVars.get(j);
                        TRSVariable coeff = vg.getExistential("c");
                        pol = CpxIntTermHelper.addTerms(pol, CpxIntTermHelper.mulTerms(CpxIntTermHelper.mulTerms(var1, var2), coeff));
                    }
                }
                for (int i : allowedPositions) {
                    TRSVariable var1 = argVars.get(i);
                    for (int j : allowedPositions) {
                        TRSVariable var2 = argVars.get(j);
                        for (int k : allowedPositions) {
                            TRSVariable var3 = argVars.get(k);
                            TRSVariable coeff = vg.getExistential("c");
                            pol = CpxIntTermHelper.addTerms(pol, CpxIntTermHelper.mulTerms(CpxIntTermHelper.mulTerms(CpxIntTermHelper.mulTerms(var1, var2), var3), coeff));
                        }
                    }
                }
                return new Pair<>(argVars, pol);
            }

        };
        protected abstract Pair<ImmutableList<TRSVariable>, TRSTerm> build(
            Set<Integer> allowedPositions,
            ImmutableList<TRSVariable> argVars,
            VarGenerator vg);
    }

    private IndefiniteCIPI(
        final Set<FunctionSymbol> definedSymbols,
        Map<FunctionSymbol, Set<Integer>> filteredPositions,
        final FreshNameGenerator fng,
        final FormulaFactory<SMTLIBTheoryAtom> factory,
        final CpxIntTrsRedPairProcessor.Arguments args)
    {
        LinkedHashMap<FunctionSymbol, Pair<ImmutableList<TRSVariable>, TRSTerm>> rawInter = new LinkedHashMap<>();
        VarGenerator vg = new VarGenerator(fng);

        for (FunctionSymbol sym : definedSymbols) {
            Set<Integer> filtered =
                filteredPositions.containsKey(sym) ? filteredPositions.get(sym) : new LinkedHashSet<Integer>();
            Set<Integer> allowedPositions = new LinkedHashSet<>();
            List<TRSVariable> argVars = new ArrayList<>();
            for (int i = 0, l = sym.getArity(); i < l; ++i) {
                TRSVariable var = vg.getUniversal("x");
                argVars.add(var);
                if (!filtered.contains(i)) {
                    allowedPositions.add(i);
                }
            }
            rawInter.put(sym, args.shape.build(allowedPositions, ImmutableCreator.create(argVars), vg));
        }

        this.interpretation = ImmutableCreator.create(rawInter);
        this.existentialVars = ImmutableCreator.create(vg.existentials);
    }

    private TRSTerm interpretTerm(final TRSTerm t) {
        if (t.isVariable()) {
            return t;
        }
        TRSFunctionApplication fa = (TRSFunctionApplication) t;
        FunctionSymbol fs = fa.getRootSymbol();
        if (CpxIntTermHelper.polySyms.contains(fs)) {
            ArrayList<TRSTerm> args = new ArrayList<>();
            for (TRSTerm e : fa.getArguments()) {
                args.add(this.interpretTerm(e));
            }
            return TRSTerm.createFunctionApplication(fs, args);
        }
        BigInteger val = CpxIntTermHelper.getIntegerValue(fa);
        if (val != null) {
            return fa;
        }
        Pair<ImmutableList<TRSVariable>, TRSTerm> ap = this.interpretation.get(fs);
        if (ap == null) {
            throw new RuntimeException("There is no interpretation for symbol "
                + fs
                + " in this "
                + IndefiniteCIPI.class.getName());
        }
        ImmutableList<TRSVariable> argVars = ap.x;
        assert argVars.size() == fs.getArity();
        TRSTerm interTerm = ap.y;
        Map<TRSVariable, TRSTerm> rawSubst = new LinkedHashMap<>();
        for (int i = 0; i < fs.getArity(); ++i) {
            rawSubst.put(argVars.get(i), this.interpretTerm(fa.getArgument(i)));
        }
        TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(rawSubst));
        return interTerm.applySubstitution(sigma);
    }

    /**
     * This is a brute force implementation of the max(0,I(t_1)) + ... +
     * max(0,I(t_n)) interpretation of RHSs.
     * @param rhss
     * @return
     */
    private ArrayList<TRSTerm> buildRHSPolynomials(final List<TRSTerm> rhss) {
        ArrayList<TRSTerm> result = new ArrayList<>();
        int size = rhss.size();
        if (size == 0) {
            return result;
        }
        // For Com_1 we don't need max...?!?
        if (size == 1) {
            result.add(rhss.get(0));
            return result;
        }
        // 20 is already too big
        if (rhss.size() > 20) {
            throw new RuntimeException("right hand side has to many calls");
        }
        int s = rhss.size();
        for (int i = 0, m = 1 << s; i < m; ++i) {
            TRSTerm t = null;
            for (int j = 0; j < m; ++j) {
                TRSTerm maxOh;
                if ((i & 1 << j) == 0) {
                    maxOh = CpxIntTermHelper.ZERO;
                } else {
                    maxOh = rhss.get(j);
                }
                if (t == null) {
                    t = maxOh;
                } else {
                    t = CpxIntTermHelper.addTerms(t, maxOh);
                }
            }
            result.add(t);
        }
        return result;
    }

    private static RationalPolynomial termToPolynomial(final TRSTerm t) {
        if (t.isVariable()) {
            TRSVariable v = (TRSVariable) t;
            return RationalPolynomial.createMonomial(1, v.getName());
        }

        TRSFunctionApplication fa = (TRSFunctionApplication) t;
        FunctionSymbol fs = fa.getRootSymbol();
        BigInteger intValue = CpxIntTermHelper.getIntegerValue(fa);

        if (intValue != null) {
            return RationalPolynomial.createFromBigRational(new BigRational(intValue));
        } else if (CpxIntTermHelper.fAdd.equals(fs)) {
            return IndefiniteCIPI.termToPolynomial(fa.getArgument(0)).add(IndefiniteCIPI.termToPolynomial(fa.getArgument(1)));
        } else if (CpxIntTermHelper.fMul.equals(fs)) {
            return IndefiniteCIPI.termToPolynomial(fa.getArgument(0)).multiply(IndefiniteCIPI.termToPolynomial(fa.getArgument(1)));
        } else if (CpxIntTermHelper.fSub.equals(fs)) {
            return IndefiniteCIPI.termToPolynomial(fa.getArgument(0)).subtract(IndefiniteCIPI.termToPolynomial(fa.getArgument(1)));
        } else if (CpxIntTermHelper.fUnaryMinus.equals(fs)) {
            return IndefiniteCIPI.termToPolynomial(fa.getArgument(0)).negate();
        }

        throw new RuntimeException("Invalid function symbol: " + fs.toString());
    }

    private RatPolImplication buildTupleFormula(
        final CpxIntTupleRule tuple,
        final boolean strict,
        final FreshNameGenerator fng)
    {
        ConstraintInformation info = tuple.getConstraintInformation();

        TRSTerm left = this.interpretTerm(tuple.getLeft());
        ArrayList<TRSTerm> rights = new ArrayList<>();
        for (TRSFunctionApplication t : tuple.getRights()) {
            rights.add(this.interpretTerm(t));
        }
        rights = this.buildRHSPolynomials(rights);

        // apply equalities to remove unconstrained variables
        for (Entry<TRSVariable, TRSTerm> eq : info.getEqualities().entrySet()) {
            TRSSubstitution sigma = TRSSubstitution.create(eq.getKey(), eq.getValue());
            left = left.applySubstitution(sigma);
            for (int i = 0, a = rights.size(); i < a; ++i) {
                rights.set(i, rights.get(i).applySubstitution(sigma));
            }
        }

        RationalPolynomial leftPol = IndefiniteCIPI.termToPolynomial(left);
        Set<RationalPolynomial> rightPols = new LinkedHashSet<>();
        for (TRSTerm t : rights) {
            rightPols.add(IndefiniteCIPI.termToPolynomial(t));
        }
        // in the strict case, require boundedness (i.e., lhs > 0)
        if (strict) {
            rightPols.add(RationalPolynomial.ZERO);
        }

        // get constraints on the remaining variables (odd invariant of ConstraintInformation)
        Set<RationalPolynomial> premises = new LinkedHashSet<>();
        for (TRSTerm ineq : info.getInequalities()) {
            premises.add(IndefiniteCIPI.termToPolynomial(ineq));
        }

        Set<RationalPolynomial> consequences = new LinkedHashSet<>();

        for (RationalPolynomial rightPol : rightPols) {
            RationalPolynomial geqZero = leftPol.subtract(rightPol);
            if (strict) {
                // this also implies that lhs > 1
                geqZero = geqZero.subtract(RationalPolynomial.ONE);
            }
            consequences.add(geqZero);
        }

        return new RatPolImplication(
            this.existentialVars,
            ImmutableCreator.create(premises),
            ImmutableCreator.create(consequences));
    }

    private CIPI concretize(final Map<String, Object> resultMap) {
        Map<String, RationalPolynomial> replacements = new LinkedHashMap<>();
        for (String var : this.existentialVars) {
            RationalPolynomial rat = RationalPolynomial.ZERO;
            if (resultMap.containsKey(var)) {
                rat = RationalPolynomial.createFromBigRational((BigRational) resultMap.get(var));
            }
            replacements.put(var, rat);
        }

        Map<FunctionSymbol, Pair<ImmutableList<TRSVariable>, RationalPolynomial>> inter = new LinkedHashMap<>();
        for (Entry<FunctionSymbol, Pair<ImmutableList<TRSVariable>, TRSTerm>> entry : this.interpretation.entrySet()) {
            RationalPolynomial pol = IndefiniteCIPI.termToPolynomial(entry.getValue().y);
            pol = pol.instantiate(replacements);
            inter.put(entry.getKey(), new Pair<>(entry.getValue().x, pol));
        }

        return new CIPI(ImmutableCreator.create(inter));
    }

    /**
     * This should be part of the SMTEngine interface...
     * @param s
     * @return
     */
    private static Object parseSMTResult(final String s) {
        if (s.matches("^-?[0-9]*(\\.[0-9]+)?$")) {
            BigDecimal n = new BigDecimal(s);
            return BigRational.valueOf(n);
        }
        if (s.matches("^-?[0-9]*/[0-9]*$")) {
            String[] nd = s.split("/");
            BigInteger n = new BigInteger(nd[0]);
            BigInteger d = new BigInteger(nd[1]);
            return new BigRational(n, d);
        }
        if (s.matches("^(true|false)$")) {
            return Boolean.valueOf(s);
        }
        throw new RuntimeException("Could not parse \"" + s + "\" as BigRational");
    }

    public static Triple<CIPI,ImmutableSet<CpxIntTupleRule>,ImmutableSet<CpxIntTupleRule>> findCIPI(
        final CpxIntTrsProblem obl,
        Map<CallArgument, ComplexityValue> bounds,
        final FormulaFactory<SMTLIBTheoryAtom> factory,
        final CpxIntTrsRedPairProcessor.Arguments args,
        final Abortion aborter) throws AbortionException, SplitHeuristicNotApplicableException
    {
        List<Formula<SMTLIBTheoryAtom>> list = new ArrayList<>();

        FreshNameGenerator fng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        fng.lockNames(obl.getUsedVarNames());

        Set<CpxIntTupleRule> weakTuples = new LinkedHashSet<>();
        if (args.useSizeBounds) {
            weakTuples.addAll(IndefiniteCIPI.computeRPrime(obl, bounds, args, aborter));
        } else {
            weakTuples.addAll(obl.getK().keySet());
        }

        Map<FunctionSymbol, Set<Integer>> disallowedPositions;
        if (args.useSizeBounds) {
            disallowedPositions = IndefiniteCIPI.computeDisallowedPositions(obl, bounds, weakTuples);
        } else {
            disallowedPositions = new LinkedHashMap<>();
        }

        IndefiniteCIPI icipi = new IndefiniteCIPI(obl.getDefinedSymbols(), disallowedPositions, fng, factory, args);

        ArrayList<Formula<SMTLIBTheoryAtom>> weak = new ArrayList<>();
        for (CpxIntTupleRule tuple : weakTuples) {
            aborter.checkAbortion();
            RatPolImplication impli = icipi.buildTupleFormula(tuple, false, fng);
            if (!impli.isLinear()) {
                impli = SplitHeuristic.split(impli);
            }
            assert impli.isLinear();
            weak.add(PodelskiRybalchenko.solve(impli, fng, factory));
        }
        list.add(factory.buildAnd(weak));

        Map<String, CpxIntTupleRule> strictTupleNames = new LinkedHashMap<>();
        ArrayList<Formula<SMTLIBTheoryAtom>> strictMarkers = new ArrayList<>();
        ArrayList<Formula<SMTLIBTheoryAtom>> atLeastOneStrict = new ArrayList<>();
        for (CpxIntTupleRule tuple : obl.getUnknownTuples()) {
            aborter.checkAbortion();
            String varName = fng.getFreshName("strictTuple", false);
            TheoryAtom<SMTLIBTheoryAtom> var = factory.buildTheoryAtom(SMTLIBBoolVariable.create(varName));
            atLeastOneStrict.add(var);
            strictTupleNames.put(varName, tuple);
            RatPolImplication impli = icipi.buildTupleFormula(tuple, true, fng);
            if (!impli.isLinear()) {
                impli = SplitHeuristic.split(impli);
            }
            assert impli.isLinear();
            strictMarkers.add(factory.buildIff(var, PodelskiRybalchenko.solve(impli, fng, factory)));
        }
        list.add(factory.buildAnd(strictMarkers));
        if (args.allStrict) {
            list.add(factory.buildAnd(atLeastOneStrict));
        } else {
            list.add(factory.buildOr(atLeastOneStrict));
        }

        Pair<YNM, Map<String, String>> result = null;
        // maybe use QF_RA, since we might get nonlinear constraints?
        try {
            result = CpxIntTrsRedPairProcessor.SMT_ENGINE.solve(list, SMTLogic.QF_LRA, aborter);
        } catch (WrongLogicException e) {
            throw new RuntimeException(e);
        }
        if (!YNM.YES.equals(result.x)) {
            return null;
        }
        Map<String, Object> resultMap = new LinkedHashMap<>();
        for (Entry<String, String> entry : result.y.entrySet()) {
            resultMap.put(entry.getKey(), IndefiniteCIPI.parseSMTResult(entry.getValue()));
        }

        Set<CpxIntTupleRule> strictTuples = new LinkedHashSet<>();
        for (Entry<String, CpxIntTupleRule> entry : strictTupleNames.entrySet()) {
            String name = entry.getKey();
            Object res = resultMap.get(name);
            assert res instanceof Boolean;
            if (((Boolean) res).booleanValue()) {
                strictTuples.add(entry.getValue());
            }
        }

        CIPI cipi = icipi.concretize(resultMap);

        weakTuples.removeAll(strictTuples);

        return new Triple<>(cipi, ImmutableCreator.create(strictTuples), ImmutableCreator.create(weakTuples));
    }

    private static Collection<CpxIntTupleRule> computeRPrime(CpxIntTrsProblem obl, Map<CallArgument, ComplexityValue> bounds, CpxIntTrsRedPairProcessor.Arguments args, Abortion aborter) {
        LinkedHashSet<CpxIntTupleRule> r_prime = obl.getUnknownTuples();
        CpxIntGraph g = obl.getDepGraph(aborter);
        if (true) {
            Deque<CpxIntTupleRule> todo = new ArrayDeque<>();
            todo.addAll(r_prime);
            while (!todo.isEmpty()) {
                for (Pair<CpxIntTupleRule, Integer> e : g.getIn(todo.pop())) {
                    if (r_prime.contains(e.getKey())) {
                        continue;
                    }
                    boolean add = false;
                    CpxIntTupleRule rho = e.x;
                    Integer i = e.y;
                    FunctionSymbol fs = rho.getRights().get(i).getRootSymbol();
                    for (int j = 0, l = fs.getArity(); j < l; ++j) {
                        CallArgument alpha = new CallArgument(rho, i, j);
                        ComplexityValue b = bounds.get(alpha);
                        if (b.isConstant() || b instanceof FixedDegreePoly) {
                            continue;
                        }
                        r_prime.add(rho);
                        todo.push(rho);
                        break;
                    }
                }
            }
        }
        return r_prime;
    }

    private static Map<FunctionSymbol, Set<Integer>> computeDisallowedPositions(
        CpxIntTrsProblem obl,
        Map<CallArgument, ComplexityValue> bounds, Set<CpxIntTupleRule> r_prime)
    {
        Map<FunctionSymbol, Set<Integer>> rv = new LinkedHashMap<>();

        for (CpxIntTupleRule rule : r_prime) {
            Set<Pair<CpxIntTupleRule, Integer>> inRules = obl.getDepGraph(AbortionFactory.create()).getIn(rule);
            for (Pair<CpxIntTupleRule, Integer> in : inRules) {
                CpxIntTupleRule inRule = in.getKey();
                if (r_prime.contains(inRule)) {
                    continue;
                }
                FunctionSymbol f = inRule.getRights().get(in.y).getRootSymbol();
                assert rule.getRootSymbol().equals(f);
                for (int i = 0, l = f.getArity(); i < l; ++i) {
                    CallArgument alpha = new CallArgument(inRule, in.y, i);
                    ComplexityValue complexity = bounds.get(alpha);
                    if (!(complexity.isConstant() || complexity instanceof FixedDegreePoly)) {
                        Set<Integer> s = rv.get(f);
                        if (s == null) {
                            s = new LinkedHashSet<>();
                            rv.put(f, s);
                        }
                        s.add(i);
                    }
                }
            }
        }

        return rv;
    }
}
