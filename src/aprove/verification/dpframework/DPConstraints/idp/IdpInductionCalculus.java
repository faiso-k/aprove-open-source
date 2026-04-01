/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.DPConstraints.idp;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.DPConstraints.*;
import aprove.verification.dpframework.DPConstraints.idp.InfRuleConstraintRepl.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class IdpInductionCalculus extends AbstractInductionCalculus<BigIntImmutable> {

    public static class IDPOptions extends Options {

        public final IPathGenerator pathGenerator;

        public IDPOptions(final IPathGenerator pathGenerator, final int inductionCounter, final int rewritingCounter) {
            super(-1, -1, inductionCounter, rewritingCounter);
            this.pathGenerator = pathGenerator;
        }

    }

    public final StrategyLevel startStrategy = new StrategyLevel("startStrategy", new InfRule[] {
        new InfRuleAConstantFolding(),
        new InfRuleRewriting(InfRuleConstraintRepl.Mode.Full),
        new InfRuleDeleteTrivialReducesTo(),
        /* 1*/new InfRule12LeftCons(),
        /* 2*/new InfRule4DeleteA(),
        new InfRule3LeftVariableA(),
        new InfRule6SimplifyConditionA(),

        /* 3*/new InfRule3LeftConsRightVariableD(),

        /* 4*/new InfRule3LeftVariableB(),
        new InfRuleIdpBooleans(),
        new InfRule3LeftConsRightVariableE(),
        new InfRule3LeftVariableC()

    }, true);

    public final StrategyLevel standardStrategy = new StrategyLevel("standardStrategy", new InfRule[] {
        /* 1*/new InfRule12LeftCons(),
        new InfRuleRewriting(InfRuleConstraintRepl.Mode.Full),
        new InfRule3LeftVariableA(),
        new InfRule6SimplifyConditionA(),
        new InfRule4DeleteA(),
        new InfRule3LeftConsRightVariableD(),
        /* 4*/new InfRule3LeftVariableB(),
        /* 5*/new InfRule8FuncVar(),
        /* 6*/new InfRule4DeleteB(),
        new InfRule4DeleteE(),
        // new InfRule9ReverseSubstitution(), //////////////////// !!!!!!!!!!!!!!!!!!!!!!!!
        this.infRule5Induction, }, true);

    public final StrategyLevel preFinalStrategy = new StrategyLevel("preFinalStrategy", new InfRule[] {
        new InfRuleAConstantFolding(),
        new InfRuleDeleteTrivialReducesTo(),
        new InfRuleReplaceByVar(Mode.Full),
        /* 7*/new InfRule12LeftCons(),
        new InfRule3LeftVariableC(),
        new InfRule6SimplifyConditionB(),
        new InfRule3LeftConsRightVariableE(),
        new InfRuleIdpBooleans(), }, true);

    public final StrategyLevel finalStrategy = new StrategyLevelToPoly("nonInfPolyStrategy", this, new InfRule[] {
        new InfRuleUnboundedVars(),
        new InfRulePolyBSimple(), }, true);

    public final StrategyLevel finalCleanupStrategy = new StrategyLevel(
        "finalCleanupStrategy",
        new InfRule[] {new InfRulePolyGcd() },
        true);

    IDPProblem idp;
    final ImmutableSet<? extends GeneralizedRule> rules;
    final SimpleQTermSet q;
    private final StrategyLevel[] strategy;

    public static final ConstraintSet emptyConditions = ConstraintSet.create(new LinkedHashSet<Constraint>(0));

    public static final Set<TRSVariable> emptyQuantor = new LinkedHashSet<TRSVariable>(0);
    protected final Map<FunctionSymbol, Pair<Boolean[], CriticalPairs>> critPairsCache;

    /**
     * Standard constructor
     * @param idp      // the IDPProblem for which constraints are needed
     * @param proof    // a proof where the simplification steps are protocoled
     * @param options  // options
     * @param proc     // processor that uses the induction calculus
     * @param aborter  // standard aborter
     */
    public IdpInductionCalculus(
        final IDPProblem idp,
        final InductionCalculusProof proof,
        final IDPOptions options,
        final GInterpretation<BigIntImmutable> polyInterpretation,
        final StrategyLevel[] leveledStrategy,
        final Abortion aborter)
    {
        super(proof, options, polyInterpretation, aborter);
        this.idp = idp;
        this.rules = idp.getRuleAnalysis().getRAnalysis().getRules();
        this.q = idp.getRuleAnalysis().getQ();
        this.strategy = leveledStrategy;
        this.critPairsCache = new LinkedHashMap<FunctionSymbol, Pair<Boolean[], CriticalPairs>>();
    }

    @Override
    protected Set<FunctionSymbol> createConstructorSymbols() {
        final Set<FunctionSymbol> symbols =
            new LinkedHashSet<FunctionSymbol>(this.idp.getRuleAnalysis().getFunctionSymbolsPRNoHead());
        symbols.removeAll(this.idp.getRuleAnalysis().getDefinedSymbols());
        final IDPPredefinedMap predefinedMap = this.idp.getRuleAnalysis().getPreDefinedMap();
        final Iterator<FunctionSymbol> iter = symbols.iterator();
        while (iter.hasNext()) {
            final FunctionSymbol fs = iter.next();
            if (predefinedMap.getPredefinedFunction(fs) != null) {
                iter.remove();
            }
        }
        return symbols;
    }

    @Override
    protected Set<FunctionSymbol> createDefinedRSymbols() {
        final Set<FunctionSymbol> symbols =
            new LinkedHashSet<FunctionSymbol>(this.idp.getRuleAnalysis().getRAnalysis().getFunctionSymbols());
        symbols.removeAll(this.constructorSymbols);
        return symbols;
    }

    public Set<FunctionSymbol> getDefiniedSymbols() {
        throw new UnsupportedOperationException("infinitely many defined symbols");
    }

    @Override
    public boolean isDefinedSymbol(final FunctionSymbol f) {
        if (this.idp.getRuleAnalysis().getPreDefinedMap().getPredefinedFunction(f) != null) {
            return true;
        } else {
            return super.isDefinedSymbol(f);
        }
    }

    @Override
    public boolean isGround(final TRSTerm t) {
        if (t.isVariable()) {
            return true;
        }
        final TRSFunctionApplication fa = (TRSFunctionApplication) t;
        if (this.idp.getRuleAnalysis().getPreDefinedMap().isUndefinedInt(fa.getRootSymbol())) {
            return true;
        } else if (this.isDefinedSymbol(fa.getRootSymbol())) {
            return false;
        }
        for (final TRSTerm arg : fa.getArguments()) {
            if (!this.isGround(arg)) {
                return false;
            }
        }
        return true;
    }

    @Override
    protected Set<FunctionSymbol> createNoHeadSymbols() {
        final Set<FunctionSymbol> symbols = new LinkedHashSet<FunctionSymbol>(this.createConstructorSymbols());
        symbols.removeAll(this.idp.getRuleAnalysis().getHeadSymbols());
        return symbols;
    }

    @Override
    protected Map<FunctionSymbol, ImmutableSet<GeneralizedRule>> createRuleMap() {
        return this.idp.getRuleAnalysis().getRAnalysis().getRuleMap();
    }

    @Override
    public Set<? extends GeneralizedRule> getRules() {
        return this.rules;
    }

    @Override
    public boolean isNormal(final TRSTerm t) {
        if (t.isVariable()) {
            return true;
        } else {
            final TRSFunctionApplication fa = (TRSFunctionApplication) t;
            if (this.idp.getRuleAnalysis().getPreDefinedMap().isUndefinedInt(fa.getRootSymbol())) {
                return true;
            }
        }
        return !this.q.canBeRewritten(t);
    }

    public IDPProblem getIdp() {
        return this.idp;
    }

    @Override
    public Map<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> createConstraintSetProRule(
        final int c,
        final int position)
    {
        IPathGenerator pathGenerator = ((IDPOptions) this.options).pathGenerator;
        if (pathGenerator == null) {
            pathGenerator = new MetricPathGenerator(new MetricPathGenerator.Arguments());
        }
        final Map<GeneralizedRule, List<Triple<List<Node>, Pair<Integer, VariableRenamedPath>, Itpf>>> formulas =
            new LinkedHashMap<GeneralizedRule, List<Triple<List<Node>, Pair<Integer, VariableRenamedPath>, Itpf>>>();
        for (final GeneralizedRule rule : this.idp.getP()) {
            formulas.put(rule, new ArrayList<Triple<List<Node>, Pair<Integer, VariableRenamedPath>, Itpf>>());
        }
        final IIDependencyGraph graph = this.idp.getIdpGraph();
        for (final Node node : graph.getNodes()) {
            final List<Pair<Integer, ? extends List<Node>>> paths = pathGenerator.paths(graph, node);
            final List<Triple<List<Node>, Pair<Integer, VariableRenamedPath>, Itpf>> ruleFormulas =
                formulas.get(node.rule);
            for (final Pair<Integer, ? extends List<Node>> path : paths) {
                final VariableRenamedPath varPath = VariableRenamedPath.create(path.y);
                final Itpf formula = graph.itpfPath(varPath);
                ruleFormulas.add(new Triple<List<Node>, Pair<Integer, VariableRenamedPath>, Itpf>(
                    path.y,
                    new Pair<Integer, VariableRenamedPath>(path.x, varPath),
                    formula));
            }
        }

        final Map<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> map =
            new LinkedHashMap<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>>();
        for (final Map.Entry<GeneralizedRule, List<Triple<List<Node>, Pair<Integer, VariableRenamedPath>, Itpf>>> ruleForm : formulas
            .entrySet())
        {
            final GeneralizedRule rule = ruleForm.getKey();
            final Map<List<GeneralizedRule>, List<Implication>> ruleImpl =
                new LinkedHashMap<List<GeneralizedRule>, List<Implication>>();
            for (final Triple<List<Node>, Pair<Integer, VariableRenamedPath>, Itpf> p : ruleForm.getValue()) {
                final List<GeneralizedRule> projection = new ArrayList<GeneralizedRule>(p.x.size());
                for (final Node n : p.x) {
                    projection.add(n.rule);
                }
                List<Implication> impls = ruleImpl.get(projection);
                if (impls == null) {
                    impls = new ArrayList<Implication>();
                    ruleImpl.put(projection, impls);
                }
                Itpf dnf = p.z.toDnf();
                // remove outer quantors
                while (dnf.isQuantor()) {
                    if (dnf.isAll()) {
                        throw new UnsupportedOperationException("no universal quantification supported");
                    }
                    dnf = ((ItpfQuantor) dnf).getChild();
                }
                Set<? extends Itpf> conjClauses;
                if (dnf.isOr()) {
                    conjClauses = ((ItpfOr) dnf).getChildren();
                } else {
                    conjClauses = Collections.singleton(dnf);
                }
                final Constraint conclusion = this.createConclusion(p.y.y, p.y.x);
                for (final Itpf conjClause : conjClauses) {
                    impls.add(Implication.create(
                        new LinkedHashSet<TRSVariable>(0),
                        this.convertConjClause(conjClause),
                        conclusion,
                        null));
                }
            }
            map.put(rule, ruleImpl);
        }
        return map;
    }

    protected ConstraintSet convertConjClause(final Itpf clause) {
        Set<? extends Itpf> literals;
        if (clause.isAnd()) {
            literals = ((ItpfAnd) clause).getChildren();
        } else {
            literals = Collections.singleton(clause);
        }
        final Set<Constraint> constraints = new LinkedHashSet<Constraint>();
        for (final Itpf literal : literals) {
            if (literal.isItp()) {
                final ItpfItp itp = (ItpfItp) literal;
                if (itp.getRelation() == ItpRelation.EQ) {
                    constraints.add(ReducesTo.create(
                        itp.getL(),
                        itp.getR(),
                        this.getPredefinedParent(itp.getContextL()),
                        new Count(),
                        null));
                    constraints.add(ReducesTo.create(
                        itp.getR(),
                        itp.getL(),
                        this.getPredefinedParent(itp.getContextR()),
                        new Count(),
                        null));
                } else if (itp.getRelation() == ItpRelation.TO || itp.getRelation() == ItpRelation.TO_TRANS) {
                    constraints.add(ReducesTo.create(
                        itp.getL(),
                        itp.getR(),
                        this.getPredefinedParent(itp.getContextL()),
                        new Count(),
                        null));
                }
            }
        }
        return ConstraintSet.flatCreate(constraints);
    }

    protected PredefinedFunction<? extends Domain> getPredefinedParent(
        final List<ImmutablePair<FunctionSymbol, Integer>> context)
    {
        if (context != null && !context.isEmpty()) {
            final FunctionSymbol parent = context.get(context.size() - 1).x;
            return this.idp.getRuleAnalysis().getPreDefinedMap().getPredefinedFunction(parent);
        }
        return null;
    }

    protected Constraint createConclusion(final VariableRenamedPath variableRenamedPath, final int position) {
        final Set<Constraint> res = new LinkedHashSet<Constraint>();
        final ImmutablePair<Node, ImmutableMap<TRSVariable, TRSVariable>> step = variableRenamedPath.getPath().get(position);
        final TRSSubstitution sigma = TRSSubstitution.create(step.y, true);
        final TRSFunctionApplication leftSigma = step.x.rule.getLeft().applySubstitution(sigma);
        final TRSTerm rightSigma = step.x.rule.getRight().applySubstitution(sigma);
        res.add(Predicate.create(
            leftSigma,
            rightSigma,
            Predicate.Kind.AbstractRelation,
            GeneralizedRule.create(
                leftSigma,
                rightSigma,
                step.x.rule.getLhsInStandardRepresentation(),
                step.x.rule.getRhsInStandardRepresentation()),
            RelDependency.Decreasing,
            RelDependency.Increasing));
        res.add(UsableAtom.create(rightSigma, ConstraintType.GE, RelDependency.Increasing, this.polyInterpretation));
        return ConstraintSet.create(res);
    }

    @Override
    protected StrategyLevel[] initLeveledStrategy() {
        if (this.strategy != null) {
            return this.strategy;
        } else {
            return new StrategyLevel[] {
                this.startStrategy,
                null,
                this.standardStrategy,
                this.preFinalStrategy,
                this.finalStrategy,
                null };
        }
    }

    @Override
    public boolean isIdpMode() {
        return true;
    }

    @Override
    public boolean isDeterminisic(final FunctionSymbol fs, final Abortion aborter) throws AbortionException {
        return this.idp.getRuleAnalysis().getPreDefinedMap().isPredefined(fs) || !this.isDefinedSymbol(fs);
    }

    @Override
    public boolean isDeterministic(final TRSTerm t, final Abortion aborter) throws AbortionException {
        if (t.isVariable()) {
            return false;
        } else {
            final TRSFunctionApplication fa = (TRSFunctionApplication) t;
            final FunctionSymbol fs = fa.getRootSymbol();
            if (this.idp.getRuleAnalysis().getPreDefinedMap().isPredefined(fs)) {
                return true;
            }
            final Pair<Boolean[], CriticalPairs> fsAnalyzation = this.analyzeFs(fs, aborter);
            return fsAnalyzation.y.isNonOverlapping(aborter);
        }
        /*
        for (Term subTerm : t.getSubTerms()) {
            if (!subTerm.isVariable()) {
                FunctionApplication fa = (FunctionApplication) subTerm;
                if (!isDeterminisic(fa.getRootSymbol()) && !isNormal(fa)) {
                    return false;
                }
            }
        }
        return true;
        */
    }

    /**
     *
     * @param t
     * @param aborter
     * @return true if t evaluates to an int constant or another unique normal form
     * wrt. arbitrary substitutions
     * @throws AbortionException
     */
    public boolean evaluatesToConstantInt(final TRSTerm t, final Abortion aborter) throws AbortionException {
        if (t.isVariable()) {
            return false;
        } else {
            final TRSFunctionApplication fa = (TRSFunctionApplication) t;
            final FunctionSymbol fs = fa.getRootSymbol();
            final Pair<Boolean[], CriticalPairs> fsAnalyzation = this.analyzeFs(fs, aborter);
            for (int i = fsAnalyzation.x.length - 1; i >= 0; i--) {
                if (!fsAnalyzation.x[i] && !this.evaluatesToConstantInt(fa.getArgument(i), aborter)) {
                    return false;
                }
            }
            try {
                if (!this.idp.getRuleAnalysis().getPreDefinedMap().isPredefined(fs)
                    && (fsAnalyzation.y == null || !fsAnalyzation.y.isNonOverlapping(aborter)))
                {
                    return false;
                }
            } catch (final NullPointerException e) {
                e.printStackTrace();
            }
            // is an argument used that is not deterministic?
        }
        return true;
    }

    protected Pair<Boolean[], CriticalPairs> analyzeFs(final FunctionSymbol fs, final Abortion aborter)
        throws AbortionException
    {
        Pair<Boolean[], CriticalPairs> cached = this.critPairsCache.get(fs);
        if (cached == null) {
            final RuleAnalysis<GeneralizedRule> rRules = this.getIdp().getRuleAnalysis().getRAnalysis();
            final ImmutableSet<GeneralizedRule> fsRules = rRules.getRuleMap().get(fs);
            final Boolean[] varIgnoring = new Boolean[fs.getArity()];
            if (fsRules != null) {
                final Map<FunctionSymbol, Set<GeneralizedRule>> smallMap =
                    new LinkedHashMap<FunctionSymbol, Set<GeneralizedRule>>();
                smallMap.put(fs, fsRules);
                final CriticalPairs criticalPairs =
                    new CriticalPairs(this.idp
                        .getRuleAnalysis()
                        .getUseableRulesEstimation(null)
                        .getUsableRules(this.idp.getRuleAnalysis().getRAnalysis().getRuleMap().get(fs)), this.idp
                        .getRuleAnalysis()
                        .getRAnalysis()
                        .getRuleMap());
                // check for unused vars
                for (final GeneralizedRule r : fsRules) {
                    final TRSFunctionApplication lhs = r.getLeft();
                    final Set<TRSVariable> rightVariables = r.getRight().getVariables();
                    for (int i = fs.getArity() - 1; i >= 0; i--) {
                        final TRSTerm arg = lhs.getArgument(i);
                        varIgnoring[i] = arg.isVariable() && !rightVariables.contains(arg);
                    }
                }
                cached = new Pair<Boolean[], CriticalPairs>(varIgnoring, criticalPairs);
            } else {
                for (int i = fs.getArity() - 1; i >= 0; i--) {
                    varIgnoring[i] = true;
                }
                cached = new Pair<Boolean[], CriticalPairs>(varIgnoring, null);
            }
            this.critPairsCache.put(fs, cached);
        }
        return cached;
    }

}
