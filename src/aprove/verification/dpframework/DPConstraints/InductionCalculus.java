package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * The InductionCalculus generates the implication(constraints)
 * for each DP in a given QDPProblem
 *
 * therefore it is an InfRuleContext
 * so it can provide some global information about the QDPProblem to some InfRule
 * which are applied to the constraints within the calculation process.
 *
 * @author swiste
 */
public class InductionCalculus extends AbstractInductionCalculus {

    QDPProblem qdp;

    /**
     * Standard constructor
     * @param qdp      // the QDPProblem for which constraints are needed
     * @param proof    // a proof where the simplification steps are protocolled
     * @param options  // options
     * @param aborter  // standard aborter
     */
    public InductionCalculus(
        final QDPProblem qdp,
        final InductionCalculusProof proof,
        final Options options,
        final Abortion aborter)
    {
        super(proof, options, null, aborter);
        this.qdp = qdp;
    }

    @Override
    protected Set<FunctionSymbol> createDefinedRSymbols() {
        return this.qdp.getRwithQ().getDefinedSymbolsOfR();
    }

    @Override
    protected Set<FunctionSymbol> createConstructorSymbols() {
        final Set<FunctionSymbol> symbols = new LinkedHashSet<FunctionSymbol>(this.qdp.getPRSignature());
        symbols.removeAll(this.createDefinedRSymbols());
        return symbols;
    }

    @Override
    protected Set<FunctionSymbol> createNoHeadSymbols() {
        final Set<FunctionSymbol> symbols = new LinkedHashSet<FunctionSymbol>(this.createConstructorSymbols());
        symbols.removeAll(this.qdp.getHeadSymbols());
        return symbols;
    }

    @Override
    public Set<? extends Rule> getRules() {
        return this.qdp.getR();
    }

    @Override
    public boolean isNormal(final TRSTerm t) {
        return !this.qdp.getQ().canBeRewritten(t);
    }

    @Override
    protected Map<FunctionSymbol, ImmutableSet<Rule>> createRuleMap() {
        return this.qdp.getRwithQ().getRuleMap();
    }

    @Override
    public Map<Rule, Map<List<Rule>, List<Implication>>> createConstraintSetProRule(final int c, final int position) {
        final int[] counter = new int[c];
        final QDependencyGraph qdg = this.qdp.getDependencyGraph();
        final Graph<Rule, ?> graph = qdg.getGraph();
        final Node<Rule>[] prules = graph.getNodes().toArray(new Node[0]);
        final int overflow = prules.length;
        final Map<Rule, Map<List<Rule>, List<Implication>>> map = new LinkedHashMap<>();
        for (int cDPi = 0; cDPi < prules.length; cDPi++) {
            for (int j = 0; j < c; j++) {
                counter[j] = 0;
            }
            counter[position] = cDPi; // set the currentDP an the fixing position
            final Node<Rule> pNrule = prules[cDPi];
            final Map<List<Rule>, List<Implication>> rsImpsMap = new LinkedHashMap<>();
            ChainLoop: do {
                final List<Constraint> cs = new LinkedList<>();
                final List<Rule> ps = new LinkedList<>();
                TRSTerm s = null;
                TRSTerm t = null;
                TRSTerm lastv = null;
                Rule origRule = null;
                Node<Rule> preNode = null;
                for (int i = 0; i < c; i++) {
                    final Node<Rule> pNfrule = prules[counter[i]];
                    if (preNode != null && !graph.contains(preNode, pNfrule)) {
                        continue ChainLoop;
                    }
                    preNode = pNfrule;
                    final Rule pfrule = pNfrule.getObject();
                    final TRSSubstitution subs = this.getFreshRenamingFor(pfrule.getVariables());
                    final TRSFunctionApplication u = pfrule.getLeft().applySubstitution(subs);
                    final TRSTerm v = pfrule.getRight().applySubstitution(subs);
                    final Rule renamedRule = Rule.create(u, v);
                    assert (pfrule.equals(renamedRule));
                    ps.add(renamedRule);
                    if (i == position) { // remember the renaming for the cDPi of selected position
                        s = u;
                        t = v;
                        origRule = pfrule;
                    }
                    if (lastv != null) {
                        cs.add(ReducesTo.create(lastv, u, null, new Count(), null));
                    }
                    lastv = v;
                }
                final List<Implication> rcs = new LinkedList<Implication>();
                rcs.add(Implication.create(
                    new HashSet<TRSVariable>(),
                    ConstraintSet.flatCreate(cs),
                    Predicate.create(s, t, Predicate.Kind.AbstractRelation, origRule, null, null),
                    null));
                rsImpsMap.put(ps, rcs);
            } while (AbstractInductionCalculus.inc(counter, overflow, position));
            map.put(pNrule.getObject(), rsImpsMap);
        }
        return map;
    }

    @Override
    protected StrategyLevel[] initLeveledStrategy() {
        return new StrategyLevel[] {
            this.startStrategy,
            null,
            this.standardStrategy,
            this.preFinalStrategy,
            this.finalStrategy,
            null };
    }

    @Override
    public boolean isIdpMode() {
        return false;
    }

    @Override
    public boolean isDeterminisic(final FunctionSymbol fs, final Abortion aborter) throws AbortionException {
        return !this.isDefinedSymbol(fs);
    }

    @Override
    public boolean isDeterministic(final TRSTerm t, final Abortion aborter) throws AbortionException {
        return this.isNormal(t);
    }

    @Override
    public boolean isGround(final TRSTerm left) {
        return this.constructorSymbols.containsAll(left.getFunctionSymbols());
    }

}
