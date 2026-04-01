package aprove.verification.complexity.AcdtProblem;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.complexity.AcdtProblem.Utils.*;
import aprove.verification.complexity.CdpProblem.Processors.Util.QtrsDirectGcdp.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * Complexity Dependency Tuples problem.
 *
 * FIXME: Add documentation. Always innermost
 *
 * FIXME: Cache UsableRulesCalculator?
 */
public class AcdtProblem extends DefaultBasicObligation implements DOT_Able {

    /**
     * The rules of this CdtProblem. All variables must be prefixed with
     * {@link IcapAlgorithm#PREFIX_NOTCAP}
     */
    private final ImmutableSet<Rule> rules;

    private final ImmutableSet<Acdt> cdts;
    private final BasicAcdtGraph graph;
    private final ImmutableSet<FunctionSymbol> definedRSymbols;

    /* Cached information */
    private final ImmutableSet<FunctionSymbol> definedPSymbols;
    private final ImmutableSet<FunctionSymbol> compoundSymbols;
    private final ImmutableSet<FunctionSymbol> signature;

    /**
     * @param rules See {@link #rules} for constraints.
     */
    protected AcdtProblem(ImmutableSet<Rule> rules, ImmutableSet<Acdt> cdts,
            BasicAcdtGraph graph,
            ImmutableSet<FunctionSymbol> compoundSymbols,
            ImmutableSet<FunctionSymbol> definedRSymbols,
            ImmutableSet<FunctionSymbol> definedPSymbols) {
        super("CdtProblem", "Complexity Dependency Tubles Problem");
        this.compoundSymbols = compoundSymbols;
        this.definedRSymbols = definedRSymbols;
        this.definedPSymbols = definedPSymbols;
        this.rules = rules;
        this.graph = graph;
        this.cdts = cdts;

        LinkedHashSet<FunctionSymbol> signature = new LinkedHashSet<FunctionSymbol>();
        signature.addAll(definedRSymbols);
        signature.addAll(CollectionUtils.getFunctionSymbols(rules));
        signature.addAll(CollectionUtils.getFunctionSymbols(cdts));
        this.signature = ImmutableCreator.create(signature);
    }

    public static AcdtProblem create(Set<Rule> rules, Set<FunctionSymbol> definedRSymbols) {
        ImmutableRuleSet<Rule> renRules = new ImmutableRuleSet<Rule>(
                IcapAlgorithm.renumberedRules(rules));
        TupleComputeState state = AcdtProblem.computeTuples(renRules, definedRSymbols);

        return new AcdtProblem(renRules,
                ImmutableCreator.create(state.cdts),
                BasicAcdtGraph.create(state.cdts, renRules),
                ImmutableCreator.create(state.compoundSymbols),
                ImmutableCreator.create(state.definedRSymbols),
                ImmutableCreator.create(state.definedPSymbols));
    }

    public static AcdtProblem create(Set<Rule> rules) {
        return AcdtProblem.create(rules, CollectionUtils.getRootSymbols(rules));
    }

    private static AcdtProblem uncheckedCreate(
            Set<Rule> rules,
            BasicAcdtGraph cdtGraph,
            ImmutableSet<FunctionSymbol> definedRSymbols) {
        ImmutableSet<Acdt> tuples = cdtGraph.getTuples();
        Set<FunctionSymbol> compoundSymbols = new LinkedHashSet<FunctionSymbol>(tuples.size());
        Set<FunctionSymbol> definedPSymbols = new LinkedHashSet<FunctionSymbol>();
        for (Acdt tuple : tuples) {
            TRSFunctionApplication right = tuple.getRuleRHS();
            compoundSymbols.add(right.getRootSymbol());
            definedPSymbols.add(tuple.getRule().getRootSymbol());
        }

        return new AcdtProblem(
                ImmutableCreator.create(rules),
                tuples,
                cdtGraph,
                ImmutableCreator.create(compoundSymbols),
                definedRSymbols,
                ImmutableCreator.create(definedPSymbols));
    }

    public AcdtProblem createSubproblem(BasicAcdtGraph cdtGraph) {
        if (Globals.useAssertions) {
            assert(this.cdts.containsAll(cdtGraph.getTuples()));
        }
        return AcdtProblem.uncheckedCreate(this.rules, cdtGraph, this.definedRSymbols);
    }

    public AcdtProblem createTransformed(Map<Node<Acdt>,Set<Acdt>>transformations) {
        BasicAcdtGraph transGraph = this.graph.getTransformedGraph(transformations);

        return AcdtProblem.uncheckedCreate(this.rules, transGraph, this.definedRSymbols);
    }
    /**
     * Creates a subproblem with a restricted set of rules.
     */
    public AcdtProblem createSubproblem(Set<Rule> rules) {
        if (Globals.useAssertions) {
            assert(this.getR().containsAll(rules));
        }
        return AcdtProblem.uncheckedCreate(rules, this.graph, this.definedRSymbols);
    }

    /**
     * Computes CDTS
     */
    public static TupleComputeState computeTuples(ImmutableSet<Rule> rules, Set<FunctionSymbol> definedRSymbols) {
        TupleComputeState state = new TupleComputeState();
        state.compoundSymbols = new LinkedHashSet<FunctionSymbol>(rules.size());
        state.definedRSymbols = java.util.Collections.unmodifiableSet(definedRSymbols);
        state.definedPSymbols =
            new LinkedHashSet<FunctionSymbol>(state.definedRSymbols.size());
        state.cdts = new LinkedHashSet<Acdt>(rules.size());
        state.fng = new FreshNameGenerator(
                CollectionUtils.getFunctionSymbols(rules),
                FreshNameGenerator.DEPENDENCY_PAIRS);

        for (Rule rule : rules) {
            TupleDefinedPositions tdps =
                TupleDefinedPositions.createFromRule(rule, state.definedRSymbols);
            Acdt cdt = Acdt.createFromRule(state.fng, rule, TRSSubstitution.EMPTY_SUBSTITUTION, tdps);
            state.definedPSymbols.add(cdt.getRuleLHS().getRootSymbol());
            state.compoundSymbols.add(cdt.getCompoundSym());
            state.cdts.add(cdt);
        }

        return state;
    }

    public boolean isInnermost() {
        return true;
    }

    public ImmutableSet<Rule> getR() {
        return this.rules;
    }

    public UsableRulesCalculator getURCalc() {
        return this.getGraph().getIcap().getURCalc();
    }

    public ImmutableSet<Acdt> getTuples() {
        return this.cdts;
    }

    public BasicAcdtGraph getGraph() {
        return this.graph;
    }

    public ImmutableSet<FunctionSymbol> getCompoundSymbols() {
        return this.compoundSymbols;
    }

    public ImmutableSet<FunctionSymbol> getDefinedRSymbols() {
        return this.definedRSymbols;
    }

    public ImmutableSet<FunctionSymbol> getDefinedPSymbols() {
        return this.definedPSymbols;
    }

    public ImmutableSet<FunctionSymbol> getSignature() {
        return this.signature;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder sb = new StringBuilder();
        sb.append(o.escape("Complexity Dependency Tuples Problem"));
        sb.append(o.newline());
        sb.append(o.escape("Rules:"));
        sb.append(o.set(this.getR(), Export_Util.RULES));
        sb.append(o.escape("Tuples:"));
        sb.append(o.set(this.cdts, Export_Util.RULES));
        sb.append(o.escape("Defined Rule Symbols:"));
        sb.append(o.set(this.definedRSymbols, Export_Util.NICE_SET));
        sb.append(o.newline());
        sb.append(o.escape("Defined Pair Symbols:"));
        sb.append(o.set(this.definedPSymbols, Export_Util.NICE_SET));
        sb.append(o.newline());
        sb.append(o.escape("Compound Symbols:"));
        sb.append(o.set(this.compoundSymbols, Export_Util.NICE_SET));
        sb.append(o.newline());
        return sb.toString();
    }

    @Override
    public String toDOT() {
        return this.graph.toDOT();
    }

    private static class TupleComputeState {
        Set<Acdt> cdts;
        Set<FunctionSymbol> compoundSymbols;
        Set<FunctionSymbol> definedRSymbols;
        Set<FunctionSymbol> definedPSymbols;
        FreshNameGenerator fng;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return null;
    }
}
