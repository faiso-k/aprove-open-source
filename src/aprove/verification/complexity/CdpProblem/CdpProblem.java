package aprove.verification.complexity.CdpProblem;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Complexity Dependency Pairs problem.
 *
 * FIXME: Add documentation. There is not really a written down theory yet.
 */
public class CdpProblem extends DefaultBasicObligation {

    private final ImmutableSet<Rule> rules;
    private final ImmutableSet<Rule> pairs;

    private final ImmutableSet<FunctionSymbol> definedRSymbols;
    private final ImmutableSet<FunctionSymbol> definedPSymbols;
    private final ImmutableSet<FunctionSymbol> compoundSymbols;

    protected CdpProblem(ImmutableSet<Rule> rules, ImmutableSet<Rule> pairs,
            ImmutableSet<FunctionSymbol> compoundSymbols,
            ImmutableSet<FunctionSymbol> definedRSymbols,
            ImmutableSet<FunctionSymbol> definedPSymbols) {
        super("CdpProblem", "Dependency Pairs Complexity Problem");
        this.compoundSymbols = compoundSymbols;
        this.definedRSymbols = definedRSymbols;
        this.definedPSymbols = definedPSymbols;
        this.rules = rules;
        this.pairs = pairs;
    }

    public static CdpProblem create(ImmutableSet<Rule> rules) {
        PairComputeState state = CdpProblem.computePairs(rules);

        return new CdpProblem(rules,
                ImmutableCreator.create(state.pairs),
                ImmutableCreator.create(state.compoundSymbols),
                ImmutableCreator.create(state.definedRSymbols),
                ImmutableCreator.create(state.definedPSymbols));
    }

    public static CdpProblem create(ImmutableSet<Rule> rules, Set<Rule> p,
            Set<FunctionSymbol> compoundSymbols) {
        return new CdpProblem(rules,
                ImmutableCreator.create(p),
                ImmutableCreator.create(compoundSymbols),
                ImmutableCreator.create(CollectionUtils.getRootSymbols(rules)),
                ImmutableCreator.create(CollectionUtils.getRootSymbols(p)));
    }

    /**
     * Computes Complexity Innermost Dependency Pairs
     */
    public static PairComputeState computePairs(ImmutableSet<Rule> rules) {
        PairComputeState state = new PairComputeState();
        state.pairs = new LinkedHashSet<Rule>(rules.size());
        state.compoundSymbols = new HashSet<FunctionSymbol>();
        state.definedRSymbols = CollectionUtils.getRootSymbols(rules);
        state.definedPSymbols = new LinkedHashSet<FunctionSymbol>();
        state.fng = new FreshNameGenerator(
                CollectionUtils.getFunctionSymbols(rules),
                FreshNameGenerator.DEPENDENCY_PAIRS);
        for (Rule r : rules) {
            FunctionSymbol rootSym = r.getRootSymbol();
            FunctionSymbol pairSym = FunctionSymbol.create(
                    state.fng.getFreshName(rootSym.getName(), true),
                    rootSym.getArity());
            TRSFunctionApplication pairLhs =
                TRSTerm.createFunctionApplication(pairSym, r.getLeft().getArguments());
            TRSTerm pairRhs = CdpProblem.computePairRhs(r.getRight(), state);
            state.pairs.add(Rule.create(pairLhs, pairRhs));
        }
        return state;
    }

    /**
     * For a term t, create the term c(t1, ..., tn) where c is a fresh constant
     * symbol and t1, ..., tn are the subterms of t with a defined root symbol.
     */
    private static TRSTerm computePairRhs(TRSTerm t,
            PairComputeState state) {
        List<TRSTerm> interesting = new LinkedList<TRSTerm>();
        CdpProblem.getSubtermsWithDefinedRoot(t, state, interesting );
        FunctionSymbol compound = FunctionSymbol.create(
                state.fng.getFreshName("c", false, FreshNameGenerator.APPEND_NUMBERS),
                interesting.size());
        state.compoundSymbols.add(compound);
        return TRSTerm.createFunctionApplication(compound,
                ImmutableCreator.create(new ArrayList<TRSTerm>(interesting)));
    }

    /**
     * Computes a list of all subterms with a defined root symbols
     */
    private static void getSubtermsWithDefinedRoot(TRSTerm t, PairComputeState state, List<TRSTerm> interesting) {
        if (t.isVariable()) {
            return;
        }
        TRSFunctionApplication fa = (TRSFunctionApplication)t;
        FunctionSymbol rootSym = fa.getRootSymbol();
        ImmutableList<? extends TRSTerm> args = fa.getArguments();
        if (state.definedRSymbols.contains(rootSym)) {
            final FunctionSymbol pairSym =
                FunctionSymbol.create(
                    state.fng.getFreshName(rootSym.getName(), true),
                    rootSym.getArity()
                );
            state.definedPSymbols.add(pairSym);
            TRSTerm newT = TRSTerm.createFunctionApplication(pairSym, args);
            interesting.add(newT);
        }
        for (TRSTerm arg : args) {
            CdpProblem.getSubtermsWithDefinedRoot(arg, state, interesting);
        }
    }

    public boolean isInnermost() {
        return true;
    }

    public ImmutableSet<Rule> getR() {
        return this.rules;
    }

    public ImmutableSet<Rule> getP() {
        return this.pairs;
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

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder sb = new StringBuilder();
        sb.append(o.escape("Complexity innermost Dependency Pair Problem"));
        sb.append(o.newline());
        sb.append(o.escape("Rules:"));
        sb.append(o.set(this.rules, Export_Util.RULES));
        sb.append(o.escape("Pairs:"));
        sb.append(o.set(this.pairs, Export_Util.RULES));
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

    private static class PairComputeState {
        Set<Rule> pairs;
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
