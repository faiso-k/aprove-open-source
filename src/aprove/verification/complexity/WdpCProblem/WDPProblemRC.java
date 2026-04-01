package aprove.verification.complexity.WdpCProblem;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Weak Dependency Pairs problem.
 *
 * See "Automated Complexity Analysis Based on the Dependency Method"
 */
// FIXME Rename!
public class WDPProblemRC extends DefaultBasicObligation {

    private final boolean innermost;

    private final ImmutableSet<Rule> rules;
    private final ImmutableSet<Rule> pairs;

    private final ImmutableSet<FunctionSymbol> compoundSymbols;
    private final ImmutableSet<FunctionSymbol> definedRSymbols;
    private final ImmutableSet<FunctionSymbol> definedPSymbols;

    protected WDPProblemRC(ImmutableSet<Rule> rules, ImmutableSet<Rule> pairs,
            ImmutableSet<FunctionSymbol> compoundSymbols,
            ImmutableSet<FunctionSymbol> definedRSymbols,
            ImmutableSet<FunctionSymbol> definedPSymbols,
            boolean innermost) {
        super("WdpProblemRC", "Weak Dependency Pairs Complexity Problem");
        this.compoundSymbols = compoundSymbols;
        this.definedRSymbols = definedRSymbols;
        this.definedPSymbols = definedPSymbols;
        this.innermost = innermost;
        this.rules = rules;
        this.pairs = pairs;
    }

    public static WDPProblemRC create(ImmutableSet<Rule> rules, boolean innermost) {
        PairComputeState state = WDPProblemRC.computePairs(rules, innermost);

        return new WDPProblemRC(rules,
                ImmutableCreator.create(state.pairs),
                ImmutableCreator.create(state.compoundSymbols),
                ImmutableCreator.create(state.definedRSymbols),
                ImmutableCreator.create(CollectionUtils.getRootSymbols(state.pairs)),
                innermost);
    }

    public static WDPProblemRC create(ImmutableSet<Rule> rules,
            ImmutableSet<Rule> pairs,
            ImmutableSet<FunctionSymbol> compoundSymbols,
            boolean innermost) {
        return new WDPProblemRC(rules,
                pairs,
                compoundSymbols,
                ImmutableCreator.create(CollectionUtils.getRootSymbols(rules)),
                ImmutableCreator.create(CollectionUtils.getRootSymbols(pairs)),
                innermost);
    }

    public static WDPProblemRC create(ImmutableSet<Rule> rules,
            ImmutableSet<Rule> pairs,
            ImmutableSet<FunctionSymbol> compoundSymbols,
            ImmutableSet<FunctionSymbol> definedRSymbols,
            boolean innermost) {
        return new WDPProblemRC(rules,
                pairs,
                compoundSymbols,
                definedRSymbols,
                ImmutableCreator.create(CollectionUtils.getRootSymbols(pairs)),
                innermost);
    }
    /**
     * Computes Weak (Innermost) Dependency Pairs
     */
    public static PairComputeState computePairs(ImmutableSet<Rule> rules,
            boolean innermost) {
        PairComputeState state = new PairComputeState();
        state.pairs = new LinkedHashSet<Rule>(rules.size());
        state.compoundSymbols = new HashSet<FunctionSymbol>();
        state.definedRSymbols = CollectionUtils.getRootSymbols(rules);
        state.fng = new FreshNameGenerator(
                CollectionUtils.getFunctionSymbols(rules),
                FreshNameGenerator.DEPENDENCY_PAIRS);
        state.innermost = innermost;
        for (Rule r : rules) {
            FunctionSymbol rootSym = r.getRootSymbol();
            FunctionSymbol pairSym = FunctionSymbol.create(
                    state.fng.getFreshName(rootSym.getName(), true),
                    rootSym.getArity());
            TRSFunctionApplication pairLhs =
                TRSTerm.createFunctionApplication(pairSym, r.getLeft().getArguments());
            TRSTerm pairRhs = WDPProblemRC.computePairRhs(r.getRight(), state);
            state.pairs.add(Rule.create(pairLhs, pairRhs));
        }
        return state;
    }

    private static TRSTerm computePairRhs(TRSTerm t,
            PairComputeState state) {
        List<TRSTerm> interesting = WDPProblemRC.computeContextHoles(t, state);
        int isize = interesting.size();
        if (isize == 1) {
            return interesting.get(0);
        } else {
            FunctionSymbol compound = FunctionSymbol.create(
                    state.fng.getFreshName("c", false, FreshNameGenerator.APPEND_NUMBERS),
                    isize);
            state.compoundSymbols.add(compound);
            return TRSTerm.createFunctionApplication(compound,
                    ImmutableCreator.create(new ArrayList<TRSTerm>(interesting)));
        }
    }

    /**
     * For a term of form C<t1, ..., tn>_X, compute [t1, ..., tn].
     *
     * See "Automated Complexity Analysis Based on the Dependency Method", section 3.
     * @param t
     * @param definedRSymbols
     * @param fng
     * @param innermost
     * @return
     */
    private static List<TRSTerm> computeContextHoles(TRSTerm t, PairComputeState state) {
        if (t.isVariable()) {
            if (state.innermost) {
                return java.util.Collections.emptyList();
            } else {
                return java.util.Collections.singletonList(t);
            }
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
            TRSTerm interesting = TRSTerm.createFunctionApplication(pairSym, args);
            return java.util.Collections.singletonList(interesting);
        } else {
            int argc = args.size();
            if (argc == 0) {
                return java.util.Collections.emptyList();
            } else if (argc == 1) {
                return WDPProblemRC.computeContextHoles(args.get(0), state);
            } else {
                List<TRSTerm> newInteresting = new ArrayList<TRSTerm>();
                for (TRSTerm arg : args) {
                    newInteresting.addAll(WDPProblemRC.computeContextHoles(arg, state));
                }
                return newInteresting;
            }
        }
    }

    public boolean isInnermost() {
        return this.innermost;
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
        sb.append(o.escape("Weak " + (this.innermost ? "innermost " : "") + "Dependency Pair Problem"));
        sb.append(o.newline());
        sb.append(o.escape("Rules:"));
        sb.append(o.set(this.rules, Export_Util.RULES));
        sb.append(o.escape("Pairs:"));
        sb.append(o.set(this.pairs, Export_Util.RULES));
        sb.append(o.escape("Defined Symbols:"));
        sb.append(o.set(this.definedRSymbols, Export_Util.NICE_SET));
        sb.append(o.escape("Compound Symbols:"));
        sb.append(o.set(this.compoundSymbols, Export_Util.NICE_SET));
        return sb.toString();
    }

    private static class PairComputeState {
        Set<Rule> pairs;
        Set<FunctionSymbol> compoundSymbols;
        Set<FunctionSymbol> definedRSymbols;
        FreshNameGenerator fng;
        boolean innermost;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return null;
    }
}
