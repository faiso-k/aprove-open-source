package aprove.verification.complexity.LowerBounds.Slicing;

import java.util.*;
import java.util.Map.*;

import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.CpxRelTrsProblem.Processors.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;



public class CpxTrsLowerBoundsSlicingProcessor extends CpxRelTrsProcessor {

    private class Worker {

        private CpxRelTrsProblem cpxRelTrs;
        private Set<Rule> allRules = new LinkedHashSet<>();;
        private CollectionMap<FunctionSymbol, Integer> doSlice = new CollectionMap<>();

        Worker(CpxRelTrsProblem cpxRelTrs) {
            this.cpxRelTrs = cpxRelTrs;
            allRules.addAll(cpxRelTrs.getR());
            allRules.addAll(cpxRelTrs.getS());
        }

        Result work() {
            BasicObligation sliced = this.slice();
            Result res = ResultFactory.unsuccessful();
            for (Collection<Integer> positions: this.doSlice.values()) {
                if (!positions.isEmpty()) {
                    res = ResultFactory.proved(sliced, LowerBound.create(), new SlicingProof(this.doSlice));
                    break;
                }
            }
            return res;
        }

        private BasicObligation slice() {
            for (FunctionSymbol c : cpxRelTrs.getSignature()) {
                this.initSlicing(c);
            }
            boolean changed;
            do {
                changed = this.filterSlicing();
            } while (changed);

            if (this.doSlice.isEmpty()) {
                return cpxRelTrs;
            }
            Map<FunctionSymbol, FunctionSymbol> newSymbols = new LinkedHashMap<>();
            for (FunctionSymbol c : cpxRelTrs.getSignature()) {
                if (this.doSlice.containsKey(c)) {
                    newSymbols.put(c, FunctionSymbol.create(c.getName(), c.getArity() - this.doSlice.get(c).size()));
                } else {
                    newSymbols.put(c, c);
                }
            }
            Set<Rule> newRules = sliceRules(newSymbols, cpxRelTrs.getR());
            Set<Rule> newRelativeRules = sliceRules(newSymbols, cpxRelTrs.getS());
            if (cpxRelTrs.isDerivational()) {
                return DerivationalComplexityRelTrsProblem.create(ImmutableCreator.create(newRules),
                        ImmutableCreator.create(newRelativeRules),
                        cpxRelTrs.getRewriteStrategy(),
                        cpxRelTrs.STerminatesInnermost());
            } else {
                return RuntimeComplexityRelTrsProblem.create(ImmutableCreator.create(newRules),
                        ImmutableCreator.create(newRelativeRules),
                        cpxRelTrs.getRewriteStrategy(),
                        cpxRelTrs.STerminatesInnermost());
            }
        }

        private Set<Rule> sliceRules(Map<FunctionSymbol, FunctionSymbol> newSymbols, Set<Rule> toSlice) {
            Set<Rule> newRules = new LinkedHashSet<>();
            for (Rule r : toSlice) {
                TRSTerm newLeft = this.slice(r.getLeft(), this.doSlice, newSymbols);
                TRSTerm newRight = this.slice(r.getRight(), this.doSlice, newSymbols);
                Set<TRSVariable> freeVars = new LinkedHashSet<>();
                freeVars.addAll(newRight.getVariables());
                freeVars.removeAll(newLeft.getVariables());
                for (TRSVariable v : freeVars) {
                    newRight = newRight.replaceAll(v,
                            TRSTerm.createFunctionApplication(FunctionSymbol.create(v.getName(), 0)));
                }
                newRules.add(Rule.create((TRSFunctionApplication) newLeft, newRight));
            }
            return newRules;
        }

        /* fill doSlice suitable heuristics */
        private void initSlicing(FunctionSymbol c) {
            ARGUMENT: for (int i = 0; i < c.getArity(); i++) {
                for (Rule r : allRules) {
                    for (TRSFunctionApplication t : r.getLeft().getNonVariableSubTerms()) {
                        if (t.getRootSymbol().equals(c)) {
                            TRSTerm arg = t.getArgument(i);
                            // do not slice arguments that are pattern-matched
                            if (!arg.isVariable()) {
                                continue ARGUMENT;
                            }
                        }
                    }
                    for (TRSFunctionApplication t : r.getRight().getNonVariableSubTerms()) {
                        if (t.getRootSymbol().equals(c)) {
                            TRSTerm arg = t.getArgument(i);
                            Set<FunctionSymbol> intersection = new HashSet<>(cpxRelTrs.getDefinedSymbols());
                            intersection.retainAll(arg.getFunctionSymbols());
                            if (!intersection.isEmpty()) {
                                // do not slice argument positions with function calls
                                continue ARGUMENT;
                            }
                        }
                    }
                }
                this.doSlice.add(c, i);
            }
        }

        /*
         * filter doSlice
         * - using the information from dontSlice and
         * - in such a way that there are no free variables on right hand sides
         */
        private boolean filterSlicing() {
            boolean changed = false;
            for (FunctionSymbol c : this.doSlice.keySet()) {
                Iterator<Integer> it = this.doSlice.get(c).iterator();
                IT: while (it.hasNext()) {
                    int pos = it.next();
                    for (Rule r : allRules) {
                        for (TRSFunctionApplication s : r.getLeft().getNonVariableSubTerms()) {
                            if (s.getRootSymbol().equals(c)) {
                                TRSTerm arg = s.getArgument(pos);
                                if (!this.varSlicedOnRhs(r, arg, this.doSlice)) {
                                    it.remove();
                                    changed = true;
                                    continue IT;
                                }
                            }
                        }
                    }
                }
            }
            return changed;
        }

        /* Check whether all occurrences of 'var' on the rhs of the given rule are sliced. */
        private boolean varSlicedOnRhs(Rule r, TRSTerm var, CollectionMap<FunctionSymbol, Integer> doSlice) {
            if (r.getRight().getVariables().contains(var)) {
                if (r.getRight().equals(var)) {
                    return false;
                }
                VARPOS: for (Position pi : r.getRight().getVariablePositions().get(var)) {
                    for (Position tau = pi.shorten(1); tau != null; tau =
                            tau.isEmptyPosition() ? null : tau.shorten(1)) {
                        TRSTerm subTerm = r.getRight().getSubterm(tau);
                        FunctionSymbol f = ((TRSFunctionApplication) subTerm).getRootSymbol();
                        for (int slicedPos : doSlice.getNotNull(f)) {
                            if (tau.append(slicedPos).isPrefixOf(pi)) {
                                continue VARPOS;
                            }
                        }
                    }
                    return false;
                }
            }
            return true;
        }

        /* create the sliced rules */
        private TRSTerm slice(TRSTerm tArg,
                CollectionMap<FunctionSymbol, Integer> doSlice,
                Map<FunctionSymbol, FunctionSymbol> newSymbols) {
            TRSTerm t = tArg;
            for (TRSFunctionApplication s : t.getNonVariableSubTerms()) {
                FunctionSymbol c = s.getRootSymbol();
                if (doSlice.containsKey(c)) {
                    Collection<Integer> sliced = doSlice.get(c);
                    ArrayList<TRSTerm> args = new ArrayList<>();
                    for (int i = 0; i < s.getRootSymbol().getArity(); i++) {
                        if (!sliced.contains(i)) {
                            args.add(s.getArgument(i));
                        }
                    }
                    t = t.replaceAll(s,
                            TRSTerm.createFunctionApplication(newSymbols.get(c), ImmutableCreator.create(args)));
                }
            }
            return t;
        }
    }

    @Override
    protected boolean isCpxRelTrsApplicable(CpxRelTrsProblem obl) {
        boolean rLinear = obl.getR().stream().allMatch(x -> x.getLeft().getVariableCount().values().stream().allMatch(y -> y <= 1));
        boolean sLinear = obl.getS().stream().allMatch(x -> x.getLeft().getVariableCount().values().stream().allMatch(y -> y <= 1));
        return (obl.STerminatesInnermost() || obl.getRewriteStrategy() == RewriteStrategy.FULL)
                && rLinear && sLinear && (! obl.getRewriteStrategy().contractsMultipleRedexes())
                && Options.certifier == Certifier.NONE;
    }

    @Override
    protected Result processCpxRelTrs(CpxRelTrsProblem obl, Abortion aborter, RuntimeInformation rti) {
        return new Worker(obl).work();
    }

    private static class SlicingProof extends DefaultProof {

        private CollectionMap<FunctionSymbol, Integer> doSlice = new CollectionMap<>();

        public SlicingProof(CollectionMap<FunctionSymbol, Integer> doSlice) {
            super();
            for (Entry<FunctionSymbol, Collection<Integer>> e: doSlice.entrySet()) {
                FunctionSymbol f = e.getKey();
                for (int pos: e.getValue()) {
                    this.doSlice.add(f, pos);
                }
            }
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            String res = o.escape("Sliced the following arguments:");
            res += o.linebreak();
            for (Entry<FunctionSymbol, Collection<Integer>> e : this.doSlice.entrySet()) {
                Collection<Integer> slicedArgs = e.getValue();
                for (int argPos : slicedArgs) {
                    FunctionSymbol f = e.getKey();
                    res += f.export(o);
                    res += o.escape("/" + argPos);
                    res += o.linebreak();
                }
            }
            return res;
        }

    }

}
