package aprove.verification.complexity.CpxTrsProblem.Processors.Utility;

import static aprove.verification.oldframework.Utility.Collection_Util.*;
import static java.util.stream.Collectors.*;

import java.util.*;
import java.util.Map.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class NestedDefinedSymbolComputation {

    private RuntimeComplexityTrsProblem trs;
    private Set<TRSTerm> startTerms;
    private Set<Rule> activeRules;
    private CollectionMap<Pair<FunctionSymbol, Integer>, FunctionSymbol> cachedRes;

    private class NestedDefinedSymbolProof extends DefaultProof {

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            Set<Rule> removedRules = new LinkedHashSet<>(trs.getRules());
            removedRules.removeAll(activeRules);
            StringBuilder proof = new StringBuilder();
            boolean empty = true;
            for (Entry<Pair<FunctionSymbol, Integer>, Collection<FunctionSymbol>> e: cachedRes.entrySet()) {
                FunctionSymbol f = e.getKey().x;
                int arg = e.getKey().y;
                Collection<FunctionSymbol> nested = e.getValue();
                if (!nested.isEmpty()) {
                    empty = false;
                    proof.append(o.export("The following defined symbols can occur below the " + arg + "th argument of ") + f.export(o) + o.export(": "));
                    Iterator<FunctionSymbol> it = nested.iterator();
                    while (it.hasNext()) {
                        FunctionSymbol g = it.next();
                        proof.append(g.export(o));
                        if (it.hasNext()) {
                            proof.append(o.export(", "));
                        }
                    }
                    proof.append(o.linebreak());
                }
            }
            if (empty) {
                proof.append(o.export("The TRS does not nest defined symbols."));
            }
            proof.append(o.linebreak());
            proof.append(o.export("Hence, the left-hand sides of the following rules are not basic-reachable and can be removed:"));
            proof.append(o.linebreak());
            for (Rule r: removedRules) {
                proof.append(r.export(o));
                proof.append(o.linebreak());
            }
            return proof.toString();
        }

    }

    public NestedDefinedSymbolComputation(CpxRelTrsProblem trs) {
        this(trs.getRules(), trs.getRules().stream().filter(x -> trs.isBasic(x.getLeft())).map(x -> x.getRight()).collect(toSet()));
    }

    public NestedDefinedSymbolComputation(Set<Rule> rules, Set<TRSTerm> startTerms) {
        this.trs = RuntimeComplexityTrsProblem.create(ImmutableCreator.create(rules), RewriteStrategy.FULL);
        this.startTerms = startTerms;
        this.activeRules = rules.stream().filter(x -> trs.isBasic(x.getLeft())).collect(toSet());
    }

    public CollectionMap<Pair<FunctionSymbol, Integer>, FunctionSymbol> definedArguments() {
        if (cachedRes == null) {
            do {
                cachedRes = new NestedDefinedSymbolFixedPointIteration().definedArguments();
            } while(updateActiveRules());
        }
        return cachedRes;
    }

    public Set<Rule> activeRules() {
        if (cachedRes == null) {
            do {
                cachedRes = new NestedDefinedSymbolFixedPointIteration().definedArguments();
            } while(updateActiveRules());
        }
        return activeRules;
    }

    private boolean updateActiveRules() {
        boolean changed = false;
        RULE: for (Rule r: trs.getRules()) {
            for (TRSFunctionApplication t: r.getLeft().getNonVariableSubTerms()) {
                if (trs.isDefined(t.getRootSymbol())) {
                    for (int i = 0; i < t.getArity(); i++) {
                        Pair<FunctionSymbol, Integer> key = new Pair<>(t.getRootSymbol(), i);
                        if (!cachedRes.getNotNull(key).containsAll(intersection(trs.getDefinedSymbols(), t.getArgument(i).getFunctionSymbols()))) {
                            continue RULE;
                        }
                    }
                }
            }
            changed |= activeRules.add(r);
        }
        return changed;
    }

    private class NestedDefinedSymbolFixedPointIteration {

        private CollectionMap<Pair<FunctionSymbol, Integer>, FunctionSymbol> outerRes = new CollectionMap<>();
        private DependencyGraph<CpxRelTrsProblem> depGraph = new DependencyGraph<>(RuntimeComplexityTrsProblem.createSub(trs, activeRules), true);

        CollectionMap<Pair<FunctionSymbol, Integer>, FunctionSymbol> definedArguments() {
            nestedDefinedSymbolsFromStartTerms();
            nestedDefinedSymbolsFromNonConstructorBasedRules();
            findFixedpoint();
            return outerRes;
        }

        private void nestedDefinedSymbolsFromNonConstructorBasedRules() {
            for (Rule r: activeRules) {
                if (trs.isBasic(r.getLeft())) {
                    continue;
                }
                TRSTerm rhs = r.getRight();
                for (TRSFunctionApplication t: rhs.getNonVariableSubTerms()) {
                    if (!trs.isDefined(t.getRootSymbol())) {
                        continue;
                    }
                    for (int i = 0; i < t.getArity(); i++) {
                        Set<FunctionSymbol> info = computeInfo(t.getArgument(i));
                        addNestedDefinedSymbol(t.getRootSymbol(), i, info, outerRes);
                    }
                }
            }
        }

        private Set<FunctionSymbol> computeInfo(TRSTerm t) {
            return getReachable(intersection(t.getFunctionSymbols(), trs.getDefinedSymbols()), depGraph);
        }

        /**
         * For each rule p -> D[C[t]] where root(C) is defined and t contains defined symbols, C is contained in the result.
         */
        private void nestedDefinedSymbolsFromStartTerms() {
            for (TRSTerm rhs: startTerms) {
                for (TRSFunctionApplication t: rhs.getNonVariableSubTerms()) {
                    if (!trs.isDefined(t.getRootSymbol())) {
                        continue;
                    }
                    for (int i = 0; i < t.getArity(); i++) {
                        Set<FunctionSymbol> info = computeInfo(t.getArgument(i));
                        addNestedDefinedSymbol(t.getRootSymbol(), i, info, outerRes);
                    }
                }
            }
        }

        private void findFixedpoint() {
            boolean changed;
            do {
                changed = false;
                CollectionMap<Pair<FunctionSymbol, Integer>, FunctionSymbol> toAdd = new FixedPointStep(outerRes).run();
                CollectionMap<Pair<FunctionSymbol, Integer>, FunctionSymbol> oldRes = new CollectionMap<>(outerRes);
                addNestedDefinedSymbols(toAdd, outerRes);
                changed = !oldRes.equals(outerRes);
            } while (changed);
        }


        private Set<FunctionSymbol> getReachable(Set<FunctionSymbol> fs, DependencyGraph<?> depGraph) {
            Set<Node<FunctionSymbol>> ns = depGraph.getNodes().stream().filter(x -> fs.contains(x.getObject())).collect(toSet());
            return union(depGraph.getNodes().stream().filter(x -> ns.stream().anyMatch(n -> depGraph.hasPath(n, x))).map(x -> x.getObject()).collect(toSet()), fs);
        }

        private class FixedPointStep {

            CollectionMap<Pair<FunctionSymbol, Integer>, FunctionSymbol> innerRes = new CollectionMap<>();
            CollectionMap<Pair<FunctionSymbol, Integer>, FunctionSymbol> definedArguments;

            FixedPointStep(CollectionMap<Pair<FunctionSymbol, Integer>, FunctionSymbol> definedArguments) {
                this.definedArguments = new CollectionMap<>(definedArguments);
            }

            CollectionMap<Pair<FunctionSymbol, Integer>, FunctionSymbol> run() {
                for (Rule r: activeRules) {
                    inductiveStepForRule(r);
                }
                return innerRes;
            }

            void inductiveStepForRule(Rule r) {
                if (r.getRight().isVariable()) {
                    return;
                }
                TRSFunctionApplication lhs = r.getLeft();
                TRSTerm rhs = r.getRight();
                for (Entry<Pair<FunctionSymbol, Integer>, Collection<FunctionSymbol>> e: definedArguments.entrySet()) {
                    FunctionSymbol f = e.getKey().x;
                    Integer arg = e.getKey().y;
                    Collection<FunctionSymbol> info = e.getValue();
                    if (!lhs.getRootSymbol().equals(f)) {
                        continue;
                    }
                    for (TRSVariable x: lhs.getArgument(arg).getVariables()) {
                        Collection<Position> rhsXPositions = rhs.getVariablePositions().getOrDefault(x, Collections.emptyList());
                        for (Position pi: rhsXPositions) {
                            do {
                                int last = pi.lastIndex();
                                pi = pi.shorten(1);
                                TRSFunctionApplication rhsSub = (TRSFunctionApplication) rhs.getSubterm(pi);
                                if (trs.isDefined(rhsSub.getRootSymbol())) {
                                    innerRes.add(new Pair<>(rhsSub.getRootSymbol(), last), info);
                                }
                            } while (!pi.isEmptyPosition());
                        }
                    }
                }
            }

        }
    }

    private void addNestedDefinedSymbols(CollectionMap<Pair<FunctionSymbol, Integer>, FunctionSymbol> src, CollectionMap<Pair<FunctionSymbol, Integer>, FunctionSymbol> target) {
        for (Entry<Pair<FunctionSymbol, Integer>, Collection<FunctionSymbol>> e: src.entrySet()) {
            Pair<FunctionSymbol, Integer> key = e.getKey();
            target.add(key, e.getValue());
        }
    }

    private void addNestedDefinedSymbol(FunctionSymbol c, int i, Set<FunctionSymbol> info, CollectionMap<Pair<FunctionSymbol, Integer>, FunctionSymbol> target) {
        Pair<FunctionSymbol, Integer> key = new Pair<>(c, i);
        target.add(key, info);
    }

    public Proof getProof() {
        return new NestedDefinedSymbolProof();
    }

}
