package aprove.verification.complexity.Utility;

import static aprove.verification.complexity.Utility.Util.*;
import static aprove.verification.oldframework.Utility.Collection_Util.*;
import static java.util.stream.Collectors.*;

import java.util.*;
import java.util.Map.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.LowerBounds.Util.Renaming.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

public class DefinedContextComputation implements Exportable {

    private RuleSet trs;
    private TRSFunctionApplication hole;
    private RenamingCentral renamingCentral;
    private Map<Context, Boolean> cachedRes = null;

    public DefinedContextComputation(RuleSet trs, RenamingCentral renamingCentral) {
        this.trs = trs;
        this.renamingCentral = renamingCentral;
        this.hole = TRSTerm.createFunctionApplication(renamingCentral.freshConstant("[]"));
    }

    public Map<Context, Boolean> definedContexts() {
        if (cachedRes == null) {
            cachedRes = new DefinedContextFixedPointIteration().definedContexts();
        }
        return cachedRes;
    }

    private boolean isConstructorTerm(TRSTerm t) {
        return t.getFunctionSymbols().stream().allMatch(x -> !trs.isDefined(x.getRootSymbol()));
    }

    private class DefinedContextFixedPointIteration {

        private Map<Context, Boolean> outerRes = new LinkedHashMap<>();
        private DependencyGraph<RuleSet> depGraph = new DependencyGraph<>(trs, true);

        Map<Context, Boolean> definedContexts() {
            initDefinedContexts();
            findFixedpointForDefinedContexts();
            return outerRes;
        }

        private boolean computeInfo(TRSTerm t) {
            if (!trs.isBasic(t)) {
                return false;
            } else {
                Set<FunctionSymbol> toConsider = getReachable(intersection(t.getFunctionSymbols(), trs.getDefinedSymbols()), depGraph);
                for (FunctionSymbol g: toConsider) {
                    for (Rule gr: trs.getRules()) {
                        if (gr.getRootSymbol().equals(g) && !trs.isBasic(gr.getRight()) && !isConstructorTerm(gr.getRight())) {
                            return false;
                        }
                    }
                }
            }
            return true;
        }

        /**
         * For each rule p -> D[C[t]] where root(C) is defined and t contains defined symbols, C is contained in the result.
         */
        private void initDefinedContexts() {
            for (TRSTerm rhs: trs.getRules().stream().map(x -> x.getRight()).collect(toSet())) {
                for (Pair<Position, TRSFunctionApplication> p: rhs.getNonRootNonVariablePositionsWithSubTerms()) {
                    Position innerDefinedPos = p.x;
                    TRSFunctionApplication innerDefinedTerm = p.y;
                    FunctionSymbol innerDefinedSymbol = innerDefinedTerm.getRootSymbol();
                    if (!trs.isDefined(innerDefinedSymbol)) {
                        continue;
                    }
                    for (Position outerDefinedPos: innerDefinedPos.getTruePrefixes()) {
                        TRSFunctionApplication outerDefinedTerm = (TRSFunctionApplication) rhs.getSubterm(outerDefinedPos);
                        FunctionSymbol outerDefinedSymbol = outerDefinedTerm.getRootSymbol();
                        if (!trs.isDefined(outerDefinedSymbol)) {
                            continue;
                        }
                        TRSTerm abstracted = linearizeAndAbstractInnerOccurrencesOf(outerDefinedTerm, trs.getDefinedSymbols(), renamingCentral);
                        Set<Position> abstractedPositions = abstracted.getPositions();
                        Position boxPos = innerDefinedPos.tail(outerDefinedPos.toIntArray().length);
                        if (!abstractedPositions.contains(boxPos)) {
                            continue;
                        }
                        Context c = Context.create(abstracted, boxPos);
                        boolean info = computeInfo(innerDefinedTerm);
                        addDefinedContext(c, info, outerRes);
                    }
                }
            }
        }

        /**
         * Iteratively adds more elemets to the result if
         *  - we already know that defined symbols may occur in C's box
         *  - the lhs is an instance of C
         *  - the lhs contains a variable x below the hole-position of C
         *  - x occurs below a subterm s with defined root in the rhs
         *  Then the new context results from s by replacing defined subterms with variables and x with the box.
         */
        private void findFixedpointForDefinedContexts() {
            boolean changed;
            do {
                changed = false;
                Map<Context, Boolean> toAdd = new DefinedContextFixedPointStep(outerRes).run();
                Map<Context, Boolean> oldRes = new LinkedHashMap<>(outerRes);
                addDefinedContexts(toAdd, outerRes);
                changed = !oldRes.equals(outerRes);
            } while (changed);
        }


        private Set<FunctionSymbol> getReachable(Set<FunctionSymbol> fs, DependencyGraph<?> depGraph) {
            Set<Node<FunctionSymbol>> ns = depGraph.getNodes().stream().filter(x -> fs.contains(x.getObject())).collect(toSet());
            return union(depGraph.getNodes().stream().filter(x -> ns.stream().anyMatch(n -> depGraph.hasPath(n, x))).map(x -> x.getObject()).collect(toSet()), fs);
        }

        private class DefinedContextFixedPointStep {

            Map<Context, Boolean> innerRes = new LinkedHashMap<>();
            Map<Context, Boolean> definedContexts;

            DefinedContextFixedPointStep(Map<Context, Boolean> definedContexts) {
                this.definedContexts = new LinkedHashMap<>(definedContexts);
            }

            Map<Context, Boolean> run() {
                for (Rule r: trs.getRules()) {
                    inductiveStepForRule(r);
                }
                return innerRes;
            }

            void inductiveStepForRule(Rule r) {
                TRSFunctionApplication lhs = r.getLeft();
                for (TRSTerm lhsSub: lhs.getNonVariableSubTerms()) {
                    inductiveStepForSubterm(lhsSub, r.getRight());
                }
            }

            void inductiveStepForSubterm(TRSTerm lhsSub, TRSTerm rhs) {
                for (Entry<Context, Boolean> e: definedContexts.entrySet()) {
                    Context c = e.getKey();
                    new FixedPointStepForSingleDefinedContext(lhsSub, rhs, c).run();
                }
            }

            class FixedPointStepForSingleDefinedContext {

                TRSTerm lhsSub;
                TRSTerm rhs;
                Context c;
                TRSTerm cTerm;
                Map<TRSVariable, List<Position>> lhsSubVarPositions;
                Map<TRSVariable, List<Position>> rhsVarPositions;
                Set<TRSVariable> cTermVars;

                FixedPointStepForSingleDefinedContext(TRSTerm lhsSub, TRSTerm rhs, Context c) {
                    this.lhsSub = lhsSub;
                    this.rhs = rhs;
                    this.c = c;
                    this.cTerm = c.replace(hole);
                    this.lhsSubVarPositions = lhsSub.getVariablePositions();
                    this.rhsVarPositions = rhs.getVariablePositions();
                    this.cTermVars = cTerm.getVariables();
                }

                void run() {
                    for (TRSVariable x: lhsSubVarPositions.keySet()) {
                        induciveStepForVar(x);
                    }
                }

                void induciveStepForVar(TRSVariable x) {
                    List<Position> xPositions = lhsSubVarPositions.get(x);
                    for (Position xPos: xPositions) {
                        inductiveStepForVarPos(x, xPos);
                    }
                }

                void inductiveStepForVarPos(TRSVariable x, Position xPos) {
                    Position cPos = c.getPosition();
                    if (cPos.isIndependent(xPos)) {
                        return;
                    }
                    Position shorterPos = cPos.isPrefixOf(xPos) ? cPos : xPos;
                    TRSTerm xTerm = lhsSub.replaceAt(shorterPos, hole).renameVariables(cTermVars);
                    TRSTerm adaptedCTerm = cTerm.replaceAt(shorterPos, hole);
                    if (!adaptedCTerm.unifies(xTerm) || !rhsVarPositions.containsKey(x)) {
                        return;
                    }
                    for (Position rhsVarPos: rhsVarPositions.get(x)) {
                        inductiveStepForRhsVarPos(rhsVarPos);
                    }
                }

                void inductiveStepForRhsVarPos(Position rhsVarPos) {
                    for (Position rhsDefinedPos: rhsVarPos.getTruePrefixes()) {
                        TRSFunctionApplication s = (TRSFunctionApplication) rhs.getSubterm(rhsDefinedPos);
                        FunctionSymbol g = s.getRootSymbol();
                        if (!trs.isDefined(g)) {
                            continue;
                        }
                        inductiveStepForRhsSubterm(rhsVarPos, rhsDefinedPos, s);
                    }
                }

                void inductiveStepForRhsSubterm(Position rhsVarPos, Position rhsDefinedPos, TRSFunctionApplication rhsSub) {
                    TRSTerm abstracted = linearizeAndAbstractInnerOccurrencesOf(rhsSub, trs.getDefinedSymbols(), renamingCentral);
                    Set<Position> abstractedPositions = abstracted.getPositions();
                    Position boxPos = rhsVarPos.tail(rhsDefinedPos.toIntArray().length);
                    if (abstractedPositions.contains(boxPos)) {
                        addDefinedContext(Context.create(abstracted, boxPos), false, innerRes);
                    }
                }

            }

        }

    }

    private void addDefinedContexts(Map<Context, Boolean> src, Map<Context, Boolean> target) {
        for (Entry<Context, Boolean> e: src.entrySet()) {
            Context c = e.getKey();
            boolean info = e.getValue();
            addDefinedContext(c, info, target);
        }
    }

    private void addDefinedContext(Context c, boolean info, Map<Context, Boolean> target) {
        if (target.containsKey(c)) {
            boolean newInfo = target.get(c) || info;
            target.put(c, newInfo);
        } else {
            target.put(c, info);
        }
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder res = new StringBuilder();
        for (Context c: cachedRes.keySet()) {
            res.append(o.export(c.getAsTerm().export(o)));
            res.append(o.linebreak());
        }
        res.append(o.paragraph());
        if (cachedRes.values().contains(Boolean.TRUE)) {
            res.append(o.export("[] just represents basic- or constructor-terms in the following defined contexts:"));
            res.append(o.linebreak());
            for (Entry<Context, Boolean> e: cachedRes.entrySet()) {
                if (e.getValue()) {
                    res.append(o.export(e.getKey().getAsTerm().export(o)));
                    res.append(o.linebreak());
                }
            }
            res.append(o.paragraph());
        }
        return res.toString();
    }

}
