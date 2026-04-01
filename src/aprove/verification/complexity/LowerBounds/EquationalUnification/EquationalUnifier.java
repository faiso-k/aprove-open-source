package aprove.verification.complexity.LowerBounds.EquationalUnification;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.*;
import aprove.verification.complexity.LowerBounds.BasicStructures.Equation;
import aprove.verification.complexity.LowerBounds.EquationalUnification.EquationalUnificationRule.*;
import aprove.verification.complexity.LowerBounds.EquationalUnification.UnificationProblem.*;
import aprove.verification.complexity.LowerBounds.GeneratorEquations.*;
import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.complexity.LowerBounds.Util.Renaming.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class EquationalUnifier {

    private EquationalUnificationRule[] rules;
    private CollectionMap<FunctionSymbol, FunctionSymbol> eqSymbols = new CollectionMap<>();
    private RenamingCentral renamingCentral;

    public EquationalUnifier(Iterable<Equation> equationRules, RenamingCentral renamningCentral, TrsTypes types, TermGenerator termGenerator) {
        this.renamingCentral = renamningCentral;
        /*
         * Order of rules:
         * ATermIsVariable and EqualRootSymbols can result in Occur / Clash failures and hence should be applied first.
         * The remaining three rules are ordered according to their branching factor:
         * 1 for EqualTerms, 2 for UnifyModuloEquation, unbounded for UnifyPolynomials
         */
        this.rules = new EquationalUnificationRule[] {
                new ATermIsVariable(),
                new EqualRootSymbols(termGenerator),
                new EqualTerms(),
                new UnifyModuloEquation(equationRules, renamningCentral, types),
                new UnifyPolynomials(),
        };
        for (Equation r: equationRules) {
            FunctionSymbol leftRoot = r.getLeftRootSymbol();
            FunctionSymbol rightRoot = r.getRightRootSymbol();
            Collection<FunctionSymbol> value = this.eqSymbols.getNotNullAndAdd(leftRoot);
            value.add(rightRoot);
            value = this.eqSymbols.getNotNullAndAdd(rightRoot);
            value.add(leftRoot);
        }
    }

    /**
     * Try to apply one rule to the given unification problem.
     * @return A set of new unification problems, s.t. one of them can be solved instead of the old or null.
     */
    private Set<UnificationProblem> oneStep(UnificationProblem unificationProblem) throws AbortionException {
        // Make a working copy.
        UnificationProblem adjustedProblem = unificationProblem.clone();
        Optional<Set<Result>> res;
        try {
            res = this.applyOneRule(adjustedProblem);
        } catch (NoUnifierException e) {
            return null;
        }
        // If we were able to apply a rule, construct the new unification problems that will replace the current one.
        if (res.isPresent()) {
            Set<UnificationProblem> unificationProblems = new LinkedHashSet<>();
            if (res.get().isEmpty()) {
                unificationProblems.add(adjustedProblem);
            } else {
                for (Result r: res.get()) {
                    // First apply the substitution to the old pairs.
                    if (r.needsRefinement()) {
                        TRSSubstitution refinement = r.getRefinement();
                        adjustedProblem = adjustedProblem.clone();
                        for (Entry toSubstitute : adjustedProblem) {
                            toSubstitute.applySubstitution(refinement);
                        }
                    }
                    // Then add the new pairs.
                    if (r.getNewProblem().isPresent()) {
                        UnificationProblem toSolve = adjustedProblem.union(r.getNewProblem().get());
                        unificationProblems.add(toSolve);
                    } else {
                        unificationProblems.add(adjustedProblem);
                    }
                }
            }
            return unificationProblems;
        } else {
            return null;
        }
    }

    private Optional<Set<Result>> applyOneRule(UnificationProblem problem) throws NoUnifierException {
        for (EquationalUnificationRule rule : rules) {
            // For each rule, try to apply it.
            Iterator<Entry> it = problem.iterator();
            while (it.hasNext()) {
                Entry toUnify = it.next();
                TRSTerm s = toUnify.getS();
                TRSTerm t = toUnify.getT();
                Optional<Set<Result>> res = rule.apply(s, t, problem);
                // If we were able to apply the rule, we are done.
                if (res.isPresent()) {
                    it.remove();
                    return res;
                }
            }
        }
        return Optional.empty();
    }

    /** Try to solve one of the given unification problems. */
    private TRSSubstitution unify(Set<UnificationProblem> unificationProblems) throws AbortionException {
        boolean appliedRule;
        do {
            appliedRule = false;
            Set<UnificationProblem> toAdd = new LinkedHashSet<>();
            Iterator<UnificationProblem> unificationProblemIterator = unificationProblems.iterator();
            while (unificationProblemIterator.hasNext()) {
                UnificationProblem unificationProblem = unificationProblemIterator.next();
                Set<UnificationProblem> newUnificationProblems = this.oneStep(unificationProblem);
                unificationProblemIterator.remove();
                if (newUnificationProblems == null) {
                    TRSSubstitution result = unificationProblem.getSolution();
                    if (result != null) {
                        return result;
                    }
                } else {
                    appliedRule = true;
                    toAdd.addAll(newUnificationProblems);
                }
            }
            unificationProblems.addAll(toAdd);
        } while (appliedRule);
        return null;
    }

    public TRSSubstitution unify(TRSTerm s, TRSTerm t) throws AbortionException {
        UnificationProblem unificationProblem = new UnificationProblem(s, t);
        Set<UnificationProblem> unificationProblems = new LinkedHashSet<>();
        unificationProblems.add(unificationProblem);
        TRSSubstitution res = this.unify(unificationProblems);
//        System.err.println(s.toString() + " =? " + t + " --> " + res);
        return res;
    }

    public TRSSubstitution match(TRSTerm s, TRSTerm t) throws AbortionException {
        BidirectionalMap<TRSTerm, TRSTerm> replacementMap =
            this.renamingCentral.mapVariablesToFreshConstants(t.getVariables());
        TRSSubstitution unifier = this.unify(s, t.replaceAll(replacementMap.getLRMap()));
        if (unifier != null) {
            Map<TRSVariable, TRSTerm> res = new LinkedHashMap<>();
            for (Map.Entry<TRSVariable, ? extends TRSTerm> e : unifier.toMap().entrySet()) {
                res.put(e.getKey(), e.getValue().replaceAll(replacementMap.getRLMap()));
            }
            return TRSSubstitution.create(ImmutableCreator.create(res));
        } else {
            return null;
        }
    }

    public boolean matches(TRSTerm s, TRSTerm t) {
        return this.match(s, t) != null;
    }
}
