package aprove.verification.dpframework.BasicStructures.Unification;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 *
 * @author Matthias Sondermann
 * @version $Id$
 */
public class SemiUnificationSolutionExtraction implements Exportable {

    Set<Pair<TRSTerm, TRSTerm>> algoConstraints;

    Map<TRSVariable, TRSTerm> matcher;
    Set<Pair<TRSTerm, TRSTerm>> matchingConstraints;

    TRSSubstitution matchingSubst;
    FunctionSymbol phi;

    Map<TRSVariable, TRSTerm> semiunifier;
    TRSSubstitution semiunifyingSubst;

    TRSTerm term1;
    TRSTerm term2;

    /**
     * necessary for generating the semiunifier and the matcher
     */
    private FreshNameGenerator nameGen;

    public SemiUnificationSolutionExtraction(
        Pair<TRSTerm, TRSTerm> termPair,
        Set<Pair<TRSTerm, TRSTerm>> constraints,
        FunctionSymbol phi,
        FreshNameGenerator nameGen
    ) {
        this.term1 = termPair.x;
        this.term2 = termPair.y;
        this.phi = phi;
        this.algoConstraints = constraints;
        this.nameGen = nameGen;
    }

    /**
     * Be aware of the side effect this method makes. The algorithm should only work once, because after that
     * some variables might be initialized not correct.
     */
    @Override
    public String export(Export_Util eu) {
        StringBuilder s = new StringBuilder();
        Pair<TRSSubstitution, TRSSubstitution> subst = this.getSubstitutions();
        s.append("Matcher: " + subst.x);
        s.append("Semiunifier: " + subst.y);
        return s.toString();
    }

    public Pair<TRSSubstitution, TRSSubstitution> getSubstitutions() {
        this.semiunifier = new LinkedHashMap<TRSVariable, TRSTerm>();
        this.matcher = new LinkedHashMap<TRSVariable, TRSTerm>();
        this.matchingConstraints = new LinkedHashSet<Pair<TRSTerm, TRSTerm>>();
        // create emtpy substitution to return it in case of unification or matching
        TRSSubstitution emptySubst =
            TRSSubstitution.create(ImmutableCreator.create(java.util.Collections.<TRSVariable, TRSTerm>emptyMap()));

        // Try to match or to semiunify the given terms in order to be fast and to get a nice substitution
        // check if the terms match
        TRSSubstitution subst = this.term1.getMatcher(this.term2);
        if (subst != null) {
            // subst = this.simplifySubst(subst);
            return new Pair<TRSSubstitution, TRSSubstitution>(subst, emptySubst);
        }
        //check if the terms unify
        subst = this.term1.getMGU(this.term2);
        if (subst != null) {
            // subst = this.simplifySubst(subst);
            return new Pair<TRSSubstitution, TRSSubstitution>(emptySubst, subst);
        }

        // generate solution
        // System.out.println("Given algoConstraints:\n" + this.algoConstraints);
        this.algoConstraints = this.getFixPointOfConstraintSet(this.algoConstraints);
        // System.out.println("Optimized algoConstraints:\n" + this.algoConstraints);
        Pair<TRSTerm, TRSTerm> newTermPair = this.getTermsAfterApplyingSemiUnifier();
        this.matchingConstraints = this.getMatchingConstraints(newTermPair.x, newTermPair.y);
        // System.out.println("Matching constraints:\n" + matchingConstraints);
        this.matchingConstraints = this.getFixPointOfConstraintSet(this.matchingConstraints);
        // System.out.println("Optimzied matching constraints:\n" + this.matchingConstraints + "\n");
        this.getMatcher();
        this.matcher = this.simplifySubst(this.matcher);
        this.matchingSubst = TRSSubstitution.create(ImmutableCreator.create(this.matcher));
        this.getSemiunifier();
        this.semiunifier = this.simplifySubst(this.semiunifier);
        this.semiunifyingSubst = TRSSubstitution.create(ImmutableCreator.create(this.semiunifier));

        Pair<TRSSubstitution, TRSSubstitution> substPair =
            new Pair<TRSSubstitution, TRSSubstitution>(this.matchingSubst, this.semiunifyingSubst);

        // check if the substitutions are really a matcher and a semiunifier which make the terms equal
        if (Globals.useAssertions) {
            assert (this.checkPropernessOfSubstitutions(substPair));
        } else {
            if (!this.checkPropernessOfSubstitutions(substPair)) {
                throw new RuntimeException("internal error in semiunification");
            }
        }
        return substPair;
    }

    /**
     * Applies <code>subst</code> to <code>term</code> as many times as <code>term</code> has phis in front -1.
     * The -1 is because of possibility that the right side of the matching constraint is of the form f(...)
     * so that the last matching would be now trivial matching.
     */
    private TRSTerm applyMatchingLeft(TRSTerm termParam, TRSSubstitution subst) {
        TRSTerm term = termParam;
        int numberOfMatchings = PhiTermFunctions.countPhisInFront(term, this.phi);
        term = PhiTermFunctions.removePhisInFront(term, this.phi);
        for (int i = 0; i < numberOfMatchings - 1; i++) {
            term = term.applySubstitution(subst);
        }
        return term;
    }

    /**
     * Applies <code>subst</code> to <code>term</code> as many times as <code>term</code> has phis in front.
     */
    private TRSTerm applyMatchingRight(TRSTerm termParam, TRSSubstitution subst) {
        TRSTerm term = termParam;
        if (PhiTermFunctions.termIsPhiFunction(term, this.phi)) {
            int numberOfMatchings = PhiTermFunctions.countPhisInFront(term, this.phi);
            term = PhiTermFunctions.removePhisInFront(term, this.phi);
            for (int i = 0; i < numberOfMatchings; i++) {
                term = term.applySubstitution(subst);
            }
            return term;
        }
        TRSFunctionApplication f = (TRSFunctionApplication)term;
        ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(f.getRootSymbol().getArity());
        for (TRSTerm child : f.getArguments()) {
            args.add(this.applyMatchingRight(child, subst));
        }
        return TRSTerm.createFunctionApplication(f.getRootSymbol(), ImmutableCreator.create(args));
    }

    /**
     * Checks if the two terms are equal after applying the two substitutions
     */
    private boolean checkPropernessOfSubstitutions(Pair<TRSSubstitution, TRSSubstitution> subst) {
        TRSSubstitution matcherVar = subst.x;
        TRSSubstitution semiunifierVar = subst.y;
        TRSTerm newTerm1 = (this.term1.applySubstitution(semiunifierVar)).applySubstitution(matcherVar);
        TRSTerm newTerm2 = this.term2.applySubstitution(semiunifierVar);
        boolean isProper = newTerm1.equals(newTerm2);
        // give some information in case of failure
        if (!isProper) {
            System.err.println(
                "The semiunification algorithm could show that the terms\n"
                + this.term1
                + " and\n"
                + this.term2
                + "\nsemiunify, but the resulting matcher and semiunifier are not correct!"
            );
            System.err.println("\nMatcher " + matcherVar);
            System.err.println("Semiunifier " + semiunifierVar);
            System.err.println("\nApplying these substitutions leads to the following terms:");
            System.err.println(newTerm1);
            System.err.println(newTerm2);
        }
        return isProper;
    }

    /**
     * Constructs the phi terms out of the links given in the dag.
     * @return A term of the form phi^n(term) where n=numberOfPhis and all phis are pushed as far as possible.
     */
    private TRSTerm constructPhiTerm(TRSTerm term, int numberOfPhis) {
        TRSTerm retTerm = term;
        ArrayList<TRSTerm> phiArgs;
        for (int i = 0; i < numberOfPhis; i++) {
            phiArgs = new ArrayList<TRSTerm>(1);
            phiArgs.add(retTerm);
            retTerm = TRSTerm.createFunctionApplication(this.phi, ImmutableCreator.create(phiArgs));
        }
        return PhiTermFunctions.push(retTerm, this.phi);
    }

    private Set<Pair<TRSTerm, TRSTerm>> getFixPointOfConstraintSet(Set<Pair<TRSTerm, TRSTerm>> setOfTermPairs) {
        boolean change = true;
        List<Pair<TRSTerm, TRSTerm>> d = new ArrayList<Pair<TRSTerm, TRSTerm>>(setOfTermPairs);
        //System.out.println("d: " + d);
        while (change) {
            change = false;
            for (int i = 0; i < d.size(); i++) {
                Pair<TRSTerm, TRSTerm> actPair = d.get(i);
                for (int j = 0; j < d.size(); j++) {
                    if (i == j) {
                        continue;
                    }
                    Pair<TRSTerm, TRSTerm> compPair = d.get(j);
                    //System.out.println("act " + actPair + " at " + i);
                    //System.out.println("com " + compPair + " at " + j);
                    TRSTerm newX = actPair.x;//.replaceAll(compPair.x,compPair.y);
                    TRSTerm newY = actPair.y.replaceAll(compPair.x, compPair.y);
                    if (!newX.equals(actPair.x) || !newY.equals(actPair.y)) {
                        d.set(i, this.orientatePhiTerms(newX, newY));
                        //System.out.println("new d at " + i + " : " + d.get(i));
                        change = true;
                    }
                    //System.out.println(d);
                }
            }
        }
        return this.removeUselessStuff(d);
    }

    private void getMatcher() {
        for (Pair<TRSTerm, TRSTerm> actPair : this.matchingConstraints) {
            if (!actPair.x.isVariable()) {
                this.matcher.putAll(this.getTrivialMatchers(actPair));
            }
            //constraints of the form x = t have to be added to the semiunifier
            else {
                this.semiunifier.put((TRSVariable)actPair.x, actPair.y);
            }
        }
        for (Pair<TRSTerm, TRSTerm> actPair : this.matchingConstraints) {
            if (!actPair.x.isVariable()) {
                this.matcher.putAll(this.getNonTrivialMatchers(actPair));
            }
        }
    }

    /**
     * Computes all constraints to make the two terms equal after applying the substitution which was directly generated
     * after the boolean procedure semiUnify().
     */
    private Set<Pair<TRSTerm, TRSTerm>> getMatchingConstraints(TRSTerm term1, TRSTerm term2) {
        Set<Pair<TRSTerm, TRSTerm>> constraints = new LinkedHashSet<Pair<TRSTerm, TRSTerm>>();
        // this would be a useless constraint
        if (term1.equals(term2)) {
            return constraints;
        }
        // check if a side is a phi-term
        if (PhiTermFunctions.termIsPhiFunction(term1, this.phi)) {
            if (PhiTermFunctions.termIsPhiFunction(term2, this.phi)) {
                // case: phi^n(x) = phi^m()
                int p1 = PhiTermFunctions.countPhisInFront(term1, this.phi);
                int p2 = PhiTermFunctions.countPhisInFront(term2, this.phi);
                if (p1 >= p2) {
                    constraints.add(new Pair<TRSTerm, TRSTerm>(term1, term2));
                    return constraints;
                } else {
                    constraints.add(new Pair<TRSTerm, TRSTerm>(term2, term1));
                    return constraints;
                }
            }
            // case: phi^n(x) = f(...)
            constraints.add(new Pair<TRSTerm, TRSTerm>(term1, term2));
            return constraints;
        } else if (PhiTermFunctions.termIsPhiFunction(term2, this.phi)) {
            // case:  f(...) = phi^n(x) -> invert the sides
            constraints.add(new Pair<TRSTerm, TRSTerm>(term2, term1));
            return constraints;
        } else {
            // case: f(...) = f(...) -> push the obligation to the children of both sides
            TRSFunctionApplication f1 = (TRSFunctionApplication)term1;
            TRSFunctionApplication f2 = (TRSFunctionApplication)term2;
            List<? extends TRSTerm> childrenOfF1 = f1.getArguments();
            List<? extends TRSTerm> childrenOfF2 = f2.getArguments();
            for (int i = 0; i < childrenOfF1.size(); i++) {
                constraints.addAll(this.getMatchingConstraints(childrenOfF1.get(i), childrenOfF2.get(i)));
            }
        }
        return constraints;
    }

    /**
     * Compute the rest of the matchers out of matching constraints of the form phi^n(var) = f(t_1,...,t_n)
     */
    private Map<TRSVariable, TRSTerm> getNonTrivialMatchers(Pair<TRSTerm, TRSTerm> termPair) {
        Map<TRSVariable, TRSTerm> nonTrivMatcher = new LinkedHashMap<TRSVariable, TRSTerm>();
        TRSSubstitution subst = TRSSubstitution.create(ImmutableCreator.create(this.matcher));
        TRSTerm term1Var = this.applyMatchingLeft(termPair.x, subst);
        TRSTerm term2Var = this.applyMatchingRight(termPair.y, subst);
        nonTrivMatcher.put(PhiTermFunctions.getVarOfPhiFunction(term1Var), term2Var);
        return nonTrivMatcher;
    }

    private void getSemiunifier() {
        for (Map.Entry<TRSVariable, TRSTerm> actEntry : this.semiunifier.entrySet()) {
            this.semiunifier.put(actEntry.getKey(), this.applyMatchingRight(actEntry.getValue(), this.matchingSubst));
        }
    }

    private TRSSubstitution getTempSemiunifier() {
        for (Pair<TRSTerm, TRSTerm> actPair : this.algoConstraints) {
            if (actPair.x.isVariable()) {
                this.semiunifier.put((TRSVariable)actPair.x, actPair.y);
            }
        }
        return TRSSubstitution.create(ImmutableCreator.create(this.semiunifier));
    }

    private Pair<TRSTerm, TRSTerm> getTermsAfterApplyingSemiUnifier() {
        TRSTerm newTerm1;
        TRSTerm newTerm2;
        TRSSubstitution tempSemiunifier = this.getTempSemiunifier();
        newTerm1 = this.term1.applySubstitution(tempSemiunifier);
        newTerm2 = this.term2.applySubstitution(tempSemiunifier);
        // apply phi to term1
        newTerm1 = this.constructPhiTerm(newTerm1, 1);
        return new Pair<TRSTerm, TRSTerm>(newTerm1, newTerm2);
    }

    /**
     * Generates all trivial matchers that can be computed without applying any substitution to the terms.
     * Because of that all trivial matchers are of the form [var^n/var^{n+1}]
     */
    private Map<TRSVariable, TRSTerm> getTrivialMatchers(Pair<TRSTerm, TRSTerm> termPair) {
        Map<TRSVariable, TRSTerm> trivialMatcher = new LinkedHashMap<TRSVariable, TRSTerm>();
        TRSTerm term1Var = termPair.x;
        TRSTerm term2Var = termPair.y;
        if (term1Var.equals(term2Var)) {
            return trivialMatcher;
        }
        int numberOfMatchings = PhiTermFunctions.countPhisInFront(term1Var, this.phi);
        TRSVariable actualVar = PhiTermFunctions.getVarOfPhiFunction(term1Var);
        if (numberOfMatchings == 1) {
            return trivialMatcher;
        }
        // generate a new name for the new variable
        for (int i = 0; i < numberOfMatchings - 1; i++) {
            String newName = this.nameGen.getFreshName(actualVar.getName(), false);
            TRSVariable newVar = TRSTerm.createVariable(newName);
            trivialMatcher.put(actualVar, newVar);
            actualVar = newVar;
        }
        return trivialMatcher;
    }

    private Pair<TRSTerm, TRSTerm> orientatePhiTerms(TRSTerm term1Param, TRSTerm term2Param) {
        TRSTerm term1Var = PhiTermFunctions.push(term1Param, this.phi);
        TRSTerm term2Var = PhiTermFunctions.push(term2Param, this.phi);
        // System.out.println(term1+  " and " + term2);
        if (PhiTermFunctions.termIsPhiFunction(term1Var, this.phi)) {
            if (PhiTermFunctions.termIsPhiFunction(term2Var, this.phi)) {
                int p1 = PhiTermFunctions.countPhisInFront(term1Var, this.phi);
                int p2 = PhiTermFunctions.countPhisInFront(term2Var, this.phi);
                if (p1 >= p2) {
                    return new Pair<TRSTerm, TRSTerm>(term1Var, term2Var);
                } else {
                    return new Pair<TRSTerm, TRSTerm>(term2Var, term1Var);
                }
            } else {
                return new Pair<TRSTerm, TRSTerm>(term1Var, term2Var);
            }
        } else {
            if (PhiTermFunctions.termIsPhiFunction(term2Var, this.phi)) {
                return new Pair<TRSTerm, TRSTerm>(term2Var, term1Var);
            }
        }
        // pair is of the form f(t) = f(t)
        return new Pair<TRSTerm, TRSTerm>(term1Var, term2Var);
    }

    /**
     * Removes every useless item out of the collection, e.g. constraints of the form t = t.
     * @return A set containing all usefull elements of <code>col</code>
     */
    private Set<Pair<TRSTerm, TRSTerm>> removeUselessStuff(Collection<Pair<TRSTerm, TRSTerm>> col) {
        Set<Pair<TRSTerm, TRSTerm>> retCol = new LinkedHashSet<Pair<TRSTerm, TRSTerm>>();
        for (Pair<TRSTerm, TRSTerm> pair : col) {
            if (!pair.x.equals(pair.y)) {
                retCol.add(pair);
            }
        }
        return retCol;
    }

    /**
     * Removes every x/x from the mapping.
     */
    private Map<TRSVariable, TRSTerm> simplifySubst(Map<TRSVariable, TRSTerm> subst) {
        Map<TRSVariable, TRSTerm> dummyMap = new LinkedHashMap<TRSVariable, TRSTerm>();
        for (Map.Entry<TRSVariable, TRSTerm> e : subst.entrySet()) {
            TRSVariable var = e.getKey();
            TRSTerm value = e.getValue();
            if (!var.equals(value)) {
                dummyMap.put(var, value);
            }
        }
        return dummyMap;
    }

    private TRSSubstitution simplifySubst(TRSSubstitution subst) {
        Map<TRSVariable, TRSTerm> retMap = new LinkedHashMap<TRSVariable, TRSTerm>();
        for (TRSVariable key : subst.getDomain()) {
            TRSTerm value = key.applySubstitution(subst);
            if (!key.equals(value)) {
                retMap.put(key, value);
            }
        }
        return TRSSubstitution.create(ImmutableCreator.create(retMap));
    }

}
