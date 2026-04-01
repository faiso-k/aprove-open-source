/*
 * Created on 17.03.2005
 */
package aprove.verification.dpframework.BasicStructures.AFSPrecalculation;


import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;

/**
 * A YnmPET is a partially evaluated Term w.r.t. some YNM Interpretation.
 * It is the same as a PET with the difference, that
 * in YnmPET we can en/disable each argument seperately.
 * The use of a YnmPET is to determine which rules will be usable w.r.t. the given
 * interpretation.
 *
 * @author thiemann
 */
public class YnmPET {

    private final static YNM YES = YNM.YES;
    private final static YNM MAYBE = YNM.MAYBE;

    private final Map<Integer, YnmPET> arguments; // a mapping from positions (which may result in new rules) to corresponding PETs
    private final Set<? extends GeneralizedRule> mustRules; // the rules that must be oriented due to this pet (regardless of specialization)
    private final Set<? extends GeneralizedRule> mayRules; // the rules that may (and not must) be oriented due to this pet (depending on specialization)
    public final FunctionSymbol f; // the top-most functionSymbol


    private YnmPET(FunctionSymbol f, Map<Integer, YnmPET> arguments, Set<? extends GeneralizedRule> mustRules, Set<? extends GeneralizedRule> mayRules) {
        this.arguments = arguments;
        this.mustRules = mustRules;
        this.mayRules = mayRules;
        this.f = f;
    }

    /**
     * creates a term for the given set of rules
     * If there are no rules possible, null is returned, otherwise the pet.
     * @param term
     * @param rules
     * @param lhss the lhss of those rules that we need for capping
     * @return
     */
    private static YnmPET create(TRSTerm term, Set<? extends GeneralizedRule> rules, final Map<FunctionSymbol, Set<TRSFunctionApplication>> lhss) {
        if (rules.isEmpty()) {
            return null;
        }
        if (term.isVariable()) {
            return null;
        }

        // determine which rules must be oriented due to top-level
        Set<GeneralizedRule> mustRules = new LinkedHashSet<GeneralizedRule>();
        Set<GeneralizedRule> remainingRules = new LinkedHashSet<GeneralizedRule>();
        TRSFunctionApplication fterm = (TRSFunctionApplication) term;
        term = fterm.tcapNe(lhss);
        for (GeneralizedRule rule : rules) {
            if (term.unifies(rule.getLhsInStandardRepresentation())) {
                mustRules.add(rule);
            } else {
                remainingRules.add(rule);
            }
        }


        // now look at argument level
        Set<GeneralizedRule> mayRules = new LinkedHashSet<GeneralizedRule>();
        int i = 0;
        Map<Integer, YnmPET> argumentMap = new HashMap<Integer, YnmPET>();
        for (TRSTerm arg : fterm.getArguments()) {
            YnmPET argPET = YnmPET.create(arg, remainingRules, lhss);
            if (argPET != null) {
                // we have some rules in argPET (otherwise it would be null!);
                mayRules.addAll(argPET.mustRules);
                mayRules.addAll(argPET.mayRules);
                argumentMap.put(i, argPET);
            }
            i++;
        }

        if (mayRules.isEmpty() && mustRules.isEmpty()) {
            return null;
        } else {
            return new YnmPET(fterm.getRootSymbol(), argumentMap, mustRules, mayRules);
        }
    }


    /**
     * takes the rules that may potentially be usable
     * and a set for storing new usable rules that are activated by this PET.
     * Returns the set of remaining pets that may be examined further
     * and that do need further specialization on top-level
     * @param interpretation - the current interpretation
     * @param remainingUsable - those rules that remain to become usable.
     *    We delete all rules from this set, that we active and put them into the newUsable set.
     * @param newUsable - the set where to insert the newly activated rules
     */
    public List<YnmPET> simplify(Map<FunctionSymbol, YNM[]> interpretation, Set<? extends GeneralizedRule> remainingUsable, Set<GeneralizedRule> newUsable) {

        // let us first delete some new rules
        for (GeneralizedRule must : this.mustRules) {
            if (remainingUsable.remove(must)) {
                newUsable.add(must);
            }
        }

        // let us look whether we have to look into the arguments
        boolean lookArgs = false;
        for (GeneralizedRule may : this.mayRules) {
            if (remainingUsable.contains(may)) {
                lookArgs = true;
                break;
            }
        }


        List<YnmPET> newPets = new LinkedList<YnmPET>();


        if (!lookArgs) {
            // there is nothing to do here any more
            return newPets;
        }

        // okay, so here we know that there are some rules in the arguments
        // that want to be activated

        // let us look whether we know the exact arguments
        YNM[] inter = interpretation.get(this.f);


        if (inter == null) { // perhaps this should not happen!
            // we must abort here, sorry no f given!
            YnmPET newPet = new YnmPET(this.f, this.arguments, new LinkedHashSet<Rule>(), this.mayRules);
            newPets.add(newPet);
            return newPets;
        }

        // perhaps, if we have no must rules, then first check
        // whether they are YES/NO args to determine progress?

        // okay, let us examine our arguments
        Map<Integer, YnmPET> newArgMap = new LinkedHashMap<Integer, YnmPET>();
        Set<GeneralizedRule> newMayRules = new LinkedHashSet<GeneralizedRule>();

        for (Map.Entry<Integer, YnmPET> entry : this.arguments.entrySet()) {
            Integer i = entry.getKey();
            YnmPET arg = entry.getValue();
            YNM status = inter[i.intValue()];
            if (status == YnmPET.YES) {
                // this argument is relevant
                newPets.addAll(arg.simplify(interpretation, remainingUsable, newUsable));
            } else if (status == YnmPET.MAYBE) {
                Set<GeneralizedRule> argRules;
                argRules = new LinkedHashSet<GeneralizedRule>(arg.mustRules);
                argRules.addAll(arg.mayRules);
                argRules.retainAll(remainingUsable);
                if (!argRules.isEmpty()) {
                    newArgMap.put(i, arg);
                    newMayRules.addAll(argRules);
                }
            }
        }

        // this itself is not needed in the newPets any more
        // but we have to do something for our maybe-args
        if (!newArgMap.isEmpty()) {
            // we have to create some YnmPETs for our Maybe-Args
            // however, we do not need our must rules any more!
            YnmPET newPet = new YnmPET(this.f, newArgMap, new LinkedHashSet<Rule>(), newMayRules);
            newPets.add(newPet);
        }

        // so we can return the newPets of the arguments
        return newPets;
    }

    /**
     * checks whether this PET does not provide new usable rules
     * under the assumption that it was simplified after the last
     * change in the interpretation
     */
    public boolean canBeDeletedAfterSimplification(Set<? extends GeneralizedRule> remainingUsable) {
        /*
         * with the above assumption we only have to check for new
         * rules in may, but not in must!!
         */
        for (GeneralizedRule may : this.mayRules) {
            if (remainingUsable.contains(may)) {
                return false;
            }
        }
        return true;
    }

    /**
     * throws out all unnecessary PETs of the given collection.
     * Requirement: all PETs in the collection have been simplified
     * after the last change in the interpretation
     * @param pets
     * @return
     */
    public static void deleteAfterSimplification(Collection<YnmPET> pets, Set<? extends GeneralizedRule> remainingUsable) {
        Iterator<YnmPET> petIt = pets.iterator();
        while (petIt.hasNext()) {
            YnmPET pet = petIt.next();
            if (pet.canBeDeletedAfterSimplification(remainingUsable)) {
                petIt.remove();
            }
        }
    }


    @Override
    public boolean equals(Object other) {
        throw new RuntimeException("PETs may not be compared");
    }

    @Override
    public int hashCode() {
        throw new RuntimeException("Pets do not possess a hashCode");
    }

    @Override
    public String toString() {
        String s = "";
        s += "FunctionSymbol: " + this.f+"\n";

        s += "Must:\n";
        for (GeneralizedRule rule : this.mustRules) {
            s += "  "+rule+"\n";
        }
        s += "May:\n";
        for (GeneralizedRule rule : this.mayRules) {
            s += "  "+rule+"\n";
        }
        return s;
    }

    public static class PETCreator {

        private final Set<? extends GeneralizedRule> possibleUsableRules;
        private final Map<FunctionSymbol, Set<TRSFunctionApplication>> lhss; // have to be STANDARD RENUMBERED

        /**
         * @param usableRules the usable rules
         */
        public PETCreator(Set<? extends GeneralizedRule> usableRules) {
            this.possibleUsableRules = usableRules;
            this.lhss = new LinkedHashMap<FunctionSymbol, Set<TRSFunctionApplication>>();
            for (GeneralizedRule rule : usableRules) {
                FunctionSymbol f = rule.getRootSymbol();
                Set<TRSFunctionApplication> fLhss = this.lhss.get(f);
                if (fLhss == null) {
                    fLhss = new LinkedHashSet<TRSFunctionApplication>();
                    this.lhss.put(f, fLhss);
                }
                fLhss.add(rule.getLhsInStandardRepresentation());
            }
        }

        public YnmPET create(TRSTerm term) {
            return YnmPET.create(term, this.possibleUsableRules, this.lhss);
        }

    }


}
