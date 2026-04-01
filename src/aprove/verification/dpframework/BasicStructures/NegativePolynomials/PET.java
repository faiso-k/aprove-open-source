/*
 * Created on 17.03.2005
 */
package aprove.verification.dpframework.BasicStructures.NegativePolynomials;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * A PET is a partially evaluated Term w.r.t. some Polynomial Interpretation.
 * The use of a PET is to determine which rules will be usable w.r.t. the given
 * interpretation.
 *
 * @author thiemann
 */
public class PET {

    private final Map<Integer, PET> arguments; // a mapping from positions (which may result in new rules) to corresponding PETs
    private final Set<Rule> mustRules; // the rules that must be oriented due to this pet (regardless of specialization)
    private final Set<Rule> mayRules; // the rules that may (and not must) be oriented due to this pet (depending on specialization)
    public final FunctionSymbol f; // the top-most functionSymbol
                                    // null, if may=empty (no specialization needed)

//    private final int hashCode;

    private PET(FunctionSymbol f, Map<Integer, PET> arguments, Set<Rule> mustRules, Set<Rule> mayRules) {
        this.arguments = arguments;
        this.mustRules = mustRules;
        this.mayRules = mayRules;
        this.f = mayRules.isEmpty() ? null : f;
//        this.hashCode = arguments.hashCode()*430920391+mustRules.hashCode()*920329009+90782911;
    }

    /**
     * creates a term for the given set of rules
     * If there are no rules possible, null is returned, otherwise the pet.
     * @param term
     * @param rules
     * @param lhss the lhss of those rules that we need for capping
     * @return
     */
    private static PET create(TRSTerm term, Set<Rule> rules, final Map<FunctionSymbol, Set<TRSFunctionApplication>> lhss) {
        if (rules.isEmpty()) {
            return null;
        }
        if (term.isVariable()) {
            return null;
        }

        // determine which rules must be oriented due to top-level
        Set<Rule> mustRules = new LinkedHashSet<Rule>();
        Set<Rule> remainingRules = new LinkedHashSet<Rule>();
        TRSFunctionApplication fterm = (TRSFunctionApplication) term;
        term = fterm.tcapNe(lhss);
        for (Rule rule : rules) {
            if (term.unifies(rule.getLhsInStandardRepresentation())) {
                mustRules.add(rule);
            } else {
                remainingRules.add(rule);
            }
        }


        // now look at argument level
        Set<Rule> mayRules = new LinkedHashSet<Rule>();
        int i = 0;
        Map<Integer, PET> argumentMap = new HashMap<Integer, PET>();
        for (TRSTerm arg : fterm.getArguments()) {
            i++;
            PET argPET = PET.create(arg, remainingRules, lhss);
            if (argPET != null) {
                // we have some rules in argPET (otherwise it would be null!);
                mayRules.addAll(argPET.mustRules);
                mayRules.addAll(argPET.mayRules);
                argumentMap.put(i, argPET);
            }
        }

        if (mayRules.isEmpty() && mustRules.isEmpty()) {
            return null;
        } else {
            return new PET(fterm.getRootSymbol(), argumentMap, mustRules, mayRules);
        }
    }


    /**
     * takes the rules that may potentially be usable
     * and a set for new usable rules that are activated by this PET.
     * Returns the set of remaining pets that may be examined further
     * and that do need further specialization on top-level
     * @param interpretation - the current interpretation
     * @param remainingUsable - those rules that remain to become usable.
     *    We delete all rules from this set, that we active and put them into the newUsable set.
     * @param newUsable - the set where to insert the newly activated rules
     */
    public List<PET> simplify(Map<FunctionSymbol, int[]> interpretation, Set<Rule> remainingUsable, Set<Rule> newUsable) {

        // let us first delete some new rules
        for (Rule must : this.mustRules) {
            if (remainingUsable.remove(must)) {
                newUsable.add(must);
            }
        }

        // let us look whether we have to look into the arguments
        boolean lookArgs = false;
        for (Rule may : this.mayRules) {
            if (remainingUsable.contains(may)) {
                lookArgs = true;
                break;
            }
        }


        List<PET> newPets = new LinkedList<PET>();


        if (!lookArgs) {
            // there is nothing to do here any more
            return newPets;
        }

        // okay, so here we know that there are some rules in the arguments
        // that want to be activated

        // let us look whether we know the exact arguments
        int[] inter = interpretation.get(this.f);


        if (inter == null) {
            // we must abort here, sorry no f given!
            newPets.add(this);
            return newPets;
        }

        // okay, let us examine our arguments
        for (Map.Entry<Integer, PET> entry : this.arguments.entrySet()) {
            int i = entry.getKey().intValue();
            if (inter[i] != 0) {
                // this argument is relevant
                newPets.addAll(entry.getValue().simplify(interpretation, remainingUsable, newUsable));
            }
        }

        // this itself is not needed in the newPets any more
        // so we can return the newPets of the arguments
        return newPets;
    }

    /**
     * checks whether this PET does not provide new usable rules
     * under the assumption that it was simplified after the last
     * change in the interpretation
     */
    public boolean canBeDeletedAfterSimplification(Set<Rule> remainingUsable) {
        /*
         * with the above assumption we only have to check for new
         * rules in may, but not in must!!
         */
        for (Rule may : this.mayRules) {
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
    public static void deleteAfterSimplification(Collection<PET> pets, Set<Rule> remainingUsable) {
        Iterator<PET> petIt = pets.iterator();
        while (petIt.hasNext()) {
            PET pet = petIt.next();
            if (pet.canBeDeletedAfterSimplification(remainingUsable)) {
                petIt.remove();
            }
        }
    }


    @Override
    public boolean equals(Object other) {
        throw new RuntimeException("PETs may not be compared");
//        if (other instanceof PET) {
//            PET oPet = (PET) other;
//            if (this.hashCode() == oPet.hashCode() && this.mustRules.equals(oPet.mustRules)) {
//                return this.arguments.equals(oPet.arguments);
//            }
//        }
//        return false;
    }

    @Override
    public int hashCode() {
        throw new RuntimeException("Pets do not possess a hashCode");
//        return this.hashCode;
    }

    @Override
    public String toString() {
        String s = "";
        s += "FunctionSymbol: " + this.f+"\n";

        s += "Must:\n";
        for (Rule rule : this.mustRules) {
            s += "  "+rule+"\n";
        }
        s += "May:\n";
        for (Rule rule : this.mayRules) {
            s += "  "+rule+"\n";
        }
        return s;
    }

    public static class PETCreator {

        private final Set<Rule> possibleUsableRules;
        private final Map<FunctionSymbol, Set<TRSFunctionApplication>> lhss; // have to be STANDARD RENUMBERED

        public PETCreator(Set<Rule> usableRules) {
            this.possibleUsableRules = usableRules;
            this.lhss = new HashMap<FunctionSymbol, Set<TRSFunctionApplication>>();
            for (Rule rule : usableRules) {
                FunctionSymbol f = rule.getRootSymbol();
                Set<TRSFunctionApplication> fLhss = this.lhss.get(f);
                if (fLhss == null) {
                        fLhss = new LinkedHashSet<TRSFunctionApplication>();
                        this.lhss.put(f, fLhss);
                }
                fLhss.add(rule.getLhsInStandardRepresentation());
            }
        }

        public PET create(TRSTerm term) {
            return PET.create(term, this.possibleUsableRules, this.lhss);
        }

    }


}
