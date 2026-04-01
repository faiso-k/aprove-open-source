/*
 * Created on 17.03.2005
 */
package aprove.verification.dpframework.BasicStructures.NegativePolynomials;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.PiDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class DynamicNegPOLOSolver implements NegPOLOSolver {

    static Logger log = Logger.getLogger("aprove.verification.theoremprover.TerminationVerifier.UsableRules");

    private final static YNM YES = YNM.YES;
    private final static YNM NO = YNM.NO;
    private final static YNM MAYBE = YNM.MAYBE;

    /*
     * for timing
     */
    private static final int STATES_PER_CHECK = 500;
    private final Abortion clock;
    private int ticks;


    public final int range;
    public final int restriction;

    public Map<Rule, Pair<PEP,PET>> infoMap;
    // in this map we recompute for each rule
    // its constraint (the PEP) and
    // its activation term (the PET)
    // possible improvements: icap(s) instead of tcap for
    // innermost constraint solving

    private Set<Rule> orientedRules;

    private boolean active;


    /**
     * creates a new NegPOLOSolver with the given coefficient range.
     * It may only be used with one Aborter, hence it cannot be used
     * concurrently!
     * However, creation of a NegPOLOSolver is cheap!
     * @param range
     * @param restriction - a negative value means no restriction.
     *   Otherwise the solver only searches for interpretations where
     *   for each function symbol at most restriction many arguments
     *   obtain a non-zero coefficient
     */
    public DynamicNegPOLOSolver(int range, int restriction, boolean active, Abortion aborter) {
        if (range == 0) {
            throw new RuntimeException("Invalid Range: "+range);
        }
        this.restriction = restriction < 0 ? -1 : restriction;
        this.range = range;
        this.clock = aborter;
        this.active = active;
    }

    /**
     * tries to give an Interpretation that solves the constraints arising from the qdp
     * additionally the set of oriented rules is returned
     * @param cs - must not be null
     * @return null - if no solution was found, a solution, otherwise.
     * @throws AbortionException
     */
    @Override
    public Pair<NegPolyOrder, Set<Rule>> solve(QDPProblem qdp, boolean allStrict) throws AbortionException {
        Set<Rule> dps = qdp.getP();
        Set<Rule> usableRules = qdp.getUsableRules();
        return this.solve(dps, usableRules, allStrict);
    }
    /**
     * tries to give an Interpretation that solves the constraints arising from the qdp
     * additionally the set of oriented rules is returned
     * @param cs - must not be null
     * @return null - if no solution was found, a solution, otherwise.
     * @throws AbortionException
     */
    @Override
    public NegPolyOrder solve(Set<Rule> P, Map<Rule, QActiveCondition> active, boolean allStrict) throws AbortionException {
        Set<Rule> R = active.keySet();
        Pair<NegPolyOrder, Set<Rule>> result =  this.solve(P, R, allStrict);
        if (result != null) {
            if (Globals.useAssertions) {
                assert(active.keySet().containsAll(result.y));
            }
            return result.x;
        }
        return null;
    }
    /**
     * tries to give an Interpretation that solves the constraints arising from the qdp
     * additionally the set of oriented rules is returned
     * @param cs - must not be null
     * @return null - if no solution was found, a solution, otherwise.
     * @throws AbortionException
     */
    @Override
    public Pair<NegPolyOrder, Set<GeneralizedRule>> solve(PiDPProblem pidp, boolean allStrict) throws AbortionException {
        Afs afs = pidp.getPi();
        Set<GeneralizedRule> dps = pidp.getP();
        Set<Rule> newDps = new LinkedHashSet<Rule>();
        Set<GeneralizedRule> usableRules = pidp.getUsableRules();
        Set<Rule> newUsableRules = new LinkedHashSet<Rule>();
        Map<GeneralizedRule,Rule> gen2rules = new LinkedHashMap<GeneralizedRule,Rule>();
        for (GeneralizedRule dp : dps) {
            Rule newDp = Rule.fromGeneralizedRule(afs.filterRule(dp));
            newDps.add(newDp);
            //gen2rules.put(dp, newDp);
        }
        for (GeneralizedRule rule : usableRules) {
            Rule newRule = Rule.fromGeneralizedRule(afs.filterRule(rule));
            newUsableRules.add(newRule);
            gen2rules.put(rule, newRule);
        }
        Pair<NegPolyOrder, Set<Rule>> solution = this.solve(newDps, newUsableRules, allStrict);
        if (solution == null) {
            return null;
        }
        Set<GeneralizedRule> orientedRules = new LinkedHashSet<GeneralizedRule>();
        for (Map.Entry<GeneralizedRule, Rule> entry : gen2rules.entrySet()) {
            if (solution.y.contains(entry.getValue())) {
                orientedRules.add(entry.getKey());
            }
        }
        return new Pair<NegPolyOrder, Set<GeneralizedRule>>(solution.x, orientedRules);
    }
    /**
     * tries to give an Interpretation that solves the constraints arising from the qdp
     * additionally the set of oriented rules is returned
     * @param cs - must not be null
     * @return null - if no solution was found, a solution, otherwise.
     * @throws AbortionException
     */
    public Pair<NegPolyOrder, Set<Rule>> solve(Set<Rule> dps, Set<Rule> usableRules, boolean allStrict) throws AbortionException {
        DynamicNegPOLOSolver.log.log(Level.INFO, "Using dynamic neg-Poly solver without preAFS check\n");
        if (dps.isEmpty()) {
            return null;
        }
        if (dps.size() == 1) {
            allStrict = true;
        }

//        long timeTotal = -System.currentTimeMillis();

        PET.PETCreator creator = new PET.PETCreator(usableRules);

        /*
         * building initial pets for rhs of usable rules
         */
        this.infoMap = new HashMap<Rule, Pair<PEP,PET>>();
        for (Rule rule : usableRules) {
            PEP pep = PEP.create(rule, false, this.range < 0);
            PET pet = creator.create(rule.getRight());
            this.infoMap.put(rule, new Pair<PEP, PET>(pep, pet));
        }

        /*
         * and for rhs of the DPs
         */
        List<PET> pets = new LinkedList<PET>();
        for (Rule dp : dps) {
            PET pet = creator.create(dp.getRight());
            if (pet != null) {
                pets.add(pet);
            }
        }

        this.orientedRules = usableRules;

        /*
         * now do the search and iterate over possible strict pairs if needed
         */
        if (allStrict) {
            State state = new State().create(null, dps, usableRules, pets);
            if (state != null) {
                Pair<NegPolyOrder, Set<Rule>> solution = this.solve(state, new HashMap<FunctionSymbol, YNM[]>());
                if (solution != null) {
//                    timeTotal += System.currentTimeMillis();
//                    System.out.println("Time: "+timeTotal+"ms");
                    return solution;
                }
            }
        } else {
            // iteratre over different strict DPs
            for (Rule strict : dps) {
//                System.out.println("Trying strict: "+strict);

                Set<Rule> nonStrict = new LinkedHashSet<Rule>(dps);
                nonStrict.remove(strict);
                State state = new State().create(strict, nonStrict, usableRules, pets);
                if (state != null) {
                    Pair<NegPolyOrder, Set<Rule>> solution = this.solve(state, new HashMap<FunctionSymbol, YNM[]>());
                    if (solution != null) {
//                        timeTotal += System.currentTimeMillis();
//                        System.out.println("Time: "+timeTotal+"ms");
                        return solution;
                    }
                }
            }
        }

        /*
         * no solution found
         */
//        timeTotal += System.currentTimeMillis();
//        System.out.println("Time: "+timeTotal+"ms");
        return null;
    }


    /**
     * performs the search for a solution
     * @param state - must not be null
     * @return null - if no solution was found, the solution, otherwise.
     * @throws AbortionException
     */
    private Pair<NegPolyOrder, Set<Rule>> solve(State state, Map<FunctionSymbol, YNM[]> oldPevlInter) throws AbortionException {
        this.checkTimer();
        // check whether we are done
        boolean noConstraints = state.currentConstraints.isEmpty();
        boolean noActivation = state.activationTerms.isEmpty();
        if (noConstraints && noActivation) {
            Set<Rule> oriented = new LinkedHashSet<Rule>(this.orientedRules);
            if (this.active) {
                oriented.removeAll(state.remainingUsableRules);
            }
            return new Pair<NegPolyOrder, Set<Rule>>(new NegPolyOrder(state.interpretation), oriented);
        }

        // so we are not done
        // do pevl-check
        Map<FunctionSymbol, YNM[]> pevlInter;
//        if (this.usePEVLCheck) { // no always use pevl-check!
        pevlInter = PEVLSolver.solve(state.interpretation, state.currentConstraints, oldPevlInter);
        if (pevlInter == null) {
//                System.out.println("PEVL-Check!");
            return null;
        }
//        } else {
//            pevlInter = oldPevlInter;
//        }



        // now choose a function symbol for specialization
        FunctionSymbol f;
        // our old strategy was not that successful:
        // get constraint with minimal set of unspecified function-symbols
        // and otherwise get arbitrary PET

        // now using simple strategy from static solver
        // todo: perhaps use pevlCheck information for choice!
        if (!noConstraints) {
//            Set<FunctionSymbol> minMiss = null;
//            int min = 0;
//            for (PEP pep : state.currentConstraints) {
//                Set<FunctionSymbol> candidat = pep.getMissingInterpretations();
//                int candSize = candidat.size();
//                if (minMiss == null || candSize < min) {
//                    minMiss = candidat;
//                    min = candSize;
//                }
//            }
//            f = minMiss.iterator().next();
            f = state.currentConstraints.iterator().next().getMissingInterpretations().iterator().next();
        } else {
            f = state.activationTerms.iterator().next().f;
        }


        // now try different interpretations

        int n = f.getArity();
        int restriction = this.restriction == -1 ? n : this.restriction;
        Iterable<int[]> fInterpretations =
            new InterpretationEnumerator(n, this.range, restriction, pevlInter.get(f), NegPOLOSolver.reverse);
        for (int[] specialization : fInterpretations) {
            State newState = state.specialize(f, specialization);
            if (newState != null) {
                Pair<NegPolyOrder, Set<Rule>> solution = this.solve(newState, pevlInter);
                if (solution != null) {
                    return solution;
                }
            }
        }
        state.removeSpecialization(f);

        // we have tried every interpretation, giving up
        return null;
    }


    private void checkTimer() throws AbortionException {
        this.ticks++;
        if (this.ticks == DynamicNegPOLOSolver.STATES_PER_CHECK) {
            this.ticks = 0;
            this.clock.checkAbortion();
        }
    }



    /**
     * a state consists of a set of constraints and a partial interpretation.
     * Moreover, we have a set of possible (remaining) usable rules and a
     * set of terms that may enforce some rules to become usable.
     * The invariant is that only those constraints are stored where the truth
     * value is unclear. Moreover, we only store activation terms that do enforce
     * new constraints indirectly, but not directly.
     * Everything else will be thrown out or will lead to
     * the unsatisfiable state (represented by null).
     * @author thiemann
     */
    private class State {

        LinkedHashMap<FunctionSymbol, int[]> interpretation;
        LinkedHashSet<PEP> currentConstraints;
        List<PET> activationTerms;
        LinkedHashSet<Rule> remainingUsableRules;

        /**
         * creates a new State where all constraints stored
         * are not-completely specified and where it is not yet
         * clear whether they are satisfied, unsatisfiable, or depending on
         * specialization.
         * Moreover, all usable rules have been created.
         * @param strictDp - the strict DP (if null, all other dps will result in strict constraints!)
         * @param dps - the remaining DPs
         * @return
         */
        public State create(Rule strictDp, Set<Rule> dps, Set<Rule> usable, List<PET> activation) {
            State s = new State();
            s.interpretation = new LinkedHashMap<FunctionSymbol, int[]>();
            s.currentConstraints = new LinkedHashSet<PEP>();
            boolean strict = true;
            if (strictDp != null) {
                s.currentConstraints.add(PEP.create(strictDp, strict, DynamicNegPOLOSolver.this.range < 0));
                strict = false;
            }
            for (Rule dp : dps) {
                s.currentConstraints.add(PEP.create(dp, strict, DynamicNegPOLOSolver.this.range < 0));
            }
            s.remainingUsableRules = new LinkedHashSet<Rule>(usable);
            s.activationTerms = activation;
            return s.simplify();
        }

        private State() {
        }

        /**
         * creates all new constraints that have to be generated.
         * all constraints that can be evaluated will be deleted or
         * will result in a null state (depending on value-state)
         * IMPORTANT: this is a destructive method!! (but interpretatation will not be changed)
         * @return
         */
        State simplify() {
            // check all constraints
            Iterator<PEP> constraintIterator = this.currentConstraints.iterator();
            while (constraintIterator.hasNext()) {
                PEP constraint = constraintIterator.next();
                YNM status = constraint.getStatus();
                if (status == DynamicNegPOLOSolver.YES) {
                    constraintIterator.remove();
                } else if (status == DynamicNegPOLOSolver.NO) {
                    return null;
                }
            }

            // create and add all new constraints due to activation terms
            List<PET> todoPETs = this.activationTerms;
            List<PET> nearlyFinalPETs = new LinkedList<PET>();

            while (!todoPETs.isEmpty()) {
//                /* debug */
//                System.out.println("remaining Rules");
//                for (Rule rule : this.remainingUsableRules) {
//                    System.out.println(rule);
//                }
//                System.out.println("\ntodo PETs");
//                for (PET pet : todoPETs) {
//                    System.out.println(pet);
//                }
//                System.out.println("\n\n");
//                /* end debug */
                List<PET> newTodoPETs = new LinkedList<PET>(); // set for PETs from new Rules
                // examine current PETs
                for (PET pet : todoPETs) {
                    Set<Rule> newlyUsable = new LinkedHashSet<Rule>();
                    nearlyFinalPETs.addAll(pet.simplify(this.interpretation, this.remainingUsableRules, newlyUsable));
                    // build PEPs and PETs for new rules (constraints and new activation terms)
                    for (Rule rule : newlyUsable) {
                        Pair<PEP, PET> petPep = DynamicNegPOLOSolver.this.infoMap.get(rule);

                        // first check PEP for truth value
                        PEP constraint = petPep.x.specialize(this.interpretation);
                        YNM status = constraint.getStatus();
                        // abort if false
                        if (status == DynamicNegPOLOSolver.NO) {
                            return null;
                        }
                        // and add if not YES
                        if (status == DynamicNegPOLOSolver.MAYBE) {
                            this.currentConstraints.add(constraint);
                        }

                        // now handle the activation term
                        if (petPep.y != null) {
                            newTodoPETs.add(petPep.y);
                        }
                    }
                }
                todoPETs = newTodoPETs;
            }


            // finally create final PETs by deleting superflous PETs
            this.activationTerms = nearlyFinalPETs;
            PET.deleteAfterSimplification(this.activationTerms, this.remainingUsableRules);
            return this;
        }


        /**
         * returns a new state that adds the given interpretation for f to the
         * current interpretation.
         * Important: this method is destructive for efficiency reasons.
         * To undo this change, call removeSpecialization!
         */
        State specialize(FunctionSymbol f, int[] specialization) {
            Pair<Boolean, PEP> res;

            // specialize the current constraints
            LinkedHashSet<PEP> newConstraints = new LinkedHashSet<PEP>();
            for (PEP pep : this.currentConstraints) {
                res = PEP.specialize(pep, f, specialization);
                if (res != null) {
                    // we have a new pet
                    // check for truth value
                    if (res.x == null) {
                        // no truth value, continue with new pet
                        newConstraints.add(res.y);
                    } else {
                        // we have truth value
                        // abort if truth = false
                        if (!res.x) {
                            return null;
                        }
                        // otherwise we can just dismiss the contraint
                        // by doing nothing here

                    }
                } else {
                    // nothing changed and we just use add the old pet
                    newConstraints.add(pep);
                }
            }

            // now create a new State
            State newState = new State();

            newState.interpretation = this.interpretation;
//          this is destructive as we do not copy the interpretation!
            newState.interpretation.put(f, specialization);
            newState.currentConstraints = newConstraints;
            newState.remainingUsableRules = new LinkedHashSet<Rule>(this.remainingUsableRules);
            newState.activationTerms = new LinkedList<PET>(this.activationTerms);

            return newState.simplify();
        }


        /**
         * removes the attempt to give some interpretation for f
         * @param f
         */
        void removeSpecialization(FunctionSymbol f) {
            this.interpretation.remove(f);
        }

    }

}
