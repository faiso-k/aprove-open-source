/*
 * Created on 17.03.2005
 */
package aprove.verification.dpframework.BasicStructures.AFSPrecalculation;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


/**
 * @author thiemann
 *
 * The DynamicYnmPEVLSolver can iterate over all AFSs that satisfy that
 * the the corresponding active usable rules and filtered DPs form a TRS.
 *
 * The iterator can only be used once, so if one wants to iterate multiple
 * times, one should use a MemoryIterator.
 *
 * Moreover, this class is NOT THREAD SAFE.
 *
 */
public class DynamicYnmPEVLSolver implements AbortableIterable<Pair<Map<FunctionSymbol, YNM[]>, Set<? extends GeneralizedRule>>> {

    private final static YNM YES = YNM.YES;
    private final static YNM NO = YNM.NO;
    private final static YNM MAYBE = YNM.MAYBE;

    private final int restriction; // restrict possible AFSs to include at most restriction many args
    // -1 corresponds to no restriction
    private final boolean reverse; // order in which AFSs are tried 0000 and then 0001 or then 1000


    private final Map<GeneralizedRule, Triple<YnmPEVL, YnmPEVL, YnmPET>> infoMap;
    // in this map we recompute for each rule
    // its constraint (the two PEVLs) and
    // its activation term (the PET)
    // possible improvements: icap(s) instead of tcap for
    // innermost constraint solving

    private final Set<? extends GeneralizedRule> usableRules;

    private final Set<? extends GeneralizedRule> dps;


    // the one time iterator through the solutions
    private AbortableIterator<Pair<Map<FunctionSymbol, YNM[]>, Set<? extends GeneralizedRule>>> iterator;
    private boolean active = true;


    /**
     * creates a new PEVL Solver for the given Scc.
     * @param reverse start with arguments from left or from right
     * @param restriction the nr of args for each symbol that may be kept
     */
    public DynamicYnmPEVLSolver(QDPProblem scc, int restriction, boolean reverse) {
        this(scc, restriction, reverse, true);

    }
    /**
     * creates a new PEVL Solver for the given Scc.
     * @param reverse start with arguments from left or from right
     * @param restriction the nr of args for each symbol that may be kept
     */
    public DynamicYnmPEVLSolver(QDPProblem scc, int restriction, boolean reverse, boolean active) {
        this.active = active;
        this.restriction = restriction < 0 ? -1 : restriction;
        this.reverse = reverse;
        this.dps = scc.getP();
        Set<Rule> usableRules = scc.getUsableRules();
        this.usableRules = usableRules;

        YnmPET.PETCreator creator = new YnmPET.PETCreator(DynamicYnmPEVLSolver.this.usableRules);

        /*
         * building info map (initial pevls and pets for usable rules)
         */
        this.infoMap = new HashMap<GeneralizedRule, Triple<YnmPEVL, YnmPEVL, YnmPET>>();
        for (GeneralizedRule rule : this.usableRules) {
            YnmPEVL left = YnmPEVL.create(rule.getLeft(), true);
            YnmPEVL right = YnmPEVL.create(rule.getRight(), false);
            YnmPET pet = creator.create(rule.getRight());
            this.infoMap.put(rule, new Triple<YnmPEVL, YnmPEVL, YnmPET>(left, right, pet));
        }


        State state = new State().create(creator);
        this.iterator = new OneTimeIterator(state, this.active );
    }
    /**
     * creates a new PEVL Solver for the given Scc.
     * @param reverse start with arguments from left or from right
     * @param restriction the nr of args for each symbol that may be kept
     */
    public DynamicYnmPEVLSolver(Set<? extends GeneralizedRule> P, Set<? extends GeneralizedRule> R, int restriction, boolean reverse, boolean active) {
        this.active = active;
        this.restriction = restriction < 0 ? -1 : restriction;
        this.reverse = reverse;
        this.dps = P;
        this.usableRules = R;

        YnmPET.PETCreator creator = new YnmPET.PETCreator(DynamicYnmPEVLSolver.this.usableRules);

        /*
         * building info map (initial pevls and pets for usable rules)
         */
        this.infoMap = new HashMap<GeneralizedRule, Triple<YnmPEVL, YnmPEVL, YnmPET>>();
        for (GeneralizedRule rule : this.usableRules) {
            YnmPEVL left = YnmPEVL.create(rule.getLeft(), true);
            YnmPEVL right = YnmPEVL.create(rule.getRight(), false);
            YnmPET pet = creator.create(rule.getRight());
            this.infoMap.put(rule, new Triple<YnmPEVL, YnmPEVL, YnmPET>(left, right, pet));
        }


        State state = new State().create(creator);
        this.iterator = new OneTimeIterator(state, this.active );
    }

    /**
     * expand an Afs. The semantics is as follows:
     * The solver only returns a mapping of function symbols that are important to
     * determine the usable rules and to determine that the filtered rules form a TRS. The other symbols
     * are not even mentioned. E.g. for P = {F(x,y) -> F(f(a),g(y))} and R = emptyset it would not be
     * required to fix the filtering for f and a, as the DP never violates the variable condition in the
     * first argument of F!
     * But for creating filtered rules, of course f is important, and one has different choices (all).
     * This expansion also created entries in the map for these symbols like f.
     *
     * However, in the solution there might also be to much symbols determined, hence, we restrict the
     * afs to those symbols that are really needed.
     */
    private Map<FunctionSymbol, YNM[]> expandAfs(Map<FunctionSymbol, YNM[]> restriction, Set<? extends GeneralizedRule> usableRules) {
        Map<FunctionSymbol, YNM[]> expanded = new LinkedHashMap<FunctionSymbol, YNM[]>();

        for (GeneralizedRule rule : this.dps) {
            DynamicYnmPEVLSolver.expandAfsForTerm(expanded, rule.getLeft(), restriction);
            DynamicYnmPEVLSolver.expandAfsForTerm(expanded, rule.getRight(), restriction);
        }
        for (GeneralizedRule rule : usableRules) {
            DynamicYnmPEVLSolver.expandAfsForTerm(expanded, rule.getLeft(), restriction);
            DynamicYnmPEVLSolver.expandAfsForTerm(expanded, rule.getRight(), restriction);
        }
        return expanded;
    }

    private static void expandAfsForTerm(Map<FunctionSymbol, YNM[]> expanded, TRSTerm t, Map<FunctionSymbol, YNM[]> restriction) {
        if (!t.isVariable()) {
            TRSFunctionApplication ft = (TRSFunctionApplication) t;
            FunctionSymbol f = ft.getRootSymbol();
            int n = f.getArity();
            YNM[] inter = expanded.get(f);

            if (inter == null) {
                inter = restriction.get(f);
                if (inter == null) {
                    inter = new YNM[n];
                    for (int i=0; i<n; i++) {
                        inter[i] = DynamicYnmPEVLSolver.MAYBE;
                    }
                }
                expanded.put(f, inter);
            }

            int i = 0;
            for (TRSTerm arg : ft.getArguments()) {
                if (inter[i] != DynamicYnmPEVLSolver.NO) {
                    DynamicYnmPEVLSolver.expandAfsForTerm(expanded, arg, restriction);
                }
                i++;
            }
        }
    }


    @Override
    public AbortableIterator<Pair<Map<FunctionSymbol, YNM[]>, Set<? extends GeneralizedRule>>> iterator() {
        AbortableIterator<Pair<Map<FunctionSymbol, YNM[]>, Set<? extends GeneralizedRule>>> i = this.iterator;
        // only one iterator is allowed, see docu for OneTimeIterator
        this.iterator = null;
        return i;
    }

    /*
     * the iterator iterates over all possible afss by keeping a stack (set) of internal states;
     * perhaps the initial state is modified, so before making two instances of this oneTimeIterator
     * for the same DynamicPEVLSolver one should check side effects
     */
    private class OneTimeIterator implements AbortableIterator<Pair<Map<FunctionSymbol, YNM[]>, Set<? extends GeneralizedRule>>> {

        /*
         * for timing
         */
        private static final int STATES_PER_CHECK = 5000;
        private Abortion abortion;
        private int ticks;

        /*
         * for computation of results
         */
        private Stack<Triple<State, FunctionSymbol, Iterator<boolean[]>>> stack;
        private boolean computedNextResult;
        private State nextSolution;
        private boolean active = true;

        private OneTimeIterator(State state, boolean active) {
            this.stack = new Stack<Triple<State, FunctionSymbol, Iterator<boolean[]>>>();
            if (state != null) {
                this.stack.push(new Triple<State, FunctionSymbol, Iterator<boolean[]>>(state, null, null));
            }
            this.computedNextResult = false;
            this.nextSolution = null;
            this.ticks = 0;
            this.active = active;
        }



        private void checkTimer() throws AbortionException {
            this.ticks++;
            if (this.ticks == OneTimeIterator.STATES_PER_CHECK) {
                this.ticks = 0;
                this.abortion.checkAbortion();
            }
        }



        /**
         * if result is null, we have an unsolvable state
         * if functionSymbol is null, the state is a solution
         * if functionSymbol is f, then the new state should be used and we should evaluate f next
         */
        private Pair<FunctionSymbol, State> getUndeterminedFunctionSymbol(State state) {
            Pair<FunctionSymbol, State> res;

            // check whether we are done
            boolean noConstraints = state.currentConstraints.isEmpty();
            boolean noActivation = state.activationTerms.isEmpty();
            if (noConstraints && noActivation) {
                res = new Pair<FunctionSymbol, State>(null, state);
                return res;
            }


            // now choose a function symbol for specialization
            FunctionSymbol f = null;

            if (!noConstraints) {
                Iterator<Pair<YnmPEVL, YnmPEVL>> iterator = state.currentConstraints.iterator();
                while (iterator.hasNext()) {
                    Pair<YnmPEVL, YnmPEVL> constraint = iterator.next();
                    Pair<Set<FunctionSymbol>, YnmPEVL> missInterPair;

                    // try to find missing f in left side
                    missInterPair = constraint.x.getMissingInterpretationAndSimplifiedPevl(state.interpretation);
                    constraint.x = missInterPair.y;
                    if (!missInterPair.x.isEmpty()) {
                        f = missInterPair.x.iterator().next();
                        break;
                    }

                    // and in right side
                    missInterPair = constraint.y.getMissingInterpretationAndSimplifiedPevl(state.interpretation);
                    constraint.y = missInterPair.y;
                    if (!missInterPair.x.isEmpty()) {
                        f = missInterPair.x.iterator().next();
                        break;
                    }

                    // oops, we are fully specified, but we have not detected it earlier
                    YNM status = DynamicYnmPEVLSolver.checkConstraint(constraint);
                    if (status == DynamicYnmPEVLSolver.YES) {
                        iterator.remove();
                    } else if (status == DynamicYnmPEVLSolver.NO) {
                        return null;
                    } else {
                        throw new RuntimeException("Bug in getMissingInterpretationsAndSimplifiedPevl: miss=empty, but pevl is not fully specified!");
                    }
                }

                // check whether we are done now!
                if (f == null && noActivation && state.currentConstraints.isEmpty()) {
                    return new Pair<FunctionSymbol, State>(null, state);
                }
            }


            if (f == null) {
                f = state.activationTerms.get(0).f;
                // add new interpretation if necessary
                YNM[] inter = state.interpretation.get(f);
                if (inter == null) {
                    int n = f.getArity();
                    inter = new YNM[n];
                    for (int i=0; i<n; i++) {
                        inter[i] = YNM.MAYBE;
                    }
                    state.interpretation.put(f, inter);
                }
            }

            return new Pair<FunctionSymbol, State>(f, state);
        }


        @Override
        public boolean hasNext(Abortion aborter) throws AbortionException {
            this.abortion = aborter;
            if (!this.computedNextResult) {
                this.calculateNext();
            }
            return (this.nextSolution != null);
        }

        @Override
        public Pair<Map<FunctionSymbol, YNM[]>, Set<? extends GeneralizedRule>> next(Abortion aborter) throws NoSuchElementException, AbortionException {
            if (!this.hasNext(aborter)) {
                throw new NoSuchElementException();
            } else {
                Set<GeneralizedRule> oriented = new LinkedHashSet<GeneralizedRule>(DynamicYnmPEVLSolver.this.usableRules);
                if (this.active) {
                    oriented.removeAll(this.nextSolution.remainingUsableRules);
                }
                Map<FunctionSymbol, YNM[]> interpretation = DynamicYnmPEVLSolver.this.expandAfs(this.nextSolution.interpretation, oriented);
                this.nextSolution = null;
                this.computedNextResult = false;
//              System.out.println(debug+": "+DynamicYnmPEVLSolver.toString(interpretation));
                return new Pair<Map<FunctionSymbol, YNM[]>, Set<? extends GeneralizedRule>>(interpretation, oriented);
            }
        }


        private void calculateNext() throws AbortionException {
            while (!this.stack.isEmpty()) {
                this.checkTimer();

                Triple<State, FunctionSymbol, Iterator<boolean[]>> lastEntry = this.stack.peek();
                State state = lastEntry.x;
                FunctionSymbol f = lastEntry.y;
                if (f == null) {
                    Pair<FunctionSymbol, State> status = this.getUndeterminedFunctionSymbol(state);
                    if (status == null) {
                        this.stack.pop();
                        continue;
                    }

                    f = status.x;

                    if (f == null) {
                        this.nextSolution = status.y;
                        this.computedNextResult = true;
                        this.stack.pop();
                        return;
                    }

                    state = status.y;
                    int n = f.getArity();
                    YNM[] inter = state.interpretation.get(f);
                    if (Globals.useAssertions) {
                        assert(inter != null);
                    }
                    lastEntry.y = f;
                    int restriction = DynamicYnmPEVLSolver.this.restriction == -1 ? n : DynamicYnmPEVLSolver.this.restriction;
                    lastEntry.z = new BasicPowerSet(n, restriction, inter, DynamicYnmPEVLSolver.this.reverse).iterator();
                }

                Iterator<boolean[]> iterator = lastEntry.z;
                boolean dropLevel = true;
                while (iterator.hasNext()) {
                    boolean[] specialization = iterator.next();
                    State newState = state.specialize(f, specialization);
                    if (newState != null) {
                        this.stack.push(new Triple<State, FunctionSymbol, Iterator<boolean[]>>(newState, null, null));
                        dropLevel = false;
                        break;
                    }
                }
                if (dropLevel) {
                    this.stack.pop();
                }
            }

            this.nextSolution = null;
            this.computedNextResult = true;
        }


//      /**
//      * performs the search for a solution
//      * @param state - must not be null
//      * @return null - if no solution was found, the solution, otherwise.
//      */
//      private Pair<Map<FunctionSymbol, int[]>, Set<Rule>> solve(State state) throws ProcessorInterruptedException {
//      this.checkTimer();
//      // check whether we are done
//      Pair<FunctionSymbol, State> status = this.getUndeterminedFunctionSymbol(state);
//      if (status == null) {
//      return null;
//      }
//
//
//      FunctionSymbol f = status.x;
//
//      if (f == null) {
//      Set<Rule> oriented = new LinkedHashSet<Rule>(this.orientedRules);
//      oriented.removeAll(state.remainingUsableRules);
//      return new Pair<Map<FunctionSymbol, int[]>, Set<Rule>>(state.interpretation, oriented);
//      }
//
//      state = status.y;
//
//
//      // now try different interpretations
//
//      int n = f.getArity();
//      int restriction = this.restriction == -1 ? n : this.restriction;
//      Iterable<boolean[]> fInterpretations =
//      new BasicPowerSet(n, restriction, state.interpretation.get(f));
//      for (boolean[] specialization : fInterpretations) {
//      State newState = state.specialize(f, specialization);
//      if (newState != null) {
//      Pair<Map<FunctionSymbol, int[]>, Set<Rule>> solution = solve(newState);
//      if (solution != null) return solution;
//      }
//      }
//
//      // we have tried every interpretation, giving up
//      return null;
//      }


    }

    /**
     * takes a constraint. If it is fully evaluated then we determine its truth-value.
     * Otherwise we return maybe
     * @param constraint
     * @return
     */
    private static YNM checkConstraint(Pair<YnmPEVL, YnmPEVL> constraint) {
        if (constraint.x.isFullySpecified() && constraint.y.isFullySpecified()) {
            Set<String> varsLeft = constraint.x.certainVars();
            for (String var : constraint.y.certainVars()) {
                if (!varsLeft.contains(var)) {
                    return DynamicYnmPEVLSolver.NO;
                }
            }
            return DynamicYnmPEVLSolver.YES;
        } else {
            return DynamicYnmPEVLSolver.MAYBE;
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

        LinkedHashMap<FunctionSymbol, YNM[]> interpretation;
        List<Pair<YnmPEVL, YnmPEVL>> currentConstraints;
        List<YnmPET> activationTerms;
        LinkedHashSet<GeneralizedRule> remainingUsableRules;

        /**
         * creates a new State where all constraints stored
         * are not-completely specified and where it is not yet
         * clear whether they are satisfied, unsatisfiable, or depending on
         * specialization.
         * Moreover, all usable rules have been created.
         * @param creator the method to create pets
         */
        public State create(YnmPET.PETCreator creator) {
            State s = new State();

            /*
             * build PEVLs and PETs for DPs (constraints and activation terms)
             */
            s.activationTerms = new LinkedList<YnmPET>();
            s.currentConstraints = new LinkedList<Pair<YnmPEVL, YnmPEVL>>();
            for (GeneralizedRule dp : DynamicYnmPEVLSolver.this.dps) {
                // constraint
                YnmPEVL left = YnmPEVL.create(dp.getLeft(), true);
                YnmPEVL right = YnmPEVL.create(dp.getRight(), false);
                s.currentConstraints.add(new Pair<YnmPEVL, YnmPEVL>(left, right));

                // and activation
                YnmPET pet = creator.create(dp.getRight());
                if (pet != null) {
                    s.activationTerms.add(pet);
                }
            }
            s.remainingUsableRules = new LinkedHashSet<GeneralizedRule>(DynamicYnmPEVLSolver.this.usableRules);
            s.interpretation = new LinkedHashMap<FunctionSymbol, YNM[]>();

            return s.simplify();
        }

        private State() {
        }

        /**
         * creates all new constraints that have to be generated.
         * all constraints that can be evaluated will be deleted or
         * will result in a null state (depending on value-state)
         * IMPORTANT: this is a destructive method!! Changes:
         *   - the list of constraints (and the pairs inside the list!)
         *   - the list of activation terms
         *   - the set of remaining usable rules
         *   - the interpretation (both the map and the int-arrays)
         * @return
         */
        State simplify() {
            // check all constraints
            Iterator<Pair<YnmPEVL, YnmPEVL>> constraintIterator = this.currentConstraints.iterator();
            while (constraintIterator.hasNext()) {
                Pair<YnmPEVL, YnmPEVL> constraint = constraintIterator.next();
                YNM status = DynamicYnmPEVLSolver.checkConstraint(constraint);
                if (status == DynamicYnmPEVLSolver.YES) {
                    constraintIterator.remove();
                } else if (status == DynamicYnmPEVLSolver.NO) {
                    return null;
                }
            }

            LinkedHashMap<FunctionSymbol, YNM[]> interpretation = this.interpretation;
            List<Pair<YnmPEVL, YnmPEVL>> constraintsToAnalyze = this.currentConstraints;
            List<Pair<YnmPEVL, YnmPEVL>> constraintsDone = new LinkedList<Pair<YnmPEVL, YnmPEVL>>();
            boolean first = true;
            Set<FunctionSymbol> changed = null;

            while (first || !constraintsToAnalyze.isEmpty()) {
                first = false;

                // create and add all new constraints due to activation terms
                List<YnmPET> todoPETs = this.activationTerms;
                List<YnmPET> nearlyFinalPETs = new LinkedList<YnmPET>();

                while (!todoPETs.isEmpty()) {
                    List<YnmPET> newTodoPETs = new LinkedList<YnmPET>(); // set for PETs from new Rules
                    // examine current PETs
                    for (YnmPET pet : todoPETs) {
                        Set<GeneralizedRule> newlyUsable = new LinkedHashSet<GeneralizedRule>();
//                      perhaps integrate changed information here for less simplifications
                        nearlyFinalPETs.addAll(pet.simplify(interpretation, this.remainingUsableRules, newlyUsable));
                        // build PEPs and PETs for new rules (constraints and new activation terms)
                        for (GeneralizedRule rule : newlyUsable) {
                            Triple<YnmPEVL, YnmPEVL, YnmPET> pevlPet = DynamicYnmPEVLSolver.this.infoMap.get(rule);

                            // first check PEP for truth value
                            YnmPEVL left = pevlPet.x.specialize(null, interpretation);
                            YnmPEVL right = pevlPet.y.specialize(null, interpretation);
                            Pair<YnmPEVL, YnmPEVL> newConstraint = new Pair<YnmPEVL, YnmPEVL>(left, right);
                            YNM status = DynamicYnmPEVLSolver.checkConstraint(newConstraint);
                            // abort if false
                            if (status == DynamicYnmPEVLSolver.NO) {
                                return null;
                            }
                            // and add if not YES
                            if (status == DynamicYnmPEVLSolver.MAYBE) {
                                constraintsToAnalyze.add(0, newConstraint);
                            }

                            // now handle the activation term
                            if (pevlPet.z != null) {
                                newTodoPETs.add(pevlPet.z);
                            }
                        }
                    }
                    todoPETs = newTodoPETs;
                }


                // next create final PETs by deleting superflous PETs
                this.activationTerms = nearlyFinalPETs;
                YnmPET.deleteAfterSimplification(this.activationTerms, this.remainingUsableRules);



                // now we perform deduction over the constraintsToAnalyse
                changed = new LinkedHashSet<FunctionSymbol>();
                for (Pair<YnmPEVL, YnmPEVL> constraint : constraintsToAnalyze) {
                    boolean subFirst = true;
                    Set<FunctionSymbol> changesForThisConstraint = null;
                    while (subFirst || !changesForThisConstraint.isEmpty()) {
                        boolean doCheck = false;
                        if (subFirst) {
                            // in first case we have to apply changes from changed (from other constraints before)
                            subFirst = false;
                            if (!changed.isEmpty()) {
                                constraint.x = constraint.x.specialize(changed, interpretation);
                                constraint.y = constraint.y.specialize(changed, interpretation);
                                doCheck = true;
                            }
                        } else {
                            // otherwise we only have to apply changes from our own deduction
                            changed.addAll(changesForThisConstraint);
                            constraint.x = constraint.x.specialize(changesForThisConstraint, interpretation);
                            constraint.y = constraint.y.specialize(changesForThisConstraint, interpretation);
                            doCheck = true;
                        }

                        // check for complete evaluation
                        if (doCheck) {
                            YNM status = DynamicYnmPEVLSolver.checkConstraint(constraint);
                            if (status == DynamicYnmPEVLSolver.NO) {
                                return null;
                            } else if (status == DynamicYnmPEVLSolver.YES) {
                                changesForThisConstraint = null;
                                break;
                            }
                        }

                        changesForThisConstraint = YnmPEVL.deduce(constraint, interpretation, DynamicYnmPEVLSolver.this.restriction);
                        if (changesForThisConstraint == null) {
                            return null;
                        }
                    }

                    // now we are done by doing deductions over this constraint

                    if (changesForThisConstraint != null) {
                        // we may infer more from this constraint
                        constraintsDone.add(constraint);
                    }

                }

                // infer new todo constraints (reactivate Done constraints)
                constraintsToAnalyze.clear();
                if (!changed.isEmpty()) {
                    Iterator<Pair<YnmPEVL, YnmPEVL>> iterator = constraintsDone.iterator();
                    while (iterator.hasNext()) {
                        Pair<YnmPEVL, YnmPEVL> constraint = iterator.next();
                        // test whether we have changed something in this constraint
                        YnmPEVL left = constraint.x.specialize(changed, interpretation);
                        YnmPEVL right = constraint.y.specialize(changed, interpretation);
                        boolean foundChange = left != constraint.x || right != constraint.y;
                        if (foundChange) {
                            // build new constraint
                            constraint.x = left;
                            constraint.y = right;

                            // and check status
                            YNM status = DynamicYnmPEVLSolver.checkConstraint(constraint);
                            if (status == DynamicYnmPEVLSolver.NO) {
                                return null; // abort
                            }

                            iterator.remove(); // delete from done

                            if (status == DynamicYnmPEVLSolver.MAYBE) { // do not add constraint in case of YES
                                constraintsToAnalyze.add(constraint);
                            }
                        }
                    }
                }
            }

            this.currentConstraints = constraintsDone;
            this.interpretation = interpretation;

            return this;

        }


        /**
         * returns a new state that adds the given interpretation for f to the
         * current interpretation.
         * This method is not destructive!
         */
        State specialize(FunctionSymbol f, boolean[] specialization) {

            // create copies for all parts!

            // create new interpretation
            LinkedHashMap<FunctionSymbol, YNM[]> newInterpretation = new LinkedHashMap<FunctionSymbol, YNM[]>();
            for (Map.Entry<FunctionSymbol, YNM[]> entry : this.interpretation.entrySet()) {
                FunctionSymbol g = entry.getKey();
                int n = g.getArity();
                YNM[] newInter = new YNM[n];
                if (g.equals(f)) {
                    for (int i=0; i<n; i++) {
                        newInter[i] = specialization[i] ? DynamicYnmPEVLSolver.YES : DynamicYnmPEVLSolver.NO;
                    }
                } else {
                    YNM[] oldInter = entry.getValue();
                    for (int i=0; i<n; i++) {
                        newInter[i] = oldInter[i];
                    }
                }
                newInterpretation.put(g, newInter);
            }

            // and new constraints
            List<Pair<YnmPEVL, YnmPEVL>> newConstraints = new LinkedList<Pair<YnmPEVL, YnmPEVL>>();
            Set<FunctionSymbol> fs = new LinkedHashSet<FunctionSymbol>();
            fs.add(f);
            for (Pair<YnmPEVL, YnmPEVL> constraint : this.currentConstraints) {
                YnmPEVL left = constraint.x.specialize(fs, newInterpretation);
                YnmPEVL right = constraint.y.specialize(fs, newInterpretation);
                newConstraints.add(new Pair<YnmPEVL, YnmPEVL>(left, right));
            }

            // now create a new State
            State newState = new State();

            newState.interpretation = newInterpretation;
            newState.currentConstraints = newConstraints;
            newState.remainingUsableRules = new LinkedHashSet<GeneralizedRule>(this.remainingUsableRules);
            newState.activationTerms = new LinkedList<YnmPET>(this.activationTerms);

            return newState.simplify();
        }


        @Override
        public String toString() {
            String s;
            s = "Constraints:\n";
            for (Pair<YnmPEVL, YnmPEVL> constraint : this.currentConstraints) {
                s += constraint;
            }
            s += this.activationTerms.size() + " PETs\n";
            s += this.remainingUsableRules.size() + " remaining rules\n";
            s += "Interpretation:\n";
            for (Map.Entry<FunctionSymbol, YNM[]> entry : this.interpretation.entrySet()) {
                s += "  "+entry.getKey().getName()+": [";
                YNM[] inter = entry.getValue();
                boolean first = true;
                for (int i=0; i<inter.length; i++) {
                    if (first) {
                        first = false;
                    } else {
                        s += ",";
                    }
                    YNM status = inter[i];
                    s += status == DynamicYnmPEVLSolver.YES ? "1" : (status == DynamicYnmPEVLSolver.NO ? "0" : "M");
                }
                s += "]\n";
            }
            return s;
        }
    }


    public static String toString(Map<FunctionSymbol, YNM[]> interpretation) {
        String s = "Interpretation:\n";
        for (Map.Entry<FunctionSymbol, YNM[]> entry : interpretation.entrySet()) {
            s += "  "+entry.getKey().getName()+": [";
            YNM[] inter = entry.getValue();
            boolean first = true;
            for (int i=0; i<inter.length; i++) {
                if (first) {
                    first = false;
                } else {
                    s += ",";
                }
                YNM status = inter[i];
                s += status == DynamicYnmPEVLSolver.YES ? "1" : (status == DynamicYnmPEVLSolver.NO ? "0" : "M");
            }
            s += "]\n";
        }
        return s;
    }

    /**
     * debug output of a solution
     * @param solution
     * @return
     */
    public static String toString(Pair<Map<FunctionSymbol, YNM[]>, Set<Rule>> solution) {
        if (solution == null) {
            return "No solution";
        }
        String s = DynamicYnmPEVLSolver.toString(solution.x);
        s += "Rules:\n";
        for (Rule rule : solution.y) {
            s += "  "+rule+"\n";
        }
        return s;
    }


}
