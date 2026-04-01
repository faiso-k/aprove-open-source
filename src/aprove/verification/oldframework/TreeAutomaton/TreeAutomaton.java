package aprove.verification.oldframework.TreeAutomaton;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * @author Marcel Klinzing
 * @param <S> The type of a function symbol/constant.
 * @param <Z> The type of a state.
 */

public class TreeAutomaton<S extends HasArity, Z> {

    private final ImmutableSet<Z> finalStates;
    private final ImmutableSet<Transition<S, Z>> transitions;
    private final ImmutableMap<Z, Set<Z>> epsTransitions;

    /**
     * @param finalStates The set of final states of this tree automaton.
     * @param transitions The set of transitions for this tree automaton. For 2
     * function symbols f1 and f2 (used in the Transitions), f1.equals(f2)
     * should be always false, if the arity of f1 doesn't equal the arity of f2.
     */
    public TreeAutomaton(final ImmutableSet<Z> finalStates,
        final ImmutableSet<Transition<S, Z>> transitions) {
        this(finalStates, transitions, ImmutableCreator.create(new LinkedHashMap<Z, Set<Z>>()));

    }

    public TreeAutomaton(final ImmutableSet<Z> finalStates, final ImmutableSet<Transition<S, Z>> transitions,
        final ImmutableMap<Z, Set<Z>> epsTransitions) {
        if (Globals.useAssertions) {
            this.checkConstrArg(finalStates, transitions, epsTransitions);
        }
        this.finalStates = finalStates;
        this.transitions = transitions;
        this.epsTransitions = epsTransitions;
    }

    private void checkConstrArg(final ImmutableSet<Z> finalStates,
        final ImmutableSet<Transition<S, Z>> transitions, final ImmutableMap<Z, Set<Z>> epsTransitions) {
        assert (finalStates != null);
        assert (transitions != null);
        assert (epsTransitions != null);
    }

    public static <S extends HasArity, Z>TreeAutomaton<S, Z> create(
        final Set<Z> finalStates,
        final Set<Transition<S, Z>> transitions) {
        ImmutableSet<Z> iFS = ImmutableCreator.create(finalStates);
        ImmutableSet<Transition<S, Z>> iT = ImmutableCreator.create(transitions);
        return new TreeAutomaton<S, Z>(iFS, iT);
    }

    public static <S extends HasArity, Z>TreeAutomaton<S, Z> create(
        final Set<Z> finalStates,
        final Set<Transition<S, Z>> transitions,
        Map<Z, Set<Z>> epsTransitions) {
        ImmutableSet<Z> iFS = ImmutableCreator.create(finalStates);
        ImmutableSet<Transition<S, Z>> iT = ImmutableCreator.create(transitions);
        ImmutableMap<Z, Set<Z>> iET = ImmutableCreator.create(epsTransitions);
        return new TreeAutomaton<S, Z>(iFS, iT, iET);
    }

    public static <S extends HasArity, Z>TreeAutomaton<S, Z> createEmpty() {
        Set<Z> fS = new LinkedHashSet<Z>();
        Set<Transition<S, Z>> t = new LinkedHashSet<Transition<S, Z>>();
        return TreeAutomaton.<S, Z>create(fS, t);
    }

    public ImmutableSet<Z> getFinalStates() {
        return this.finalStates;
    }

    public ImmutableSet<Transition<S, Z>> getTransitions() {
        return this.transitions;
    }

    public ImmutableMap<Z, Set<Z>> getEpsTransitions() {
        return this.epsTransitions;
    }

    public ImmutableMap<Z, Set<Z>> getReversedEpsTransitions() {
        Map<Z, Set<Z>> reversedEpsTransitions = new LinkedHashMap<Z, Set<Z>>();
        for (Map.Entry<Z, Set<Z>> entry : this.getEpsTransitions().entrySet()) {
            for (Z curRhs : entry.getValue()) {
                Set<Z> revRhs = reversedEpsTransitions.get(curRhs);
                if (revRhs == null) {
                    revRhs = new LinkedHashSet<Z>();
                }
                revRhs.add(entry.getKey());
                reversedEpsTransitions.put(curRhs, revRhs);
            }
        }
        return ImmutableCreator.create(reversedEpsTransitions);
    }

    /**
     * @return final states and states used in transitions
     */
    public ImmutableSet<Z> getAllStates() {
        final LinkedHashSet<Z> allStates = new LinkedHashSet<Z>();
        for (final Z fState : this.finalStates) {
            allStates.add(fState);
        }
        for (final Transition<S, Z> t : this.transitions) {
            for (final Z state : t.getLhsStateParameters()) {
                allStates.add(state);
            }

            allStates.add(t.getRhsState());
        }
        for (Map.Entry<Z, Set<Z>> entry : this.epsTransitions.entrySet()) {
            allStates.add(entry.getKey());
            for (Z state : entry.getValue()) {
                allStates.add(state);
            }
        }

        return ImmutableCreator.create(allStates);
    }

    public ImmutableSet<Z> getAllRhsStates() {
        final LinkedHashSet<Z> allRhsStates = new LinkedHashSet<Z>();

        for (final Transition<S, Z> t : this.transitions) {
            allRhsStates.add(t.getRhsState());
        }

        for (Map.Entry<Z, Set<Z>> entry : this.epsTransitions.entrySet()) {
            allRhsStates.addAll(entry.getValue());

        }
        return ImmutableCreator.create(allRhsStates);
    }

    /**
     * @return all function symbols/constants used in transitions
     */
    public ImmutableSet<S> getAllFunctionSymbols() {
        final LinkedHashSet<S> allFunctionSymbols = new LinkedHashSet<S>();
        for (final Transition<S, Z> trans : this.transitions) {
            allFunctionSymbols.add(trans.getLhsFunctionSymbol());
        }

        return ImmutableCreator.create(allFunctionSymbols);
    }

    /**
     * @return The set of all states, in which the tree automaton can be after
     * evaluating sigma(t).
     */
    public ImmutableSet<Z> evaluate(TRSTerm t, StateSubstitution<Z> sigma) {
        return this.evaluate(t, sigma, true);
    }

    private ImmutableSet<Z> evaluate(TRSTerm t, StateSubstitution<Z> sigma, boolean assertThis) {
        Map<TRSVariable, Z> stateSMap = sigma.getMap();
        Set<TRSVariable> variables = t.getVariables();
        Set<Z> reachedStates = new LinkedHashSet<Z>();
        if (Globals.useAssertions) {
            if (assertThis) {
                for (TRSVariable x : variables) {
                    assert (stateSMap.containsKey(x));
                }
            }
        }
        if (t.isVariable()) {
            Z state = stateSMap.get(t);
            reachedStates.addAll(this.epsTransClosure(state));
        } else if (t instanceof TRSFunctionApplication) {
            TRSFunctionApplication f = (TRSFunctionApplication)t;
            ImmutableList<TRSTerm> args = f.getArguments();
            ArrayList<Set<Z>> reachedStatesFromArgs = new ArrayList<Set<Z>>();
            // compute all states to which the arguments of f can be evaluated
            for (TRSTerm arg : args) {
                reachedStatesFromArgs.add(this.evaluate(arg, sigma, false));
            }
            //check which transition of this tree automaton can be applied to f
            for (Transition<S, Z> trans : this.transitions) {
                if (trans.getLhsFunctionSymbol().equals(f.getRootSymbol())) {
                    if (trans.getLhsFunctionSymbol().getArity() == f.getRootSymbol().getArity()) {
                        int nextArgument = 0;
                        boolean transApplicable = true;
                        for (Z z : trans.getLhsStateParameters()) {
                            if (!reachedStatesFromArgs.get(nextArgument).contains(z)) {
                                transApplicable = false;
                            }
                            nextArgument++;
                        }
                        if (transApplicable) {
                            reachedStates.addAll(this.epsTransClosure(trans.getRhsState()));
                        }
                    }
                }
            }
        }
        return ImmutableCreator.create(reachedStates);
    }

    /**
     * @return All lists of state Parameters q_1,...,q_n so that f(q_1,...,q_n)
     * is a lhs of a transition of this tree automaton.
     */
    public Set<List<Z>> getAllStateParamsWith(S f, Z rhsState) {
        Set<List<Z>> stateParamsWithF = new LinkedHashSet<List<Z>>();
        for (Transition<S, Z> trans : this.transitions) {
            if (f.equals(trans.getLhsFunctionSymbol()) && rhsState.equals(trans.getRhsState())) {
                stateParamsWithF.add(trans.getLhsStateParameters());
            }
        }
        return stateParamsWithF;
    }

    @Override
    public String toString() {
        String output =
            "TreeAutomaton [finalStates="
                + this.finalStates
                + ", transitions="
                + this.transitions
                + ", epsTransitions=[";
        for (Map.Entry<Z, Set<Z>> entry : this.epsTransitions.entrySet()) {
            if (!entry.getValue().isEmpty()) {
                output += entry.getKey() + "-->";
                for (Z state : entry.getValue()) {
                    output += state + " | ";
                }
                output = output.substring(0, output.length() - 2);
            }
        }
        output = output.substring(0, output.length() - 1);
        output += "]";
        return output;
    }

    /**
     * Builds the union of this tree automaton with the tree automaton given as
     * a parameter.
     */
    public TreeAutomaton<S, Z> union(final TreeAutomaton<S, Z> A) {
        TreeAutomaton<S, Z> unionedAutomaton;
        final LinkedHashSet<Z> unionedFStates = new LinkedHashSet<Z>();
        final LinkedHashSet<Transition<S, Z>> unionedTransitions =
            new LinkedHashSet<Transition<S, Z>>();

        //join final states
        for (final Z state : this.finalStates) {
            unionedFStates.add(state);
        }
        for (final Z state : A.finalStates) {
            unionedFStates.add(state);
        }

        //join transitions
        for (final Transition<S, Z> trans : this.transitions) {
            unionedTransitions.add(trans);
        }
        for (final Transition<S, Z> trans : A.transitions) {
            unionedTransitions.add(trans);
        }

        //join epsTransitions
        final Map<Z, Set<Z>> unionedEpsTransitions =
            TreeAutomatonHelper.<Z>unionEpsTransitions(this.epsTransitions, A.getEpsTransitions());

        final ImmutableLinkedHashSet<Z> immutableFStates = ImmutableCreator.create(unionedFStates);
        final ImmutableLinkedHashSet<Transition<S, Z>> immutableTransitions =
            ImmutableCreator.create(unionedTransitions);
        final ImmutableMap<Z, Set<Z>> immutableEpsTransitions = ImmutableCreator.create(unionedEpsTransitions);

        unionedAutomaton = new TreeAutomaton<S, Z>(immutableFStates, immutableTransitions, immutableEpsTransitions);
        return unionedAutomaton;

    }

    /**
     * Builds the subset (powerset) construction of this automaton. Currently
     * accessible States (resp. transitions operating on these) are kept, i.e.
     * sets with one element are identified with the element in the set.
     */
    public TreeAutomaton<S, Set<Z>> subsetConstructionWKT() {
        Set<Set<Z>> newPSetStates = new LinkedHashSet<Set<Z>>();
        Set<Transition<S, Z>> constantTransitions = new LinkedHashSet<Transition<S, Z>>();
        Set<Transition<S, Z>> posFSymbolTransitions = new LinkedHashSet<Transition<S, Z>>();
        final Set<Transition<S, Z>> allTransitions = this.removeEpsTransitions().getTransitions();

        final LinkedHashSet<Transition<S, Set<Z>>> newTransitions = new LinkedHashSet<Transition<S, Set<Z>>>();

        Map<Set<Z>, Set<Set<Z>>> newEpsTransitions = new LinkedHashMap<Set<Z>, Set<Set<Z>>>();

        // Keep Epsilon transitions
        for (Map.Entry<Z, Set<Z>> entry : this.getEpsTransitions().entrySet()) {
            Set<Z> newLhs = new LinkedHashSet<Z>();
            Set<Set<Z>> newRhs = new LinkedHashSet<Set<Z>>();
            newLhs.add(entry.getKey());
            newRhs.add(entry.getValue());
            newEpsTransitions.put(newLhs, newRhs);
        }

        for (Transition<S, Z> trans : allTransitions) {
            if (trans.getLhsFunctionSymbol().getArity() == 0) {
                constantTransitions.add(trans);
                Set<Z> newRhsState = new LinkedHashSet<Z>();
                newRhsState.add(trans.getRhsState());
                Transition<S, Set<Z>> newTrans =
                    Transition.<S, Set<Z>>create(trans.getLhsFunctionSymbol(), new ArrayList<Set<Z>>(), newRhsState);
                newTransitions.add(newTrans);
                newPSetStates.add(newRhsState);

            } else {
                posFSymbolTransitions.add(trans);
                List<Set<Z>> newStateParams = new ArrayList<Set<Z>>();
                for (Z state : trans.getLhsStateParameters()) {
                    Set<Z> newState = new LinkedHashSet<Z>();
                    newState.add(state);
                    newStateParams.add(newState);
                    newPSetStates.add(newState);
                }

                Set<Z> newRhsState = new LinkedHashSet<Z>();
                newRhsState.add(trans.getRhsState());
                Transition<S, Set<Z>> newTrans =
                    Transition.<S, Set<Z>>create(trans.getLhsFunctionSymbol(), newStateParams, newRhsState);
                newTransitions.add(newTrans);
                newPSetStates.add(newRhsState);
            }
        }

        LinkedHashSet<Set<Z>> oldPSetStates = new LinkedHashSet<Set<Z>>();
        final LinkedHashSet<Set<Z>> newFStates = new LinkedHashSet<Set<Z>>();
        for (Transition<S, Z> constTrans : constantTransitions) {
            Set<Transition<S, Set<Z>>> pSetTrans = this.createPowerSetTransitions(constTrans, new LinkedHashSet<Set<Z>>());
            newTransitions.addAll(pSetTrans);
            Set<Z> rhsState = pSetTrans.iterator().next().getRhsState();
            newPSetStates.add(rhsState);
        }

        //compute new transitions of powerset automaton
        //compute new final states of powerset automaton (only those which build rhs's of transitions)
        while (!oldPSetStates.equals(newPSetStates)) {
            oldPSetStates.addAll(newPSetStates);
            for (final Transition<S, Z> trans : posFSymbolTransitions) {
                final LinkedHashSet<Transition<S, Set<Z>>> pSetTransitions =
                    this.createPowerSetTransitions(trans, oldPSetStates);//allTransitions, oldPSetStates);
                newTransitions.addAll(pSetTransitions);
                for (Transition<S, Set<Z>> pSetTrans : pSetTransitions) {
                    newPSetStates.add(pSetTrans.getRhsState());
                }

            }
        }

        //compute new final States
        final LinkedHashSet<Set<Z>> pSetFStates = this.createPowerSetFStates(this.finalStates, newPSetStates);
        newFStates.addAll(pSetFStates);

        return TreeAutomaton.<S, Set<Z>>create(newFStates, newTransitions, newEpsTransitions);

    }

    private LinkedHashSet<Transition<S, Set<Z>>> createPowerSetTransitions(
        final Transition<S, Z> transition,
        final Set<Set<Z>> powerSetStates) {
        final S funcSymbol = transition.getLhsFunctionSymbol();
        final int arity = funcSymbol.getArity();
        final LinkedHashSet<Transition<S, Set<Z>>> pSetTransitions =
            new LinkedHashSet<Transition<S, Set<Z>>>();

        final ArrayList<Set<Z>> orderedPowerSetStates = new ArrayList<Set<Z>>(powerSetStates);
        final int numberOfStates = orderedPowerSetStates.size();

        /* create for function symbol used in trans and every possible power set state parameters a new transition
         * iff the rhs of the new transition isn't the empty set
         */
        for (int i = 0; i < Math.pow(numberOfStates, arity); i++) {
            //generate next state parameters
            final ArrayList<Set<Z>> stateParameters = new ArrayList<Set<Z>>();
            int next = i;
            for (int j = 0; j < arity; j++) {
                stateParameters.add(orderedPowerSetStates.get(next % numberOfStates));
                next /= numberOfStates;
            }

            /* find the corresponding right hand side state for the current stateParameters
             * and the function symbol trans.getLhsFunctionSymbol()
             */
            final LinkedHashSet<Z> rhsState = new LinkedHashSet<Z>();
            for (final Transition<S, Z> trans : this.getTransitions()) {
                final S lhsFSymbol = trans.getLhsFunctionSymbol();
                if (lhsFSymbol.equals(funcSymbol) && lhsFSymbol.getArity() == funcSymbol.getArity()) {
                    int curIndex = 0;
                    boolean match = true;
                    /*
                     * decide whether trans "matches" the lhs of the current power set transition.
                     * Here "matches" means, that the state Parameters of trans are actually contained in the state-set-parameters
                     * of the power set transition to be created.
                     */
                    for (final Z state : trans.getLhsStateParameters()) {
                        if (!stateParameters.get(curIndex).contains(state)) {
                            match = false;
                        }
                        curIndex++;
                    }
                    if (match) {
                        rhsState.add(trans.getRhsState());
                    }
                }
            }

            if (!rhsState.isEmpty()) {
                final Transition<S, Set<Z>> pSetTrans =
                    new Transition<S, Set<Z>>(funcSymbol, ImmutableCreator.create(stateParameters), rhsState);
                pSetTransitions.add(pSetTrans);
            }

        }
        return pSetTransitions;
    }

    /**
     * Returns a TreeAutomaton which accepts the same language as this without
     * epsilon transitions.
     */
    public TreeAutomaton<S, Z> removeEpsTransitions() {
        Set<Transition<S, Z>> newTransitions = new LinkedHashSet<Transition<S, Z>>();
        for (Transition<S, Z> trans : this.getTransitions()) {
            for (Z rhsState : this.epsTransClosure(trans.getRhsState())) {
                Transition<S, Z> newTrans =
                    Transition.<S, Z>create(trans.getLhsFunctionSymbol(), trans.getLhsStateParameters(), rhsState);
                newTransitions.add(newTrans);
            }
        }
        return TreeAutomaton.<S, Z>create(this.getFinalStates(), newTransitions);
    }

    private LinkedHashSet<Set<Z>> createPowerSetFStates(final Set<Z> oldFinalStates, final Set<Set<Z>> pSetStates) {
        final LinkedHashSet<Set<Z>> accessiblePowFStates = new LinkedHashSet<Set<Z>>();
        for (final Set<Z> pSetState : pSetStates) {
            for (final Z oldFState : oldFinalStates) {
                if (pSetState.contains(oldFState)) {
                    accessiblePowFStates.add(pSetState);
                }
            }
        }
        return accessiblePowFStates;
    }

    /*
     * Returns a Set consisting of the param state and every other state that can be reached from this state through epsilon transitions.
     */
    public Set<Z> epsTransClosure(Z state) {
        Set<Z> reachedStates = new LinkedHashSet<Z>();
        Set<Z> newReachedStates = new LinkedHashSet<Z>();
        newReachedStates.add(state);
        while (!newReachedStates.isEmpty()) {
            reachedStates.addAll(newReachedStates);
            Set<Z> copyOfNewReachedStates = new LinkedHashSet<Z>(newReachedStates);
            newReachedStates.clear();
            for (Z reachedState : copyOfNewReachedStates) {
                Set<Z> epsReachableStates = this.epsTransitions.get(reachedState);
                if (epsReachableStates != null) {
                    for (Z epsReachableState : epsReachableStates) {
                        if (!reachedStates.contains(epsReachableState)) {
                            newReachedStates.add(epsReachableState);
                        }
                    }

                }
            }
        }
        return reachedStates;
    }
}
