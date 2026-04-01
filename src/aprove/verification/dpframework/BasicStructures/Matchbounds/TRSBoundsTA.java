package aprove.verification.dpframework.BasicStructures.Matchbounds;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.TreeAutomaton.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Marcel Klinzing
 */
public class TRSBoundsTA {

    protected static class BijectiveStateToPowStateMapper {
        Map<Set<Integer>, Integer> powStateToState;
        Map<Integer, Set<Integer>> stateToPowState;

        public Map<Set<Integer>, Integer> getPowStateToState() {
            return this.powStateToState;
        }

        public void setPowStateToState(final Map<Set<Integer>, Integer> powStateToState) {
            this.powStateToState = powStateToState;
        }

        public Map<Integer, Set<Integer>> getStateToPowState() {
            return this.stateToPowState;
        }

        public void setStateToPowState(final Map<Integer, Set<Integer>> stateToPowState) {
            this.stateToPowState = stateToPowState;
        }

        public BijectiveStateToPowStateMapper() {
            this.powStateToState = new LinkedHashMap<Set<Integer>, Integer>();
            this.stateToPowState = new LinkedHashMap<Integer, Set<Integer>>();
        }

        public Set<Integer> getPowState(final int state) {
            return this.stateToPowState.get(state);
        }

        public Integer getState(final Set<Integer> powState) {
            return this.powStateToState.get(powState);
        }

        public void set(final Integer state, final Set<Integer> powState) {
            if (!this.stateToPowState.containsKey(state)) {
                this.stateToPowState.put(state, powState);
                this.powStateToState.put(powState, state);
            }
        }
    }

    protected static class QuasiDeterministicTA {
        TreeAutomaton<FunctionSymbol, Integer> A;
        ImmutableSet<Transition<FunctionSymbol, Integer>> detTrans;
        Map<Integer, Set<Integer>> detEpsTransitions;

        public QuasiDeterministicTA(final TreeAutomaton<FunctionSymbol, Integer> A,
                final ImmutableSet<Transition<FunctionSymbol, Integer>> detTrans,
                final Map<Integer, Set<Integer>> detEpsTransitions) {
            this.A = A;
            this.detTrans = detTrans;
            this.detEpsTransitions = detEpsTransitions;
        }

        public ImmutableSet<Integer> getFinalStates() {
            return this.A.getFinalStates();
        }

        public ImmutableSet<Transition<FunctionSymbol, Integer>> getDetTransitions() {
            return this.detTrans;
        }

        public TreeAutomaton<FunctionSymbol, Integer> getDetAutomaton() {
            return new TreeAutomaton<>(this.getDetFinalStates(), this.getDetTransitions(), this.getDetEpsTransitions());
        }

        public Set<Integer> detEvaluate(final TRSTerm t, final StateSubstitution<Integer> sigma) {
            final TreeAutomaton<FunctionSymbol, Integer> detA =
                TreeAutomaton.<FunctionSymbol, Integer>create(this.A.getFinalStates(), this.detTrans,
                    this.detEpsTransitions);
            return detA.evaluate(t, sigma);
        }

        public TreeAutomaton<FunctionSymbol, Integer> getTA() {
            return this.A;
        }

        public static QuasiDeterministicTA create(final Set<Integer> finalStates,
            final Set<Transition<FunctionSymbol, Integer>> transitions,
            final Map<Integer, Set<Integer>> epsTrans,
            final Set<Transition<FunctionSymbol, Integer>> detTransitions,
            final Map<Integer, Set<Integer>> detEpsTransitions) {
            final ImmutableSet<Transition<FunctionSymbol, Integer>> iDetTrans = ImmutableCreator.create(detTransitions);
            return new QuasiDeterministicTA(TreeAutomaton.<FunctionSymbol, Integer>create(finalStates, transitions,
                epsTrans), iDetTrans, detEpsTransitions);
        }

        public static QuasiDeterministicTA create(final Set<Integer> finalStates,
            final Set<Transition<FunctionSymbol, Integer>> transitions,
            final Set<Transition<FunctionSymbol, Integer>> detTransitions,
            final Map<Integer, Set<Integer>> detEpsTransitions) {
            final ImmutableSet<Transition<FunctionSymbol, Integer>> iDetTrans = ImmutableCreator.create(detTransitions);
            return new QuasiDeterministicTA(TreeAutomaton.<FunctionSymbol, Integer>create(finalStates, transitions),
                iDetTrans, detEpsTransitions);
        }

        @Override
        public String toString() {
            return "QuasiDeterministicTA [A=" + this.A + ", detEpsTransitions=" + this.detEpsTransitions
                + ", detTrans=" + this.detTrans + "]";
        }

        public ImmutableSet<Transition<FunctionSymbol, Integer>> getTransitions() {
            return this.A.getTransitions();
        }

        public Set<Integer> evaluate(final TRSTerm t, final StateSubstitution<Integer> sigma) {
            return this.A.evaluate(t, sigma);
        }

        public ImmutableMap<Integer, Set<Integer>> getEpsTransitions() {
            return this.A.getEpsTransitions();
        }

        public ImmutableMap<Integer, Set<Integer>> getDetEpsTransitions() {
            return ImmutableCreator.create(this.detEpsTransitions);
        }

        public ImmutableSet<Integer> getDetFinalStates() {
            final Set<Integer> detFStates = new LinkedHashSet<Integer>();
            final TreeAutomaton<FunctionSymbol, Integer> detA =
                TreeAutomaton.<FunctionSymbol, Integer>create(new LinkedHashSet<Integer>(), this.detTrans,
                    this.detEpsTransitions);
            for (final Integer state : detA.getAllStates()) {
                if (this.A.getFinalStates().contains(state)) {
                    detFStates.add(state);
                }
            }
            return ImmutableCreator.create(detFStates);
        }

        public Set<FunctionSymbol> getAllFunctionSymbols() {
            final Set<FunctionSymbol> detSymbols = new LinkedHashSet<FunctionSymbol>();
            for (final Transition<FunctionSymbol, Integer> trans : this.detTrans) {
                detSymbols.add(trans.getLhsFunctionSymbol());
            }
            return detSymbols;
        }
    }

    /*
     * If there is a transition f(q_1,...,q_i,...,q_n) -> q_f and q_i represents a power set state p = {p_1,...,p_m}  and there is a state
     * r = {p_1,...,p_m,..} which is a proper superset of p in the param newPosStates, then a transition f(q_1,...,r,...,q_n) -> q*_f
     * is returned where q*_f is computed over the param set "transitions"
     */
    protected static LinkedHashSet<Transition<FunctionSymbol, Set<Integer>>> getSubsumeTransitions(final FunctionSymbol f,
        final Set<Set<Integer>> newPowStates,
        final Set<Transition<FunctionSymbol, Integer>> transitions,
        final BijectiveStateToPowStateMapper sTPS) {
        final FunctionSymbol funcSymbol = f;
        final LinkedHashSet<Transition<FunctionSymbol, Set<Integer>>> pSetTransitions =
            new LinkedHashSet<Transition<FunctionSymbol, Set<Integer>>>();
        for (final Set<Integer> newPowState : newPowStates) {
            for (int argNumber = 0; argNumber < f.getArity(); argNumber++) {

                /*
                 * find the corresponding right hand side state for the current stateParameters
                 */
                final Map<ArrayList<Set<Integer>>, Set<Integer>> stateParamsToRhsState =
                    new LinkedHashMap<ArrayList<Set<Integer>>, Set<Integer>>();
                for (final Transition<FunctionSymbol, Integer> trans : transitions) {
                    final FunctionSymbol lhsFSymbol = trans.getLhsFunctionSymbol();
                    if (lhsFSymbol.equals(funcSymbol) && lhsFSymbol.getArity() == funcSymbol.getArity()) {
                        final ArrayList<Set<Integer>> stateParameters = new ArrayList<Set<Integer>>();
                        final Set<Integer> powStateParam =
                            sTPS.getPowState(trans.getLhsStateParameters().get(argNumber));
                        if (newPowState.containsAll(powStateParam) && newPowState.size() != powStateParam.size()) {
                            int index = 0;
                            for (final Integer state : trans.getLhsStateParameters()) {
                                if (argNumber == index) {
                                    stateParameters.add(newPowState);
                                } else {
                                    stateParameters.add(sTPS.getPowState(state));
                                }
                                index++;
                            }
                            Set<Integer> rhsState = stateParamsToRhsState.get(stateParameters);
                            if (rhsState == null) {
                                rhsState = new LinkedHashSet<Integer>();
                            }
                            rhsState.addAll(sTPS.getPowState(trans.getRhsState()));
                            stateParamsToRhsState.put(stateParameters, rhsState);
                        }
                    }
                }

                for (final Map.Entry<ArrayList<Set<Integer>>, Set<Integer>> entry : stateParamsToRhsState.entrySet()) {
                    final Transition<FunctionSymbol, Set<Integer>> pSetTrans =
                        new Transition<FunctionSymbol, Set<Integer>>(funcSymbol,
                            ImmutableCreator.create(entry.getKey()), entry.getValue());
                    pSetTransitions.add(pSetTrans);
                }

            }
        }

        return pSetTransitions;
    }

    protected static LinkedHashSet<Set<Integer>> createPowerSetFStates(final ImmutableSet<Integer> finalStates,
        final Set<Set<Integer>> allPowStates) {
        final LinkedHashSet<Set<Integer>> accessiblePowFStates = new LinkedHashSet<Set<Integer>>();
        for (final Set<Integer> pSetState : allPowStates) {
            for (final Integer oldFState : finalStates) {
                if (pSetState.contains(oldFState)) {
                    accessiblePowFStates.add(pSetState);
                }
            }
        }
        return accessiblePowFStates;
    }

    protected static Transition<FunctionSymbol, Integer> powTransToTrans(final Transition<FunctionSymbol, Set<Integer>> powerSetTrans,
        final BijectiveStateToPowStateMapper sTPS) {
        final List<Integer> newStateParams = new ArrayList<Integer>();
        for (final Set<Integer> powState : powerSetTrans.getLhsStateParameters()) {
            newStateParams.add(sTPS.getState(powState));
        }
        final int rhsState = sTPS.getState(powerSetTrans.getRhsState());
        return Transition.<FunctionSymbol, Integer>create(powerSetTrans.getLhsFunctionSymbol(), newStateParams,
            rhsState);
    }

    /*
     * Computes all possible state substitutions sigma such that (lhs sigma) --> targetState with transitions of A.
     * Returns an empty set iff there is noch such an sigma. Note that if t has no variables but t --> targetState
     * then this method will return an Set consisting of an empty stateSubstitution.
     */
    public static Set<StateSubstitution<Integer>> createStateSubstitutions(final TreeAutomaton<FunctionSymbol, Integer> A,
        final TRSTerm t,
        final Integer targetState,
        final Set<Integer> possibleVarAlloc) {
        final Set<StateSubstitution<Integer>> stateSubstitutions = new LinkedHashSet<StateSubstitution<Integer>>();

        final TreeAutomaton<FunctionSymbol, Integer> AWithRevEpsTranss =
            TreeAutomaton.<FunctionSymbol, Integer>create(A.getFinalStates(), A.getTransitions(),
                A.getReversedEpsTransitions());

        final Set<Set<Pair<TRSVariable, Integer>>> solutions =
            TRSBoundsTA.solveStateSubstitutions(AWithRevEpsTranss, t, targetState, possibleVarAlloc);
        for (final Set<Pair<TRSVariable, Integer>> sol : solutions) {
            boolean isSolution = true;
            final Map<TRSVariable, Integer> stateSubs = new LinkedHashMap<TRSVariable, Integer>();
            for (final Pair<TRSVariable, Integer> varMapping : sol) {
                final Integer assignedState = stateSubs.get(varMapping.getKey());
                if (assignedState == null) {
                    stateSubs.put(varMapping.getKey(), varMapping.getValue());
                } else {
                    if (!assignedState.equals(varMapping.getValue())) {
                        isSolution = false;
                        break;
                    }
                }
            }

            if (isSolution) {
                stateSubstitutions.add(StateSubstitution.<Integer>create(stateSubs));
            }
        }

        return stateSubstitutions;
    }

    private static Set<Set<Pair<TRSVariable, Integer>>> solveStateSubstitutions(final TreeAutomaton<FunctionSymbol, Integer> AWithRevEpsTranss,
        final TRSTerm t,
        final Integer state,
        final Set<Integer> possibleVarAlloc) {
        final Set<Set<Pair<TRSVariable, Integer>>> solutions = new LinkedHashSet<Set<Pair<TRSVariable, Integer>>>();
        /*
         * We can evaluate t to a state q iff we can evaluate t to some state p and p --> ... --> q.
         */
        final Set<Integer> targetStates = AWithRevEpsTranss.epsTransClosure(state);
        if (t.isVariable()) {
            for (final Integer targetState : targetStates) {
                if (possibleVarAlloc.contains(targetState)) {
                    final Set<Pair<TRSVariable, Integer>> solution = new LinkedHashSet<Pair<TRSVariable, Integer>>();
                    solution.add(new Pair<TRSVariable, Integer>((TRSVariable) t, targetState));
                    solutions.add(solution);
                }
            }
        } else {
            final TRSFunctionApplication fA = (TRSFunctionApplication) t;

            for (final Transition<FunctionSymbol, Integer> trans : AWithRevEpsTranss.getTransitions()) {
                if (targetStates.contains(trans.getRhsState())
                    && fA.getRootSymbol().equals(trans.getLhsFunctionSymbol())) {
                    final Set<Set<Pair<TRSVariable, Integer>>> solution =
                        TRSBoundsTA.solveStateSubstitutions(
                            AWithRevEpsTranss,
                            fA,
                            new Pair<FunctionSymbol, List<Integer>>(trans.getLhsFunctionSymbol(),
                                trans.getLhsStateParameters()), possibleVarAlloc);
                    solutions.addAll(solution);
                }
            }
        }
        return solutions;

    }

    /*
     * Computes with which stateSubstitutions we get from f(t_1,...,t_n) to f(q_1,...,q_n), where q_1,...,q_n are states of A.
     */
    private static Set<Set<Pair<TRSVariable, Integer>>> solveStateSubstitutions(final TreeAutomaton<FunctionSymbol, Integer> AWithRevEpsTranss,
        final TRSFunctionApplication fA,
        final Pair<FunctionSymbol, List<Integer>> rhs,
        final Set<Integer> possibleVarAlloc) {
        final Set<Set<Pair<TRSVariable, Integer>>> solutions = new LinkedHashSet<Set<Pair<TRSVariable, Integer>>>();
        solutions.add(new LinkedHashSet<Pair<TRSVariable, Integer>>());

        if (!fA.isConstant()) {
            int index = 0;
            for (final TRSTerm arg : fA.getArguments()) {
                // we get from fA to rhs if all arguments of fA can be avaluated to the corresponding state in rhs
                final Set<Set<Pair<TRSVariable, Integer>>> disjSolution =
                    TRSBoundsTA.solveStateSubstitutions(AWithRevEpsTranss, arg, rhs.getValue().get(index), possibleVarAlloc);
                index++;
                if (disjSolution.isEmpty()) {
                    solutions.clear();
                    return solutions;
                }
                // All solutions for the argument are given in disjunctive normal form; we have to compute the
                // "new" disjunctive normal form since we want to combine these solutions with a logical and, i.e.:
                // build the cross product for current known solutions and the computed solutions for this argument
                final Set<Set<Pair<TRSVariable, Integer>>> oldSolutions =
                    new LinkedHashSet<Set<Pair<TRSVariable, Integer>>>(solutions);
                for (final Set<Pair<TRSVariable, Integer>> solution : oldSolutions) {
                    solutions.remove(solution);
                    for (final Set<Pair<TRSVariable, Integer>> disj : disjSolution) {
                        final Set<Pair<TRSVariable, Integer>> sol = new LinkedHashSet<Pair<TRSVariable, Integer>>(solution);
                        for (final Pair<TRSVariable, Integer> lit : disj) {
                            sol.add(lit);
                        }
                        solutions.add(sol);
                    }

                }

            }
        }
        return solutions;
    }
}
