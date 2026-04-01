package aprove.verification.dpframework.BasicStructures.Matchbounds;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Matchbounds.TRSBoundsHelper.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.TreeAutomaton.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Contains some functions/classes which are used for conflict resolving.
 * @author Marcel Klinzing
 */
public class TRSBoundsCRHelper {

    protected static class KMSContext {
        private TRSTerm t;
        private StateSubstitution<Integer> sigma;
        private Set<Position> positions;

        public KMSContext(TRSTerm t, StateSubstitution<Integer> sigma, Set<Position> positions) {
            if (Globals.useAssertions) {
                assert (t.getPositions().containsAll(positions));
            }
            this.sigma = sigma;
            this.positions = positions;
            this.t = t;
        }

        @Override
        public String toString() {
            return "KMSContext [positions=" + this.positions + ", sigma=" + this.sigma + ", t=" + this.t + "]";
        }
    }

    protected static Set<Pair<List<StateSubstTerm>, List<Integer>>> computeKMSContexts(TreeAutomaton<FunctionSymbol, Integer> A, Conflict c) {
        Set<Pair<List<StateSubstTerm>, List<Integer>>> kmsContexts = new LinkedHashSet<Pair<List<StateSubstTerm>, List<Integer>>>();
        Set<Pair<TRSBoundsCRHelper.KMSContext, Map<Position, Integer>>> outerContexts = TRSBoundsCRHelper.computeOuterContexts(A, c);

        for (Pair<TRSBoundsCRHelper.KMSContext, Map<Position, Integer>> kmsOutCon : outerContexts) {
            Pair<List<StateSubstTerm>, List<Integer>> kmsContext = TRSBoundsCRHelper.computeInnerContexts(A, c, kmsOutCon);
            kmsContexts.add(kmsContext);

            if (Globals.useAssertions) {
                assert (kmsContext.getKey().size() == kmsContext.getValue().size());
            }
        }

        return kmsContexts;
    }

    /*
     * Computes minimal contexts D_1[t_1, ..., t_i], ... , D_n[t_j, ..., t_m] so that C[D_1[t_1, ..., t_i], ... , D_n[t_j, ..., t_m]] --> c.getTargetState() and
     * t_1 --> q_1 ... t_i --> q_i ... t_j --> q_j ... t_m --> q_m for the outer context kmsOutCon.
     */
    protected static Pair<List<StateSubstTerm>, List<Integer>> computeInnerContexts(TreeAutomaton<FunctionSymbol, Integer> A, Conflict c,
                    Pair<TRSBoundsCRHelper.KMSContext, Map<Position, Integer>> kmsOutCon) {

        StateSubstitution<Integer> sigma = c.getStateSubstitution();
        List<StateSubstTerm> innerContexts = new ArrayList<StateSubstTerm>();
        List<Integer> targetStates = new ArrayList<Integer>();

        for (Map.Entry<Position, Integer> entry : kmsOutCon.getValue().entrySet()) {
            Position pos = entry.getKey();
            Integer targetState = entry.getValue();
            TRSTerm t = c.getTerm().getSubterm(pos);
            StateSubstTerm innerCon = TRSBoundsCRHelper.computeInnerContext(A, t, sigma, new VariableGenerator(t.getVariables()));
            innerContexts.add(innerCon);
            targetStates.add(targetState);

        }
        return new Pair<List<StateSubstTerm>, List<Integer>>(innerContexts, targetStates);
    }

    protected static StateSubstTerm computeInnerContext(TreeAutomaton<FunctionSymbol, Integer> A, TRSTerm t, StateSubstitution<Integer> sigma,
                    VariableGenerator varGen) {
        StateSubstTerm innerContext;
        Set<Integer> evaluatedToStates = A.evaluate(t, sigma);
        if (t.isVariable()) {
            innerContext = new StateSubstTerm(t, sigma);
        } else if (evaluatedToStates.isEmpty()) {
            if (t.isConstant()) {
                innerContext = new StateSubstTerm(t, sigma);
            } else {
                TRSFunctionApplication fA = (TRSFunctionApplication) t;
                FunctionSymbol root = fA.getRootSymbol();
                for (int i = 0; i < root.getArity(); i++) {
                    Position curPos = Position.create(i);
                    StateSubstTerm res = TRSBoundsCRHelper.computeInnerContext(A, t.getSubterm(curPos), sigma, varGen);
                    t = t.replaceAt(curPos, res.getT());
                    sigma = res.getSigma();
                }
                innerContext = new StateSubstTerm(t, sigma);
            }
        } else {
            TRSVariable x = varGen.getFresh("x");
            Map<TRSVariable, Integer> newStateSubsMap = new LinkedHashMap<TRSVariable, Integer>(sigma.getMap());
            newStateSubsMap.put(x, evaluatedToStates.iterator().next());
            sigma = StateSubstitution.<Integer> create(newStateSubsMap);
            innerContext = new StateSubstTerm(x, sigma);
        }
        return innerContext;
    }

    /*
     *  Computes all Contexts C and a map from the positions of C to State q_1, ..., q_n, so that C[t_1,...,t_n] = c.getTerm() and C[q_1, ..., q_n] --> c.getTargetState().
     */
    protected static Set<Pair<TRSBoundsCRHelper.KMSContext, Map<Position, Integer>>> computeOuterContexts(TreeAutomaton<FunctionSymbol, Integer> A, Conflict c) {
        TRSTerm t = c.getTerm();
        // This set will contain those positions of t which have to be checked as context possible context leaf positions
        Set<Position> possibleBoxPositions = new LinkedHashSet<Position>();
        Set<FunctionSymbol> functionSymbolsOfA = A.getAllFunctionSymbols();
        Set<Position> leafPositions = new LinkedHashSet<Position>();

        //compute leaf Positions of t
        for (Position pos : t.getPositions()) {
            TRSTerm sub = t.getSubterm(pos);
            if (sub.isVariable() || sub.isConstant()) {
                leafPositions.add(pos);
            }
        }

        // compute possibleBoxPositions
        for (Position pos : leafPositions) {
            Position actPos = Position.create();
            for (int i : pos) {
                actPos = actPos.append(i);
                TRSTerm sub = t.getSubterm(actPos);
                if (!sub.isVariable()) {
                    TRSFunctionApplication fA = (TRSFunctionApplication) t;
                    if (functionSymbolsOfA.contains(fA.getRootSymbol())) {
                        possibleBoxPositions.add(actPos);
                    } else {
                        break;
                    }
                }

            }
        }

        // The root position of the term has to be always in  possibleBoxPositions
        possibleBoxPositions.add(Position.create(new int[0]));

        Set<Set<Position>> powPositions = TreeAutomatonHelper.powerSet(possibleBoxPositions);
        powPositions.remove(new LinkedHashSet<Position>());
        Set<Set<Position>> indPositions = new LinkedHashSet<Set<Position>>();

        // only sets conteaining independent position pi_1,... pi_n have to be checked, if C[q_1]_pi_1 ... [q_n]_pi_n
        // can be evaluated to c.getTargetState()
        for (Set<Position> s : powPositions) {
            List<Position> orderedPositions = new ArrayList<Position>(s);
            boolean independent = true;
            for (int i = 0; i < orderedPositions.size() && independent; i++) {
                Position pos1 = orderedPositions.get(i);
                for (int j = i + 1; j < orderedPositions.size() && independent; j++) {
                    Position pos2 = orderedPositions.get(j);
                    if (!pos1.isIndependent(pos2)) {
                        independent = false;
                    }
                }
            }

            if (independent) {
                indPositions.add(s);
            }
        }
        return TRSBoundsCRHelper.computeOuterContexts(A, c, indPositions);
    }

    /*
     * computes Contexts C and a map from the positions of C to State q_1, ..., q_n, so that C[t_1,...,t_n] = c.getTerm() and C[q_1, ..., q_n] --> c.getTargetState() by
     * testing the Positions of the argument possiblePositions.
     */
    protected static Set<Pair<TRSBoundsCRHelper.KMSContext, Map<Position, Integer>>> computeOuterContexts(TreeAutomaton<FunctionSymbol, Integer> A, Conflict c,
                    Set<Set<Position>> possiblePositions) {
        Set<Pair<TRSBoundsCRHelper.KMSContext, Map<Position, Integer>>> con_states_pairs = new LinkedHashSet<Pair<TRSBoundsCRHelper.KMSContext, Map<Position, Integer>>>();
        TRSTerm t = c.getTerm();
        StateSubstitution<Integer> sigma = c.getStateSubstitution();
        Integer targetState = c.getTargetState();
        Set<Integer> allStates = A.getAllStates();
        for (Set<Position> positions : possiblePositions) {
            int numberOfPositions = positions.size();
            int numberOfAllStates = allStates.size();
            List<Integer> orderedStates = new ArrayList<Integer>(allStates);
            for (int i = 0; i < Math.pow(numberOfAllStates, numberOfPositions); i++) {
                Map<Position, Integer> posStateMap = new LinkedHashMap<Position, Integer>();
                VariableGenerator varGen = new VariableGenerator(t.getVariables());
                TRSTerm sub = t;
                Map<TRSVariable, Integer> newSigma = new LinkedHashMap<TRSVariable, Integer>(sigma.getMap());
                int next = i;
                for (Position pos : positions) {
                    int state = orderedStates.get(next % numberOfAllStates);
                    next /= numberOfAllStates;
                    TRSVariable x = varGen.getFresh("x" + i);
                    sub = sub.replaceAt(pos, x);
                    posStateMap.put(pos, state);
                    newSigma.put(x, state);
                }
                Set<Integer> evalStates = A.evaluate(sub, StateSubstitution.<Integer> create(newSigma));
                if (evalStates.contains(targetState)) {
                    TRSBoundsCRHelper.KMSContext kmsContext = new TRSBoundsCRHelper.KMSContext(t, sigma, positions);
                    con_states_pairs.add(new Pair<TRSBoundsCRHelper.KMSContext, Map<Position, Integer>>(kmsContext, posStateMap));
                }
            }
        }

        return con_states_pairs;
    }

}
