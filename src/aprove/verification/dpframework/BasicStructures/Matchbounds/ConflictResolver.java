package aprove.verification.dpframework.BasicStructures.Matchbounds;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Matchbounds.TRSBoundsHelper.*;
import aprove.verification.dpframework.BasicStructures.Matchbounds.TRSBoundsTA.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.TreeAutomaton.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class ConflictResolver {

    private Map<TRSTerm, Integer> stateMap;
    private int nextNewState;
    private BijectiveStateToPowStateMapper sTPS;
    private final TRSFunctionApplication uniqueConstant;

    public ConflictResolver(Integer nextNewState, BijectiveStateToPowStateMapper sTPS, FunctionSymbolGenerator funcSymbGen) {
        this.nextNewState = nextNewState;
        this.sTPS = sTPS;
        this.stateMap = new LinkedHashMap<TRSTerm, Integer>();
        FunctionSymbol constSymb = funcSymbGen.getFresh("#-", 0);
        this.uniqueConstant = TRSTerm.createFunctionApplication(constSymb, new ArrayList<TRSTerm>());
    }

    public int getNextNewState() {
        return this.nextNewState;
    }

    public void setNextNewState(int state) {
        this.nextNewState = state;
    }

    public ImmutableMap<TRSTerm, Integer> getStateMap() {
        return ImmutableCreator.create(this.stateMap);
    }

    public void putToStateMap(TRSTerm t, Integer state) {
        this.stateMap.put(t, state);
    }

    public Pair<Set<Transition<FunctionSymbol, Integer>>, Map<Integer, Set<Integer>>> resolveConflict(TreeAutomaton<FunctionSymbol, Integer> A,
                    Conflict c, Abortion aborter) throws AbortionException {
        aborter.checkAbortion();
        TRSTerm t = c.getTerm();
        StateSubstitution<Integer> sigma = c.getStateSubstitution();
        Rule evokingRule = c.getEvokingRule();
        int targetState = c.getTargetState();

        Set<Transition<FunctionSymbol, Integer>> resolvingTransitions = new LinkedHashSet<Transition<FunctionSymbol, Integer>>();
        Map<Integer, Set<Integer>> epsTransitions = new LinkedHashMap<Integer, Set<Integer>>();
        if (t.isVariable()) {
            // if t is a variable, we resolve this conflict by adding a epsilon transition from the state given by sigma to the targetState
            if (!A.evaluate(t, sigma).contains(targetState)) {
                LinkedHashSet<Integer> newEpsTransRhs = new LinkedHashSet<Integer>();
                newEpsTransRhs.add(targetState);
                epsTransitions.put(sigma.getMap().get(t), newEpsTransRhs);
            }
            return new Pair<Set<Transition<FunctionSymbol, Integer>>, Map<Integer, Set<Integer>>>(resolvingTransitions, epsTransitions);
        } else {
            TRSFunctionApplication fA = (TRSFunctionApplication) t;
            FunctionSymbol rootSymbol = fA.getRootSymbol();
            List<Integer> stateArgsForRoot = new ArrayList<Integer>();
            List<TRSTerm> rootArguments = fA.getArguments();

            int argNumber = 0;
            for (TRSTerm arg : rootArguments) {
                Integer stateForArg;
                if (arg.isVariable()) {
                    TRSVariable x = (TRSVariable) arg;
                    stateForArg = sigma.getMap().get(x);
                } else {

                    TRSTerm transformedArg = this.getTermRepresentation(arg, rootSymbol, argNumber);
                    stateForArg = this.stateMap.get(transformedArg);

                    if (stateForArg == null) {

                        this.stateMap.put(transformedArg, this.nextNewState);
                        this.updateSTPS();
                        stateForArg = this.nextNewState;
                        this.nextNewState++;
                    }

                    Conflict newConflict = new Conflict(arg, sigma, stateForArg, evokingRule);
                    Pair<Set<Transition<FunctionSymbol, Integer>>, Map<Integer, Set<Integer>>> transToResNewConflict = this.resolveConflict(A,
                        newConflict, aborter);
                    resolvingTransitions.addAll(transToResNewConflict.x);
                    epsTransitions = TreeAutomatonHelper.<Integer> unionEpsTransitions(epsTransitions, transToResNewConflict.y);
                }

                stateArgsForRoot.add(stateForArg);

                argNumber++;
            }

            Integer stateForRoot = targetState;

            Transition<FunctionSymbol, Integer> newTrans = Transition.<FunctionSymbol, Integer> create(rootSymbol, stateArgsForRoot, stateForRoot);
            resolvingTransitions.add(newTrans);

        }
        return new Pair<Set<Transition<FunctionSymbol, Integer>>, Map<Integer, Set<Integer>>>(resolvingTransitions, epsTransitions);
    }

    private TRSTerm getTermRepresentation(TRSTerm arg, FunctionSymbol rootSymbol, int argNumber) {
        /*Term transformedArg = arg;
        if (!arg.isConstant() && arg.getDepth() >= 4) {
            Map<Variable, Term> subs = new LinkedHashMap<Variable, Term>();
            for (Variable x : arg.getVariables()) {
                subs.put(x, this.uniqueConstant);
            }
            BaseSubstitution sigma = Substitution.create(ImmutableCreator.create(subs));
            transformedArg = transformedArg.applySubstitution(sigma);
            Map<FunctionSymbol, FunctionSymbol> constToUniqueConst = new LinkedHashMap<FunctionSymbol, FunctionSymbol>();
            for (FunctionSymbol f : arg.getFunctionSymbols()) {
                if (f.getArity() == 0) {
                    constToUniqueConst.put(f, this.uniqueConstant.getRootSymbol());
                }
            }
            transformedArg = transformedArg.replaceAllFunctionSymbols(constToUniqueConst);
        }*/

        TRSTerm transformedArg = arg;
        if (!arg.isConstant()) {
            Map<TRSVariable, TRSTerm> subs = new LinkedHashMap<TRSVariable, TRSTerm>();
            for (TRSVariable x : arg.getVariables()) {
                subs.put(x, this.uniqueConstant);
            }
            Substitution sigma = TRSSubstitution.create(ImmutableCreator.create(subs));
            transformedArg = transformedArg.applySubstitution(sigma);

            TRSFunctionApplication transformedArgFA = (TRSFunctionApplication) transformedArg;
            ArrayList<TRSTerm> newArgArgs = new ArrayList<TRSTerm>();
            for (TRSTerm argArg : transformedArgFA.getArguments()) {
                TRSFunctionApplication argArgFA = (TRSFunctionApplication) argArg;
                newArgArgs.add(this.getWithUniqueConstArgs(argArgFA.getRootSymbol()));
            }

            transformedArg = TRSTerm.createFunctionApplication(transformedArgFA.getRootSymbol(), newArgArgs);

            /*Map<FunctionSymbol, FunctionSymbol> constToUniqueConst = new LinkedHashMap<FunctionSymbol, FunctionSymbol>();
            for (FunctionSymbol f : arg.getFunctionSymbols()) {
                if (f.getArity() == 0) {
                    constToUniqueConst.put(f, this.uniqueConstant.getRootSymbol());
                }
            }
            transformedArg = transformedArg.replaceAllFunctionSymbols(constToUniqueConst);*/
        }

        ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
        for (int i = 0; i < rootSymbol.getArity(); i++) {
            if (i == argNumber) {
                newArgs.add(transformedArg);
            } else {
                newArgs.add(this.uniqueConstant);
            }
        }

        TRSFunctionApplication argRepresentation = TRSTerm.createFunctionApplication(rootSymbol, newArgs);
        return argRepresentation;
    }

    private TRSTerm getWithUniqueConstArgs(FunctionSymbol f) {
        ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
        for (int i = 0; i < f.getArity(); i++) {
            newArgs.add(this.uniqueConstant);
        }

        return TRSTerm.createFunctionApplication(f, newArgs);
    }

    private void updateSTPS() {
        if (this.sTPS != null) {
            Set<Integer> initSTPS = new LinkedHashSet<Integer>();
            initSTPS.add(this.nextNewState);
            this.sTPS.set(this.nextNewState, initSTPS);
        }
    }
}
