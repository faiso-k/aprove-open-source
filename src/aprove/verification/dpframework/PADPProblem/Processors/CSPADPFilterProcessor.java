package aprove.verification.dpframework.PADPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.PADPProblem.*;
import aprove.verification.dpframework.PATRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * @author Stephan Falke
 * Tries to filter arguments of tuple symbols to make the problem TH-based on rhs.
 * @version $Id$
 */

@NoParams
public class CSPADPFilterProcessor extends CSPADPProcessor {

    @Override
    protected Result processCSPADP(CSPADPProblem cspadp, Abortion aborter) throws AbortionException {
        Set<FunctionSymbol> tups = cspadp.getTupleSymbols();
        Map<FunctionSymbol, FunctionSymbol> def_tup = cspadp.getDefTup();
        ImmutableMap<String, ImmutableList<String>> sortMap = cspadp.getSortMap();

        Map<FunctionSymbol, Set<Integer>> keepMap = new LinkedHashMap<FunctionSymbol, Set<Integer>>();

        Set<FunctionSymbol> pafuns = new LinkedHashSet<FunctionSymbol>();
        pafuns.add(FunctionSymbol.create("0", 0));
        pafuns.add(FunctionSymbol.create("1", 0));
        pafuns.add(FunctionSymbol.create("-", 1));
        pafuns.add(FunctionSymbol.create("+", 2));
        for (PARule dp : cspadp.getP()) {
            this.computeKeepMap(dp, def_tup, sortMap, keepMap, pafuns);
        }

        if (keepMap.keySet().isEmpty()) {
            return ResultFactory.unsuccessful();
        }

        Map<String, ImmutableList<String>> newSortMap = new LinkedHashMap<String, ImmutableList<String>>(sortMap);
        Map<FunctionSymbol, FunctionSymbol> newDefTup = new LinkedHashMap<FunctionSymbol, FunctionSymbol>(def_tup);
        Map<String, ImmutableSet<Integer>> newMu = new LinkedHashMap<String, ImmutableSet<Integer>>(cspadp.getMu());
        this.extendMaps(keepMap, newSortMap, newDefTup, newMu);

        Set<PARule> newP = this.getNewP(cspadp.getP(), keepMap);
        if (this.violatesVariableCondition(newP)) {
            return ResultFactory.unsuccessful();
        }

        Proof proof = new CSPADPFilterProof(keepMap);
        CSPATRSProblem dummy = CSPATRSProblem.create(cspadp.getR(), cspadp.getS(), cspadp.getE(), ImmutableCreator.create(newSortMap), ImmutableCreator.create(newMu));
        CSPADPProblem newCSPADP = CSPADPProblem.create(ImmutableCreator.create(newP), dummy, newDefTup);
        return ResultFactory.proved(newCSPADP, YNMImplication.SOUND, proof);
    }

    private boolean violatesVariableCondition(Collection<PARule> p) {
        for (PARule dp : p) {
            if (this.violatesVariableCondition(dp)) {
                return true;
            }
        }
        return false;
    }

    private boolean violatesVariableCondition(PARule dp) {
        return !dp.getLeft().getVariables().containsAll(dp.getRight().getVariables());
    }

    private Set<PARule> getNewP(Collection<PARule> p, Map<FunctionSymbol, Set<Integer>> keepMap) {
        Set<PARule> res = new LinkedHashSet<PARule>();
        for (PARule dp : p) {
            res.add(this.filter(dp, keepMap));
        }
        return res;
    }

    private PARule filter(PARule dp, Map<FunctionSymbol, Set<Integer>> keepMap) {
        TRSFunctionApplication newL = this.filter(dp.getLeft(), keepMap);
        TRSFunctionApplication newR = this.filter((TRSFunctionApplication) dp.getRight(), keepMap);
        ImmutableSet<PAConstraint> newC = this.filter(dp.getConstraint(), newL.getVariables());
        return PARule.create(newL, newR, newC);
    }

    private ImmutableSet<PAConstraint> filter(ImmutableSet<PAConstraint> cs, Set<TRSVariable> vars) {
        Set<PAConstraint> res = new LinkedHashSet<PAConstraint>();
        for (PAConstraint c : cs) {
            if (vars.containsAll(c.getVariables())) {
                res.add(c);
            }
        }
        return ImmutableCreator.create(res);
    }

    private TRSFunctionApplication filter(TRSFunctionApplication t, Map<FunctionSymbol, Set<Integer>> keepMap) {
        FunctionSymbol tup = t.getRootSymbol();
        Set<Integer> keepers = keepMap.get(tup);
        if (keepers == null) {
            return t;
        } else {
            FunctionSymbol newTup = FunctionSymbol.create(tup.getName(), keepers.size());
            ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
            int oldArr = tup.getArity();
            for (int i = 0; i < oldArr; i++) {
                if (keepers.contains(Integer.valueOf(i))) {
                    newArgs.add(t.getArgument(i));
                }
            }
            return TRSTerm.createFunctionApplication(newTup, ImmutableCreator.create(newArgs));
        }
    }

    private void extendMaps(Map<FunctionSymbol, Set<Integer>> keepMap, Map<String, ImmutableList<String>> sortMap, Map<FunctionSymbol, FunctionSymbol> def_tup, Map<String, ImmutableSet<Integer>> mu) {
        for (FunctionSymbol oldTup : keepMap.keySet()) {
            Set<Integer> keptArgs = keepMap.get(oldTup);
            int newArr = keptArgs.size();
            FunctionSymbol newTup = FunctionSymbol.create(oldTup.getName(), newArr);
            List<String> newSorts = this.getNewSorts(newArr + 1);
            sortMap.put(newTup.getName(), ImmutableCreator.create(newSorts));
            def_tup.put(newTup, newTup);
            int arr = oldTup.getArity();
            int j = 0;
            ImmutableSet<Integer> oldMu = mu.get(this.getDef(oldTup, def_tup).getName());
            Set<Integer> newMu = new LinkedHashSet<Integer>();
            for (int i = 0; i < arr; i++) {
                Integer ii = Integer.valueOf(i);
                if (keptArgs.contains(ii)) {
                    if (oldMu.contains(ii)) {
                        newMu.add(Integer.valueOf(j));
                    }
                    j++;
                }
            }
            mu.put(newTup.getName(), ImmutableCreator.create(newMu));
        }
    }

    private List<String> getNewSorts(int num) {
        List<String> res = new Vector<String>();
        for (int i = 0; i < num; i++) {
            res.add("int");
        }
        return res;
    }

    private void computeKeepMap(PARule dp, Map<FunctionSymbol, FunctionSymbol> def_tup, ImmutableMap<String, ImmutableList<String>> sortMap, Map<FunctionSymbol, Set<Integer>> keepMap, Set<FunctionSymbol> pafuns) {
        TRSFunctionApplication rhs = (TRSFunctionApplication) dp.getRight();
        FunctionSymbol tup = rhs.getRootSymbol();
        int arr = tup.getArity();
        List<String> fsorts = sortMap.get(this.getDef(tup, def_tup).getName());
        Set<Integer> keepers = new LinkedHashSet<Integer>();
        for (int i = 0; i < arr; i++) {
            if (fsorts.get(i).equals("int") && this.isPurePA(rhs.getArgument(i), pafuns)) {
                keepers.add(Integer.valueOf(i));
            }
        }
        int size = keepers.size();
        if (keepers.size() < arr) {
            // not keeping everything
            keepMap.put(tup, keepers);
        }
    }

    private boolean isPurePA(TRSTerm t, Set<FunctionSymbol> pafuns) {
        return pafuns.containsAll(t.getFunctionSymbols());
    }

    private FunctionSymbol getDef(FunctionSymbol f, Map<FunctionSymbol, FunctionSymbol> defTup) {
        for (FunctionSymbol g : defTup.keySet()) {
            if (f.equals(defTup.get(g))) {
                return g;
            }
        }
        return null;
    }

    /***************************************************************/
    private static class CSPADPFilterProof extends Proof.DefaultProof {

        private Map<FunctionSymbol, Set<Integer>> keepMap;

        private CSPADPFilterProof(Map<FunctionSymbol, Set<Integer>> keepMap) {
            this.keepMap = keepMap;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            result.append("For the following tuple symbols, only some arguments are retained:");
            result.append(o.linebreak());
            Set<String> tmp = new LinkedHashSet<String>();
            for (Map.Entry<FunctionSymbol, ? extends Set<Integer>> keepEntry : this.keepMap.entrySet()) {
                Set<Integer> keep = keepEntry.getValue();
                ArrayList<Integer> shiftSet = new ArrayList<Integer>(keep.size());
                for (Integer i : keep) {
                    shiftSet.add(i + 1);
                }
                tmp.add(keepEntry.getKey().getName() + ": " + o.set(shiftSet, Export_Util.SIMPLESET));
            }
            result.append(o.set(tmp, Export_Util.RULES));
            result.append(o.linebreak());
            return result.toString();
        }

    }

}
