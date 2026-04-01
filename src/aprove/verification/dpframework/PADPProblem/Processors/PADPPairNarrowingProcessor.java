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
import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */

@NoParams
public class PADPPairNarrowingProcessor extends PADPProcessor {

    @Override
    protected Result processPADP(PADPProblem padp, Abortion aborter) throws AbortionException {
        CollectionNameProvider paFuns = PATRSPredefinedNames.getNameProvider();
        ImmutableMap<String, ImmutableList<String>> sortMap = padp.getSortMap();
        Map<FunctionSymbol, FunctionSymbol> def_tup = padp.getDefTup();
        Set<PARule> p = new LinkedHashSet<PARule>(padp.getP());

        PARule oldRule = null;
        Set<PARule> newRules = null;

        for (PARule dp : p) {
            newRules = this.getNewRules(dp, p, paFuns, sortMap, def_tup);
            if (newRules != null) {
                oldRule = dp;
                break;
            }
        }

        if (newRules == null) {
            return ResultFactory.unsuccessful();
        }

        p.remove(oldRule);
        p.addAll(newRules);
        if (p.equals(padp.getP())) {
            return ResultFactory.unsuccessful();
        }
        Proof proof = new PADPPairNarrowingProof(oldRule, newRules);
        PADPProblem newPADP = PADPProblem.create(ImmutableCreator.create(p), padp.getPATRS(), padp.getDefTup());
        return ResultFactory.proved(newPADP, YNMImplication.EQUIVALENT, proof);
    }

    private boolean hasDistinctVars(Set<PARule> dps) {
        Set<TRSVariable> seenVars = new LinkedHashSet<TRSVariable>();
        for (PARule dp : dps) {
            seenVars.clear();
            for (TRSTerm t : dp.getLeft().getArguments()) {
                if (!t.isVariable() || seenVars.contains((TRSVariable) t)) {
                    return false;
                }
                seenVars.add((TRSVariable) t);
            }
        }
        return true;
    }

    private ImmutableList<String> getSort(FunctionSymbol f, ImmutableMap<String, ImmutableList<String>> sortMap, Map<FunctionSymbol, FunctionSymbol> def_tup) {
        ImmutableList<String> res = sortMap.get(f.getName());
        if (res == null) {
            res = sortMap.get(this.getDef(f, def_tup).getName());
        }
        return res;
    }

    private FunctionSymbol getDef(FunctionSymbol f, Map<FunctionSymbol, FunctionSymbol> def_tup) {
        for (FunctionSymbol g : def_tup.keySet()) {
            if (def_tup.get(g).equals(f)) {
                return g;
            }
        }
        return null;
    }

    private boolean isIntSorted(FunctionSymbol f, ImmutableMap<String, ImmutableList<String>> sortMap, Map<FunctionSymbol, FunctionSymbol> def_tup) {
        ImmutableList<String> sorts = this.getSort(f, sortMap, def_tup);
        int n = f.getArity() - 1;
        for (int i = 0; i < n; i++) {
            if (!sorts.get(i).equals("int")) {
                return false;
            }
        }
        return true;
    }

    private Set<PARule> getNewRules(PARule dp, Set<PARule> p, CollectionNameProvider paFuns, ImmutableMap<String, ImmutableList<String>> sortMap, Map<FunctionSymbol, FunctionSymbol> def_tup) {
        TRSFunctionApplication rhs = (TRSFunctionApplication) dp.getRight();
        // rhs must be int-based
        if (!this.isIntSorted(rhs.getRootSymbol(), sortMap, def_tup)) {
            return null;
        }
        // Arguments on rhs must be PA terms
        for (TRSTerm t : rhs.getArguments()) {
            for (FunctionSymbol fun : t.getFunctionSymbols()) {
                if (!paFuns.contains(fun.getName())) {
                    return null;
                }
            }
        }

        FunctionSymbol dpr = ((TRSFunctionApplication) dp.getRight()).getRootSymbol();
        Set<PARule> chainRules = new LinkedHashSet<PARule>();

        for (PARule odp : p) {
            if (odp.getLeft().getRootSymbol().equals(dpr)) {
                chainRules.add(odp);
            }
        }

        if (chainRules.isEmpty()) {
            return null;
        } else {
            // Lhss of chainRules need to be variable-based
            if (!this.hasDistinctVars(chainRules)) {
                return null;
            } else {
                return this.buildNewRules(dp, chainRules);
            }
        }
    }

    private Set<PARule> buildNewRules(PARule dp, Set<PARule> chainRules) {
        Set<PARule> res = new LinkedHashSet<PARule>();
        for (PARule odp : chainRules) {
            res.add(this.buildNewRule(dp, odp));
        }
        return res;
    }

    private PARule buildNewRule(PARule dp, PARule odp) {
        TRSFunctionApplication dpr = (TRSFunctionApplication) dp.getRight();
        TRSFunctionApplication odpl = odp.getLeft();
        int arr = odpl.getRootSymbol().getArity();
        TRSSubstitution subby = TRSSubstitution.create();
        for (int i = 0; i < arr; i++) {
            subby = subby.extend(TRSSubstitution.create((TRSVariable) odpl.getArgument(i), dpr.getArgument(i)));
        }
        TRSFunctionApplication newLeft = dp.getLeft();
        TRSTerm newRight = odp.getRight().applySubstitution(subby);
        Set<PAConstraint> newConstr = new LinkedHashSet<PAConstraint>(dp.getConstraint());
        for (PAConstraint constr : odp.getConstraint()) {
            newConstr.add(PAConstraint.create(constr.getLeft().applySubstitution(subby), constr.getRight().applySubstitution(subby), constr.getType()));
        }
        return PARule.create(newLeft, newRight, ImmutableCreator.create(newConstr));
    }

    private static class PADPPairNarrowingProof extends Proof.DefaultProof {

        private PARule oldRule;
        private Set<PARule> newRules;

        private PADPPairNarrowingProof(PARule oldRule, Set<PARule> newRules) {
            this.oldRule = oldRule;
            this.newRules = newRules;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            result.append("By narrowing the dependency pair");
            result.append(o.linebreak());
            Set<PARule> tmp = new LinkedHashSet<PARule>();
            tmp.add(this.oldRule);
            result.append(o.set(tmp, Export_Util.RULES));
            result.append(o.linebreak());
            result.append("we obtain the dependency pairs");
            result.append(o.linebreak());
            result.append(o.set(this.newRules, Export_Util.RULES));
            return result.toString();
        }

    }

}
