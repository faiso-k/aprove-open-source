package aprove.verification.dpframework.PADPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.PADPProblem.*;
import aprove.verification.dpframework.PATRSProblem.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */

@NoParams
public class PADPReducingProcessor extends PADPProcessor {

    private static int newnr = 0;

    @Override
    protected Result processPADP(PADPProblem padp, Abortion aborter) throws AbortionException {
        Set<PARule> p = new LinkedHashSet<PARule>(padp.getP());
        Map<FunctionSymbol, Set<Rule>> smap = Rule.getRuleMap(padp.getS());
        Set<Equation> e = padp.getE();
        Set<FunctionSymbol> defs = padp.getPATRS().getDefinedSymbols();
        Set<FunctionSymbol> sdefs = padp.getPATRS().getDefinedSymbolsOfS();
        Map<String, ImmutableList<String>> sortMap = padp.getPATRS().getSortMap();
        Map<FunctionSymbol, FunctionSymbol> def_tup = padp.getDefTup();

        PARule oldRule = null;
        PARule newRule = null;

        for (PARule dp : p) {
            newRule = this.getNewRule(dp, sortMap, defs, sdefs, smap, e, def_tup);
            if (newRule != null) {
                oldRule = dp;
                break;
            }
        }

        if (newRule == null) {
            return ResultFactory.unsuccessful();
        }

        p.remove(oldRule);
        p.add(newRule);
        Proof proof = new PADPReducingProof(oldRule, newRule);
        PADPProblem newPADP = PADPProblem.create(ImmutableCreator.create(p), padp.getPATRS(), padp.getDefTup());
        return ResultFactory.proved(newPADP, YNMImplication.EQUIVALENT, proof);
    }

    private PARule getNewRule(PARule dp, Map<String, ImmutableList<String>> sortMap, Set<FunctionSymbol> defs, Set<FunctionSymbol> sdefs, Map<FunctionSymbol, Set<Rule>> smap, Set<Equation> e, Map<FunctionSymbol, FunctionSymbol> def_tup) {
        for (Pair<Position, TRSTerm> posterm : dp.getRight().getPositionsWithSubTerms()) {
            Position pos = posterm.x;
            TRSTerm t = posterm.y;
            if (!this.isGood(t, sdefs)) {
                continue;
            }
            Map<TRSVariable, TRSTerm> subby = new HashMap<TRSVariable, TRSTerm>();
            TRSTerm capped_t = this.getCapped(t, subby, sortMap, null, defs, def_tup);
            TRSTerm that = this.rewriteOnce(capped_t, smap, e);
            if (that != null) {
                TRSTerm thatsubby = that.applySubstitution(TRSSubstitution.create(ImmutableCreator.create(subby)));
                TRSTerm newRight = dp.getRight().replaceAt(pos, thatsubby);
                return PARule.create(dp.getLeft(), newRight, dp.getConstraint());
            }
        }
        return null;
    }

    private boolean isGood(TRSTerm t, Set<FunctionSymbol> sdefs) {
        if (t.isVariable()) {
            return false;
        } else {
            return sdefs.contains(((TRSFunctionApplication) t).getRootSymbol());
        }
    }

    private TRSTerm rewriteOnce(TRSTerm t, Map<FunctionSymbol, Set<Rule>> smap, Set<Equation> e) {
        Set<TRSTerm> tclass = EquivalenceClassGenerator.getEquivalenceClass(t, e);

        for (TRSTerm s : tclass) {
            Set<TRSTerm> rewrites = s.rewrite(smap);
            if (!rewrites.isEmpty()) {
                return (new Vector<TRSTerm>(rewrites)).get(0);
            }
        }

        return null;
    }

    private TRSTerm getCapped(TRSTerm t, Map<TRSVariable, TRSTerm> subby, Map<String, ImmutableList<String>> sortMap, String currSort, Set<FunctionSymbol> defs, Map<FunctionSymbol, FunctionSymbol> def_tup) {
        if (t.isVariable()) {
            if ("int".equals(currSort)) {
                return t;
            }
            TRSVariable x = (TRSVariable) t;
            PADPReducingProcessor.newnr = PADPReducingProcessor.newnr + 1;
            TRSVariable newx = TRSTerm.createVariable("!" + x.getName() + (Integer.valueOf(PADPReducingProcessor.newnr )).toString());
            subby.put(newx, t);
            return newx;
        } else {
            TRSFunctionApplication ft = (TRSFunctionApplication) t;
            FunctionSymbol troot = ft.getRootSymbol();
            if (defs.contains(troot)) {
                PADPReducingProcessor.newnr = PADPReducingProcessor.newnr + 1;
                TRSVariable newx = TRSTerm.createVariable("!" + (Integer.valueOf(PADPReducingProcessor.newnr)).toString());
                subby.put(newx, t);
                return newx;
            } else {
                int arr = troot.getArity();
                List<String> sorts = sortMap.get(troot.getName());
                if (sorts == null) {
                    sorts = sortMap.get(this.getDef(troot, def_tup).getName());
                }
                ArrayList<TRSTerm> newargs = new ArrayList<TRSTerm>();
                for (int i = 0; i < arr; i++) {
                    newargs.add(this.getCapped(ft.getArgument(i), subby, sortMap, sorts.get(i), defs, def_tup));
                }
                return TRSTerm.createFunctionApplication(troot, ImmutableCreator.create(newargs));
            }
        }
    }

    private FunctionSymbol getDef(FunctionSymbol f, Map<FunctionSymbol, FunctionSymbol> def_tup) {
        for (FunctionSymbol g : def_tup.keySet()) {
            if (def_tup.get(g).equals(f)) {
                return g;
            }
        }
        return null;
    }

    private static class PADPReducingProof extends Proof.DefaultProof {

        private PARule oldRule;
        private PARule newRule;

        private PADPReducingProof(PARule oldRule, PARule newRule) {
            this.oldRule = oldRule;
            this.newRule = newRule;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result = new StringBuilder();
            result.append("By reducing the right-hand side of the dependency pair");
            result.append(o.linebreak());
            Set<PARule> tmp = new LinkedHashSet<PARule>();
            tmp.add(this.oldRule);
            result.append(o.set(tmp, Export_Util.RULES));
            result.append(o.linebreak());
            result.append("using S we obtain the dependency pair");
            result.append(o.linebreak());
            tmp.remove(this.oldRule);
            tmp.add(this.newRule);
            result.append(o.set(tmp, Export_Util.RULES));
            return result.toString();
        }

    }

}
