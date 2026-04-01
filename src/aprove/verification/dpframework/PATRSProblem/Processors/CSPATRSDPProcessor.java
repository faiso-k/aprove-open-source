package aprove.verification.dpframework.PATRSProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.PADPProblem.*;
import aprove.verification.dpframework.PATRSProblem.*;
import aprove.verification.dpframework.PATRSProblem.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Processor that transforms a CSPATRS into a CSPADPProblem containing all dependency pairs.
 *
 * @author Stephan Falke
 * @version $Id$
 */
@NoParams
public class CSPATRSDPProcessor extends CSPATRSProcessor {

    private static final Logger logger = Logger.getLogger("aprove.verification.dpframework.PATRSProblem.Processors.CSPATRSDPProcessor");

    private Map<TRSTerm, Set<TRSVariable>> getVars(Set<TRSTerm> T, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        Map<TRSTerm, Set<TRSVariable>> res = new LinkedHashMap<TRSTerm, Set<TRSVariable>>();
        for (TRSTerm t : T) {
            Set<TRSVariable> tres = new LinkedHashSet<TRSVariable>();
            for (TRSTerm s : CSTermHelper.getActiveSubterms(t, mu)) {
                if (s.isVariable()) {
                    tres.add((TRSVariable) s);
                }
            }
            res.put(t, tres);
        }
        return res;
    }

    private Set<TRSVariable> getAllVars(Map<TRSTerm, Set<TRSVariable>> map) {
        Set<TRSVariable> res = new LinkedHashSet<TRSVariable>();
        for (Set<TRSVariable> vs : map.values()) {
            res.addAll(vs);
        }
        return res;
    }

    private boolean checkSE(Set<Rule> S, Set<Equation> E, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        // E is collapse-free by construction, so no need to check for this...
        for (Equation e : E) {
            Set<TRSTerm> leftActive = CSTermHelper.getActiveSubterms(e.getLeft(), mu);
            Set<TRSTerm> leftInactive = CSTermHelper.getInactiveSubterms(e.getLeft(), mu);
            Set<TRSTerm> rightActive = CSTermHelper.getActiveSubterms(e.getRight(), mu);
            Set<TRSTerm> rightInactive = CSTermHelper.getInactiveSubterms(e.getRight(), mu);
            for (TRSVariable v : e.getVariables()) {
                if ((leftActive.contains(v) && rightInactive.contains(v)) ||
                    (leftInactive.contains(v) && rightActive.contains(v))) {
                    //System.out.println("For " + e + ": " + v);
                    return false;
                }
            }
            Map<TRSTerm, Set<TRSVariable>> leftVars = this.getVars(leftInactive, mu);
            Set<TRSVariable> allLeftVars = this.getAllVars(leftVars);
            Map<TRSTerm, Set<TRSVariable>> rightVars = this.getVars(rightInactive, mu);
            Set<TRSVariable> allRightVars = this.getAllVars(rightVars);
            for (TRSTerm up : leftInactive) {
                if (!up.isVariable()) {
                    for (TRSVariable x : leftVars.get(up)) {
                        if (!allRightVars.contains(x)) {
                            //System.out.println("For " + e + ": " + up + " and " + x);
                            return false;
                        }
                    }
                }
            }
            for (TRSTerm vp : rightInactive) {
                if (!vp.isVariable()) {
                    for (TRSVariable x : rightVars.get(vp)) {
                        if (!allLeftVars.contains(x)) {
                            //System.out.println("For " + e + ": " + vp + " and " + x);
                            return false;
                        }
                    }
                }
            }
        }
        for (Rule s : S) {
            Set<TRSTerm> leftActive = CSTermHelper.getActiveSubterms(s.getLeft(), mu);
            Set<TRSTerm> leftInactive = CSTermHelper.getInactiveSubterms(s.getLeft(), mu);
            Set<TRSTerm> rightActive = CSTermHelper.getActiveSubterms(s.getRight(), mu);
            Set<TRSTerm> rightInactive = CSTermHelper.getInactiveSubterms(s.getRight(), mu);
            for (TRSVariable v : s.getRight().getVariables()) {
                if (rightActive.contains(v) && leftInactive.contains(v)) {
                    //System.out.println("For " + s + ": " + v);
                    return false;
                }
            }
            Map<TRSTerm, Set<TRSVariable>> leftVars = this.getVars(leftInactive, mu);
            Set<TRSVariable> allLeftVars = this.getAllVars(leftVars);
            Map<TRSTerm, Set<TRSVariable>> rightVars = this.getVars(rightInactive, mu);
            Set<TRSVariable> allRightVars = this.getAllVars(rightVars);
            for (TRSTerm rp : rightInactive) {
                if (!rp.isVariable()) {
                    for (TRSVariable x : rightVars.get(rp)) {
                        if (!allLeftVars.contains(x)) {
                            //System.out.println("For " + s + ": " + rp + " and " + x);
                            return false;
                        }
                    }
                }
            }
        }
        return true;
    }

    @Override
    protected Result processCSPATRS(CSPATRSProblem cspatrs, Abortion aborter) throws AbortionException {
        CSPATRSDPProcessor.logger.log(Level.FINE, "Checking applicability condition\n");
        if (!this.checkSE(cspatrs.getS(), cspatrs.getE(), cspatrs.getMu())) {
            return ResultFactory.unsuccessful();
        }

        CSPATRSDPProcessor.logger.log(Level.FINE, "Computing hidden terms and hiding positions\n");
        Set<FunctionSymbol> defs = cspatrs.getDefinedSymbols();
        ImmutableMap<String, ImmutableSet<Integer>> mu = cspatrs.getMu();
        ImmutableSet<PARule> r = cspatrs.getR();
        ImmutableMap<String, ImmutableList<String>> sortMap = cspatrs.getSortMap();

        Set<TRSTerm> hiddenTerms = this.computeHiddenTerms(r, defs, mu);
        Map<FunctionSymbol, Set<Integer>> hidePos = this.computeHidePos(cspatrs.getSignature(), cspatrs.getSignatureSE(), r, defs, mu);

        CSPATRSDPProcessor.logger.log(Level.FINE, "Creating dependency pairs\n");
        Set<PARule> dps = new LinkedHashSet<PARule>();
        Set<FunctionSymbol> allfuns = new LinkedHashSet<FunctionSymbol>(cspatrs.getSignature());
        Map<FunctionSymbol, FunctionSymbol> def_tup = new HashMap<FunctionSymbol, FunctionSymbol>();
        // first, compute DP_o
        for (PARule rule : r) {
            Set<TRSFunctionApplication> calls = new LinkedHashSet<TRSFunctionApplication>();
            TRSFunctionApplication lhs = rule.getLeft();
            TRSTerm rhs = rule.getRight();
            ImmutableSet<PAConstraint> cond = rule.getConstraint();
            for (TRSTerm sub : CSTermHelper.getActiveSubterms(rhs, mu)) {
                if (!sub.isVariable()) {
                    TRSFunctionApplication subterm = (TRSFunctionApplication) sub;
                    FunctionSymbol root = subterm.getRootSymbol();
                    if (defs.contains(root)) {
                        calls.add(subterm);
                    }
                }
            }
            if (calls.isEmpty()) {
                continue;
            }
            FunctionSymbol tf = this.getTupleSymbol(lhs.getRootSymbol(), def_tup, allfuns);
            TRSFunctionApplication tlhs = TRSTerm.createFunctionApplication(tf, lhs.getArguments());
            for (TRSFunctionApplication call : calls) {
                FunctionSymbol tg = this.getTupleSymbol(call.getRootSymbol(), def_tup, allfuns);
                TRSFunctionApplication trhs = TRSTerm.createFunctionApplication(tg, call.getArguments());
                dps.add(PARule.create(tlhs, trhs, cond));
            }
        }
        // second, l# -> Unhide(x)
        FunctionSymbol unhide_base = this.getUnhideSymbol(allfuns, "int");
        FunctionSymbol unhide_univ = this.getUnhideSymbol(allfuns, "univ");
        for (PARule rule : r) {
            Set<TRSVariable> rVars = new LinkedHashSet<TRSVariable>();
            TRSFunctionApplication lhs = rule.getLeft();
            Map<TRSVariable, String> varSorts = new LinkedHashMap<TRSVariable, String>();
            this.determineVarSorts(lhs, sortMap, varSorts);
            Set<TRSVariable> lInactiveVars = CSTermHelper.getInactiveVariables(lhs, mu);
            for (TRSVariable x : CSTermHelper.getActiveVariables(rule.getRight(), mu)) {
                if (lInactiveVars.contains(x)) {
                    rVars.add(x);
                }
            }
            if (rVars.isEmpty()) {
                continue;
            }
            ImmutableSet<PAConstraint> cond = rule.getConstraint();
            FunctionSymbol tf = this.getTupleSymbol(lhs.getRootSymbol(), def_tup, allfuns);
            TRSFunctionApplication tlhs = TRSTerm.createFunctionApplication(tf, lhs.getArguments());
            for (TRSVariable v : rVars) {
                ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
                args.add(v);
                FunctionSymbol funsy = null;
                if (varSorts.get(v).equals("univ")) {
                    funsy = unhide_univ;
                } else {
                    funsy = unhide_base;
                }
                TRSFunctionApplication trhs = TRSTerm.createFunctionApplication(funsy, ImmutableCreator.create(args));
                dps.add(PARule.create(tlhs, trhs, cond));
            }
        }
        // third, Unhide(h) -> h#
        for (TRSTerm hidden : hiddenTerms) {
            ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
            args.add(hidden);
            FunctionSymbol funsy = null;
            if (this.getSort(hidden, sortMap).equals("univ")) {
                funsy = unhide_univ;
            } else {
                funsy = unhide_base;
            }
            TRSFunctionApplication tlhs = TRSTerm.createFunctionApplication(funsy, ImmutableCreator.create(args));
            FunctionSymbol tf = this.getTupleSymbol(((TRSFunctionApplication) hidden).getRootSymbol(), def_tup, allfuns);
            TRSFunctionApplication trhs = TRSTerm.createFunctionApplication(tf, ((TRSFunctionApplication) hidden).getArguments());
            dps.add(PARule.create(tlhs, trhs, ImmutableCreator.create(new LinkedHashSet<PAConstraint>())));
        }
        // fourth, Unhide(g(...x_i...)) -> Unhide(x_i)
        for (Map.Entry<FunctionSymbol, Set<Integer>> entry : hidePos.entrySet()) {
            FunctionSymbol f = entry.getKey();
            Set<Integer> hpos = entry.getValue();
            Set<TRSTerm> heidi = new LinkedHashSet<TRSTerm>();
            for (Integer i : hpos) {
                heidi.add(TRSTerm.createVariable("x_" + (i.intValue() + 1)));
            }
            if (heidi.isEmpty()) {
                continue;
            }
            int arr = f.getArity();
            ArrayList<TRSTerm> vars = new ArrayList<TRSTerm>();
            for (int i = 0; i < arr; i++) {
                vars.add(TRSTerm.createVariable("x_" + (i + 1)));
            }
            TRSTerm fvars = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(vars));
            FunctionSymbol funsy = null;
            if (this.getSort(fvars, sortMap).equals("univ")) {
                funsy = unhide_univ;
            } else {
                funsy = unhide_base;
            }
            TRSFunctionApplication tlhs = TRSTerm.createFunctionApplication(funsy, fvars);
            Map<TRSVariable, String> varSorts = new LinkedHashMap<TRSVariable, String>();
            this.determineVarSorts(fvars, sortMap, varSorts);
            for (TRSTerm v : heidi) {
                ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
                args.add(v);
                if (varSorts.get((TRSVariable) v).equals("univ")) {
                    funsy = unhide_univ;
                } else {
                    funsy = unhide_base;
                }
                TRSFunctionApplication trhs = TRSTerm.createFunctionApplication(funsy, ImmutableCreator.create(args));
                dps.add(PARule.create(tlhs, trhs, ImmutableCreator.create(new LinkedHashSet<PAConstraint>())));
            }
        }

        // add new symbols to maps
        Map<String, ImmutableList<String>> newSortMap = new LinkedHashMap<String, ImmutableList<String>>(sortMap);
        newSortMap.put(unhide_base.getName(), this.getSortEntry("int", "top"));
        newSortMap.put(unhide_univ.getName(), this.getSortEntry("univ", "top"));
        Map<String, ImmutableSet<Integer>> newMu = new LinkedHashMap<String, ImmutableSet<Integer>>(mu);
        newMu.put(unhide_base.getName(), ImmutableCreator.create(new LinkedHashSet<Integer>()));
        newMu.put(unhide_univ.getName(), ImmutableCreator.create(new LinkedHashSet<Integer>()));
        for (Map.Entry<FunctionSymbol, FunctionSymbol> entry : def_tup.entrySet()) {
            newMu.put(entry.getValue().getName(), mu.get(entry.getKey().getName()));
        }
        def_tup.put(unhide_base, unhide_base);
        def_tup.put(unhide_univ, unhide_univ);

        CSPATRSProblem newCSPATRS = CSPATRSProblem.create(cspatrs.getR(), cspatrs.getS(), cspatrs.getE(), ImmutableCreator.create(newSortMap), ImmutableCreator.create(newMu));
        CSPADPProblem cspadp = CSPADPProblem.create(ImmutableCreator.create(dps), newCSPATRS, def_tup);
        return ResultFactory.proved(cspadp, YNMImplication.SOUND, new CSPATRSDPProof(cspadp));
    }

    private ImmutableList<String> getSortEntry(String s1, String s2) {
        List<String> res = new Vector<String>();
        res.add(s1);
        res.add(s2);
        return ImmutableCreator.create(res);
    }

    private void determineVarSorts(TRSTerm t, ImmutableMap<String, ImmutableList<String>> sortMap, Map<TRSVariable, String> varSorts) {
        if (t.isVariable()) {
            return;
        }
        TRSFunctionApplication ft = (TRSFunctionApplication) t;
        String f = ft.getRootSymbol().getName();
        ImmutableList<String> sorts = sortMap.get(f);
        for (int i = 0; i < sorts.size() - 1; i++) {
            TRSTerm tt = ft.getArgument(i);
            if (tt.isVariable()) {
                String stt = varSorts.get(tt);
                if (stt == null) {
                    varSorts.put((TRSVariable) tt, sorts.get(i));
                }
            } else {
                this.determineVarSorts(tt, sortMap, varSorts);
            }
        }
    }

    private String getSort(TRSTerm t, ImmutableMap<String, ImmutableList<String>> sortMap) {
        if (t.isVariable()) {
            throw new RuntimeException("internal error in CSPATRSDP: Variable " + t + " cannot be a hidden term");
        }
        FunctionSymbol ft = ((TRSFunctionApplication) t).getRootSymbol();
        String f = ft.getName();
        return sortMap.get(f).get(ft.getArity());
    }

    private FunctionSymbol getTupleSymbol(FunctionSymbol f, Map<FunctionSymbol, FunctionSymbol> def_tup, Set<FunctionSymbol> allfuns) {
        FunctionSymbol tf = def_tup.get(f);
        if (tf == null) {
            String wishedName = f.getName().toUpperCase();
            int arity = f.getArity();
            int nr = 1;
            tf = FunctionSymbol.create(wishedName, arity);
            while (!allfuns.add(tf)) {
                tf = FunctionSymbol.create(wishedName + "^" + nr, arity);
                nr++;
            }
            def_tup.put(f, tf);
        }
        return tf;
    }

    private FunctionSymbol getUnhideSymbol(Set<FunctionSymbol> allfuns, String sort) {
        String wishedName = "Unhide";
        int nr = 1;
        FunctionSymbol tf = FunctionSymbol.create(wishedName + "_" + sort, 1);
        while (!allfuns.add(tf)) {
            tf = FunctionSymbol.create(wishedName + "^" + nr + "_" + sort, 1);
            nr++;
        }
        return tf;
    }

    private Map<FunctionSymbol, Set<Integer>> computeHidePos(ImmutableSet<FunctionSymbol> F, ImmutableSet<FunctionSymbol> FSE, ImmutableSet<PARule> r, Set<FunctionSymbol> defs, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        Map<FunctionSymbol, Set<Integer>> res = new LinkedHashMap<FunctionSymbol, Set<Integer>>();
        for (FunctionSymbol f : FSE) {
            Set<Integer> fpos = new LinkedHashSet<Integer>();
            int arr = f.getArity();
            ImmutableSet<Integer> mus = mu.get(f.getName());
            for (int i = 0; i < arr; i++) {
                Integer ii = Integer.valueOf(i);
                if (mus.contains(ii)) {
                    fpos.add(ii);
                }
            }
            res.put(f, fpos);
        }
        for (PARule rule : r) {
            Set<TRSTerm> cands = CSTermHelper.getInactiveSubterms(rule.getRight(), mu);
            for (TRSTerm s : cands) {
                if (!s.isVariable()) {
                    TRSFunctionApplication fs = (TRSFunctionApplication) s;
                    FunctionSymbol f = fs.getRootSymbol();
                    if (!FSE.contains(f)) {
                        ImmutableSet<Integer> mus = mu.get(f.getName());
                        Set<Integer> entry = this.getEntry(f, res);
                        int arr = f.getArity();
                        for (int i = 0; i < arr; i++) {
                            Integer ii = Integer.valueOf(i);
                            if (mus.contains(ii) && !entry.contains(ii) && this.causeHidePos(fs.getArgument(i), defs, mu)) {
                                entry.add(ii);
                            }
                        }
                    }
                }
            }
        }
        return res;
    }

    private boolean causeHidePos(TRSTerm t, Set<FunctionSymbol> defs, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        for (TRSTerm s : CSTermHelper.getActiveSubterms(t, mu)) {
            if (s.isVariable()) {
                return true;
            } else {
                TRSFunctionApplication fs = (TRSFunctionApplication) s;
                if (defs.contains(fs.getRootSymbol())) {
                    return true;
                }
            }
        }
        return false;
    }

    private Set<Integer> getEntry(FunctionSymbol f, Map<FunctionSymbol, Set<Integer>> map) {
        Set<Integer> res = map.get(f);
        if (res == null) {
            res = new LinkedHashSet<Integer>();
            map.put(f, res);
        }
        return res;
    }

    private Set<TRSTerm> computeHiddenTerms(ImmutableSet<PARule> R, Set<FunctionSymbol> defs, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        Set<TRSTerm> res = new LinkedHashSet<TRSTerm>();
        for (PARule r : R) {
            res.addAll(this.computeHiddenTerms(r.getRight(), defs, mu));
        }
        return res;
    }

    private Set<TRSTerm> computeHiddenTerms(TRSTerm t, Set<FunctionSymbol> defs, ImmutableMap<String, ImmutableSet<Integer>> mu) {
        Set<TRSTerm> cands = CSTermHelper.getInactiveSubterms(t, mu);
        Set<TRSTerm> res = new LinkedHashSet<TRSTerm>();
        for (TRSTerm s : cands) {
            if (!s.isVariable()) {
                FunctionSymbol f = ((TRSFunctionApplication) s).getRootSymbol();
                if (defs.contains(f)) {
                    res.add(s);
                }
            }
        }
        return res;
    }

    private class CSPATRSDPProof extends Proof.DefaultProof {
        CSPADPProblem cspadp;

        private CSPATRSDPProof(CSPADPProblem cspadp) {
            this.cspadp = cspadp;
        }

        @Override
        public String export(Export_Util eu, VerbosityLevel level){
            return "Using the dependency pair approach we obtain in the following initial CSPADP problem:" +
                   eu.linebreak() + this.cspadp.export(eu) + eu.linebreak();
        }
    }

}
