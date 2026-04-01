package aprove.verification.theoremprover.Simplifier;
import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Verifier.*;

@NoParams
public class RecursionShiftSimplifier extends FixedValueSimplifier {

    //private SimplifierObligation obl;

    public RecursionShiftSimplifier(){
        super("Recursion Shift Simplifier","RS","Recursion Shift");
    }

    @Override
    public SimplifierObligation simplify(SimplifierObligation oobl) {
        this.obl = oobl.shallowcopy();
        this.resetfvtInfo();
        Set<DefFunctionSymbol> fsymCh = this.recursionShifting();
        if (fsymCh.isEmpty()) {
            return null;
        }
        this.setProof(new RecursionShiftProof(oobl,fsymCh,this.obl));
        return this.obl;
    }

    public Set<DefFunctionSymbol> recursionShifting() {
        Set<DefFunctionSymbol> fsymCh = new HashSet<DefFunctionSymbol>();
    SimplifierProcessor.log.log(Level.FINER, "Simplifier: Performing recursion-shift.\n");
    this.obl.critRecCallsTable = new Hashtable();
    this.fixedValueTransformation();
    Iterator it = this.obl.critRecCallsTable.entrySet().iterator();
    while (it.hasNext()) {
        Map.Entry entry = (Map.Entry)it.next();
        DefFunctionSymbol fsym = (DefFunctionSymbol)entry.getKey();
        Vector fsCritRecCalls = (Vector)entry.getValue();
        Iterator it2 = fsCritRecCalls.iterator();
        while (it2.hasNext()) {
        Object tmp[] = (Object[])it2.next();
        if (this.recursionShifting(fsym, (Vector)tmp[0], (Vector<AlgebraTerm>)tmp[1], (Vector<AlgebraVariable>)tmp[2])) {
            this.fixedValueTransformation(fsym);
                    fsymCh.add(fsym);
        }
        }
    }
    this.obl.critRecCallsTable = null;
        return fsymCh;
    }

    /** Performs recursion-shifting on fsym. Returns true on success. */
    public boolean recursionShifting(DefFunctionSymbol fsym, Vector critRecCalls, Vector<AlgebraTerm> ps, Vector<AlgebraVariable> zs) {
    // Create a bit-field where the i-th bit is set iff the
    // i-th argument shall be replaced by a fixed term.

    // TODO removal of sorts
    Sort fsort = fsym.getSort();

    Vector<AlgebraTerm> contexts = new Vector<AlgebraTerm>();
    Vector<AlgebraTerm> conditions = new Vector<AlgebraTerm>();
    // Get the variablenames of the lifted-rules.
    Iterator it = critRecCalls.iterator();
    Object tmp[] = (Object[])it.next();
    Rule lrule = (Rule)tmp[1];
    List<AlgebraTerm> xs = lrule.getLeft().getArguments();
    // Create contexts with their evaluation-conditions.
    // And create a list with unproblematic recursive calls.
    Vector unprob = new Vector();
    int i = 0;
    it = critRecCalls.iterator();
    while (it.hasNext()) {
        tmp = (Object[])it.next();
        lrule = (Rule)tmp[1];
        AlgebraTerm context = lrule.getRight();
        AlgebraTerm condition = (AlgebraTerm)tmp[2];
        Hashtable recargs = (Hashtable)tmp[3];
        Hashtable unprobTable = new Hashtable();
        // Per rule problematic rec-calls.
        Iterator pos_it = recargs.keySet().iterator();
        while (pos_it.hasNext()) {
        Position pi = (Position)pos_it.next();
        String name = this.obl.symbnames.getFreshName("u_"+(++i), false);
        AlgebraVariable v = AlgebraVariable.create(VariableSymbol.create(name, fsort));
        context = context.replaceAt(v, pi);
        }
        // Per rule unproblematic rec-calls.
        pos_it = RecursionShiftSimplifier.getCallPositions(context, fsym).iterator();
        while (pos_it.hasNext()) {
        Position pi = (Position)pos_it.next();
        unprobTable.put(pi, context.getSubterm(pi));
        String name = this.obl.symbnames.getFreshName("u_"+(++i), false);
        AlgebraVariable v = AlgebraVariable.create(VariableSymbol.create(name, fsort));
        context = context.replaceAt(v, pi);
        }
        contexts.add(context);
        conditions.add(condition);
        unprob.add(unprobTable);
    }
    Set<AlgebraVariable> w = new HashSet<AlgebraVariable>();
    Vector solList = new Vector();
    RewriteCalculus rwc = RewriteCalculus.create(this.obl.rootprogram, this.obl.defsrules, this.obl.typeContext);
    // Per function rec-calls.
    it = critRecCalls.iterator();
    while (it.hasNext()) {
        tmp = (Object[])it.next();
        Rule rule = (Rule)tmp[0];
        lrule = (Rule)tmp[1];
        AlgebraTerm condition = (AlgebraTerm)tmp[2];
        Hashtable recargs = (Hashtable)tmp[3];
        Hashtable solutions = new Hashtable();
        // Per rule rec-calls.
        Iterator args_it = recargs.entrySet().iterator();
        while (args_it.hasNext()) {
        Map.Entry entry = (Map.Entry)args_it.next();
        Position pi = (Position)entry.getKey();
        List<AlgebraTerm> arguments = (List<AlgebraTerm>)entry.getValue();
        AlgebraSubstitution rsigma = AlgebraSubstitution.create();
        List<AlgebraTerm> sol = this.getRecShiftSolution(fsym, arguments, xs, ps, zs, condition, contexts, conditions, unprob, rwc, w, rsigma);
        if (sol == null) {
            return false;
        }
        solutions.put(pi, sol);
        }
        solList.add(solutions);
    }
    // Now we have have solutions for every critical recursive
    // call. Let's see whether the use of them is sound.
    Iterator it1 = critRecCalls.iterator();
    Iterator solt_it1 = solList.iterator();
    while (it1.hasNext()) {
        tmp = (Object[])it1.next();
        Rule lrule1 = (Rule)tmp[1];
        AlgebraTerm context1 = lrule1.getRight();
        AlgebraTerm condition1 = (AlgebraTerm)tmp[2];
        Hashtable recargs1 = (Hashtable)tmp[3];
        Hashtable solutions1 = (Hashtable)solt_it1.next();
        Iterator pos_it1 = recargs1.keySet().iterator();
        while (pos_it1.hasNext()) {
        Position pi1 = (Position)pos_it1.next();
        List<AlgebraTerm> rs1 = (List<AlgebraTerm>)recargs1.get(pi1);
        List<AlgebraTerm> qs1 = (List<AlgebraTerm>)solutions1.get(pi1);
        Iterator it2 = critRecCalls.iterator();
        Iterator solt_it2 = solList.iterator();
        while (it2.hasNext()) {
            tmp = (Object[])it2.next();
            Rule lrule2 = (Rule)tmp[1];
            AlgebraTerm context2 = lrule1.getRight();
            AlgebraTerm condition2 = (AlgebraTerm)tmp[2];
            Hashtable recargs2 = (Hashtable)tmp[3];
            Hashtable solutions2 = (Hashtable)solt_it2.next();
            Iterator pos_it2 = recargs2.keySet().iterator();
            while (pos_it2.hasNext()) {
            Position pi2 = (Position)pos_it2.next();
            List<AlgebraTerm> rs2 = (List<AlgebraTerm>)recargs2.get(pi2);
            List<AlgebraTerm> qs2 = (List<AlgebraTerm>)solutions2.get(pi2);
            AlgebraSubstitution r_sub = AlgebraSubstitution.create();
            AlgebraSubstitution q_sub = AlgebraSubstitution.create();
            Iterator x_it = xs.iterator();
            Iterator q_it = qs2.iterator();
            Iterator r_it = rs2.iterator();
            while (x_it.hasNext()) {
                AlgebraVariable x = (AlgebraVariable)x_it.next();
                AlgebraTerm q = (AlgebraTerm)q_it.next();
                AlgebraTerm r = (AlgebraTerm)r_it.next();
                r_sub.put((VariableSymbol)x.getSymbol(), r);
                q_sub.put((VariableSymbol)x.getSymbol(), q==null ? r : q);
            }
            Vector<AlgebraTerm> tmpargs = new Vector<AlgebraTerm>();
            tmpargs.add(condition2);
            tmpargs.add(condition1.apply(r_sub));
            AlgebraTerm cond = AlgebraFunctionApplication.create(this.obl.fAnd, tmpargs);
            q_it = qs1.iterator();
            r_it = rs1.iterator();
            int rPos=0;
            while (q_it.hasNext()) {
                AlgebraTerm q = (AlgebraTerm)q_it.next();
                AlgebraTerm r = (AlgebraTerm)r_it.next();
                AlgebraTerm cntxt1Subterm = context1.getSubterm(pi1);
                AlgebraTerm rType = TypeTools.getFunctionArgAt(this.obl.typeContext.getSingleTypeOf(cntxt1Subterm.getSymbol()).getTypeMatrix(), rPos);
                rPos++;
                if (q != null) {
                // q and r must have the same type, therefore rType is enough...
                if (!rwc.proveEquivalenceUnderCondition(q.apply(r_sub), rType, r.apply(q_sub), rType, cond)) {
                    return false;
                }
                }
            }
            }
        }
        }
    }
    // Since we are here we have solutions that are sound.
    // Hence, do the recursion-shift.
    Set<Rule> newrules = new HashSet<Rule>();
    it = critRecCalls.iterator();
    Iterator solt_it = solList.iterator();
    Iterator unprob_it = unprob.iterator();
    while (it.hasNext()) {
        tmp = (Object[])it.next();
        Rule rule = (Rule)tmp[0];
        lrule = (Rule)tmp[1];
        AlgebraTerm newright = lrule.getRight();
        AlgebraTerm condition = (AlgebraTerm)tmp[2];
        Hashtable recargs = (Hashtable)tmp[3];
        Hashtable solutions = (Hashtable)solt_it.next();
        Hashtable unprobTable = (Hashtable)unprob_it.next();
        AlgebraSubstitution sub = AlgebraSubstitution.create();
        Iterator x_it = xs.iterator();
        Iterator arg_it = rule.getLeft().getArguments().iterator();
        while (x_it.hasNext()) {
        AlgebraVariable x = (AlgebraVariable)x_it.next();
        sub.put((VariableSymbol)x.getSymbol(), (AlgebraTerm)arg_it.next());
        }
        Iterator pos_it = recargs.keySet().iterator();
        while (pos_it.hasNext()) {
        Position pi = (Position)pos_it.next();
        Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
        List<AlgebraTerm> rs = (List<AlgebraTerm>)recargs.get(pi);
        List<AlgebraTerm> qs = (List<AlgebraTerm>)solutions.get(pi);
        Iterator r_it = rs.iterator();
        Iterator q_it = qs.iterator();
        while (r_it.hasNext()) {
            AlgebraTerm r = (AlgebraTerm)r_it.next();
            AlgebraTerm q = (AlgebraTerm)q_it.next();
            args.add(q==null ? r : q);
        }
        newright = newright.replaceAt(AlgebraFunctionApplication.create(fsym, args), pi);
        }
        pos_it = unprobTable.keySet().iterator();
        while (pos_it.hasNext()) {
        Position pi = (Position)pos_it.next();
        newright = newright.replaceAt((AlgebraTerm)unprobTable.get(pi), pi);
        }
        newrules.add(Rule.create(rule.getConds(), rule.getLeft(), newright.apply(sub)));
    }
    this.obl.defsrules.put(fsym, newrules);
    this.obl.updateSymbol(fsym, newrules);
    return true;
    }

    // Returns an innermost list of positions, where f is called.
    private static Vector<Position> getCallPositions(AlgebraTerm t, SyntacticFunctionSymbol fsym) {
    Vector<Position> positions = new Vector<Position>();
    RecursionShiftSimplifier.getCallPositions(t, fsym, Position.create(), positions);
    return positions;
    }

    private static void getCallPositions(AlgebraTerm t, SyntacticFunctionSymbol fsym, Position pi, Vector<Position> positions) {
    if (!t.isVariable()) {
        Iterator it = t.getArguments().iterator();
        for (int i=0; it.hasNext(); i++) {
        AlgebraTerm t2 = (AlgebraTerm)it.next();
        Position pi2 = pi.shallowcopy();
        pi2.add(i);
        RecursionShiftSimplifier.getCallPositions(t2, fsym, pi2, positions);
        }
        if (t.getSymbol().equals(fsym)) {
        positions.add(pi);
        }
    }
    }

    /** Trys to find a solution for a certain recursive call.
     */
    List<AlgebraTerm> getRecShiftSolution(DefFunctionSymbol fsym, List<AlgebraTerm> rs, List<AlgebraTerm> xs, List<AlgebraTerm> ps, List<AlgebraVariable> zs, AlgebraTerm condition, List<AlgebraTerm> contexts, List<AlgebraTerm> conditions, Vector unprob, RewriteCalculus rwc, Set<AlgebraVariable> w, AlgebraSubstitution rsigma) {
    // Split arugments, xs and zs according to fixed.
    BigInteger fixed = BigInteger.ZERO;
    Vector<AlgebraVariable> zs1 = new Vector<AlgebraVariable>();
    Vector<AlgebraVariable> zs2 = new Vector<AlgebraVariable>();
    Vector<AlgebraVariable> xs1 = new Vector<AlgebraVariable>();
    Vector<AlgebraVariable> xs2 = new Vector<AlgebraVariable>();
    Vector pos = new Vector();
    Vector<AlgebraTerm> rs1 = new Vector<AlgebraTerm>();
    Vector<AlgebraTerm> rs2 = new Vector<AlgebraTerm>();
    Iterator p_it = ps.iterator();
    Iterator z_it = zs.iterator();
    Iterator x_it = xs.iterator();
    Iterator r_it = rs.iterator();
    int j = 0;
    int k = 0;
    for (int i=0; p_it.hasNext(); i++) {
        AlgebraVariable z = (AlgebraVariable)z_it.next();
        AlgebraVariable x = (AlgebraVariable)x_it.next();
        AlgebraTerm r = (AlgebraTerm)r_it.next();
        if (p_it.next() != null) {
        zs2.add(z);
        xs2.add(x);
        rs2.add(r);
        fixed = fixed.setBit(i);
        pos.add(Integer.valueOf(k++));
        }
        else {
        zs1.add(z);
        xs1.add(x);
        rs1.add(r);
        pos.add(Integer.valueOf(j++));
        }
    }
    // Create substitution according to unproblematic rec-calls.
    Set<AlgebraVariable> ys = new HashSet<AlgebraVariable>();
    Iterator it = unprob.iterator();
    while (it.hasNext()) {
        Hashtable unprobTable = (Hashtable)it.next();
        Iterator call_it = unprobTable.values().iterator();
        while (call_it.hasNext()) {
        AlgebraTerm call = (AlgebraTerm)call_it.next();
        Iterator arg_it = call.getArguments().iterator();
        Iterator xi_it = xs.iterator();
        Iterator ri_it = rs.iterator();
        for (int i=0; arg_it.hasNext(); i++) {
            AlgebraTerm arg = (AlgebraTerm)arg_it.next();
            AlgebraVariable xi = (AlgebraVariable)xi_it.next();
            AlgebraTerm ri = (AlgebraTerm)ri_it.next();
            if (!fixed.testBit(i) && !arg.equals(xi)) {
            Set<AlgebraVariable> argvars1 = arg.getVars();
            Set<AlgebraVariable> argvars2 = new HashSet<AlgebraVariable>(argvars1);
            argvars1.retainAll(xs2);
            argvars2.retainAll(w);
            if (argvars1.isEmpty() && argvars2.isEmpty() && !this.obl.gotDependencies(arg, fsym)) {
                Iterator xj_it = xs.iterator();
                Iterator rj_it = rs.iterator();
                for (j=0; xj_it.hasNext(); j++) {
                AlgebraVariable xj = (AlgebraVariable)xj_it.next();
                AlgebraTerm rj = (AlgebraTerm)rj_it.next();
                if (!fixed.testBit(j) && j!=i && !rsigma.inRange(rj) &&
                    !ys.contains(xj) && !ri.getVars().contains(xj)) {
                    // Replace the i-th component of rs by a new
                    // variable z and let rsigma map to it.
                    String name = this.obl.symbnames.getFreshName("z_"+(i+1), false);
                    VariableSymbol vsym = VariableSymbol.create(name, ri.getSymbol().getSort());
                    rsigma.put(vsym, ri);
                    AlgebraVariable v = AlgebraVariable.create(vsym);
                    rs.set(i, v);
                    rs1.set(((Integer)pos.get(i)).intValue(), v);
                    break;
                }
                }
            }
            }
        }
        }
    }
    // Create variable-assignment-substitution tau.
    AlgebraSubstitution tau = AlgebraSubstitution.create();
    x_it = xs.iterator();
    r_it = rs.iterator();
    while (x_it.hasNext()) {
        AlgebraVariable x = (AlgebraVariable)x_it.next();
        AlgebraTerm r = (AlgebraTerm)r_it.next();
        tau.put((VariableSymbol)x.getSymbol(), r);
    }
    // Create the rewrite-pairs that may yield suitable
    // argument-replacements.
    Vector mt = new Vector();
    Iterator cntxt_it = contexts.iterator();
    Iterator cond_it = conditions.iterator();
    while (cntxt_it.hasNext()) {
        AlgebraTerm context = (AlgebraTerm)cntxt_it.next();
        AlgebraTerm cntxtcond = (AlgebraTerm)cond_it.next();
        // rwpair made out of condition:
        Set<AlgebraVariable> cndvars = cntxtcond.getVars();
        cndvars.retainAll(xs2);
        if (!cndvars.isEmpty()) {
        Vector<AlgebraTerm> tmpargs = new Vector<AlgebraTerm>();
        AlgebraTerm rwcond = condition.apply(tau);
        Vector<RewriteCalculusPair> rwpairs = new Vector<RewriteCalculusPair>();
        Vector<Vector<AlgebraTerm>> rwpairsTermsTypes = new Vector<Vector<AlgebraTerm>>();
        RewriteCalculusPair rwpair = new RewriteCalculusPair(rwcond, cntxtcond.apply(tau));
        rwpair.label();
        rwpairs.add(rwpair);

        // the context condition cannot be a variable...
        Vector<AlgebraTerm> rwpairTermsTypes = new Vector<AlgebraTerm>();
        rwpairTermsTypes.add(TypeTools.getResultTerm(this.obl.typeContext.getSingleTypeOf(cntxtcond.apply(tau).getSymbol()).getTypeMatrix()));
        rwpairsTermsTypes.add(rwpairTermsTypes);

            Object tmp[] = new Object[4];
        tmp[0] = cntxtcond;
        tmp[1] = rwpairs;
        tmp[2] = AlgebraFunctionApplication.create(this.obl.cTrue);;
        tmp[3] = rwpairsTermsTypes;
        mt.add(tmp);
        }
        // rwpair made out of context:
        Set<AlgebraVariable> cntxtvars = context.getVars();
        cntxtvars.retainAll(xs2);
        if (!cntxtvars.isEmpty()) {
        Vector<AlgebraTerm> tmpargs = new Vector<AlgebraTerm>();
        tmpargs.add(cntxtcond);
        tmpargs.add(condition.apply(tau));
        AlgebraTerm rwcond = AlgebraFunctionApplication.create(this.obl.fAnd, tmpargs);
        Vector<RewriteCalculusPair> rwpairs = new Vector<RewriteCalculusPair>();
        Vector<Vector<AlgebraTerm>> rwpairsTermsTypes = new Vector<Vector<AlgebraTerm>>();
        RewriteCalculusPair rwpair = new RewriteCalculusPair(rwcond, context.apply(tau));

        Vector<AlgebraTerm> rwpairTermsTypes = new Vector<AlgebraTerm>();
        // if the context is a variable, there must have been a fsym symbol before...
        if (context.apply(tau).isVariable()) {
            rwpairTermsTypes.add(TypeTools.getResultTerm(this.obl.typeContext.getSingleTypeOf(fsym).getTypeMatrix()));
        }
        else {
            rwpairTermsTypes.add(TypeTools.getResultTerm(this.obl.typeContext.getSingleTypeOf(context.apply(tau).getSymbol()).getTypeMatrix()));
        }
        rwpairsTermsTypes.add(rwpairTermsTypes);

        rwpair.label();
        rwpairs.add(rwpair);
        Object tmp[] = new Object[4];
        tmp[0] = context;
        tmp[1] = rwpairs;
        tmp[2] = cntxtcond;
        tmp[3] = rwpairsTermsTypes;
        mt.add(tmp);
        }
    }
    // Try to find suitable argument-replacements by
    // breath-first search.
    Set nonSolutions = new HashSet();
    while (!mt.isEmpty()) {
        Object tmp[] = (Object[])mt.remove(0);
        AlgebraTerm t = (AlgebraTerm)tmp[0];
        Vector<RewriteCalculusPair> rwpairs = (Vector<RewriteCalculusPair>)tmp[1];
        AlgebraTerm b = (AlgebraTerm)tmp[2];
        Vector<Vector<AlgebraTerm>> rwpairsTermsTypes = (Vector<Vector<AlgebraTerm>>)tmp[3];
        if (rwpairs.isEmpty()) {
        continue;
        }
        RewriteCalculusPair rwpair = rwpairs.remove(0);
        Vector<AlgebraTerm> rwpairTermsTypes = rwpairsTermsTypes.remove(0);
        try {
        AlgebraSubstitution sigma = t.matchesWithIdentities(rwpair.getTerms().get(0));
        // Check whether sigma represents a suitable replacement.
        List<AlgebraTerm> qs = new Vector<AlgebraTerm>();
        x_it = xs.iterator();
        while (x_it.hasNext()) {
            AlgebraVariable x = (AlgebraVariable)x_it.next();
//            qs.add(sigma.get((VariableSymbol)x.getSymbol()));
            qs.add(x.apply(sigma));
        }

        // XXX extend(...) was changed, so here the original behavior is reimplemented
        // XXX I do not know whether in this implementation sigma is ever changed
//        sigma = sigma.extend(tau);
        for(VariableSymbol vsym : tau.getDomain()) {
            if (!sigma.getDomain().contains(vsym)) {
                sigma.put(vsym, tau.get(vsym));
            }
        }

        if (nonSolutions.add(qs) && RecursionShiftSimplifier.replacementIsCandidate(xs, rs, zs, ps, qs, rsigma)) {
            if (this.replacementIsSolution(fsym, b, t, contexts, conditions, xs, sigma, tau, rwc)) {
            Vector<AlgebraTerm> rplcmts = new Vector<AlgebraTerm>();
            r_it = rs.iterator();
            x_it = xs.iterator();
            while (x_it.hasNext()) {
                AlgebraVariable x = (AlgebraVariable)x_it.next();
                AlgebraTerm r = (AlgebraTerm)r_it.next();
//                Term q = rsigma.get((VariableSymbol)x.getSymbol());
                AlgebraTerm q = x.apply(rsigma);
//                if (q == null) {
                if (q.equals(x)) {
//                q = sigma.get((VariableSymbol)x.getSymbol());
                    q = x.apply(sigma);
                }
                else {
                if (!r.equals(q)) {
                    w.add(x);
                }
                }
//                rplcmts.add(sigma.get((VariableSymbol)x.getSymbol()).apply(rsigma));
                rplcmts.add(x.apply(sigma).apply(rsigma));
            }
            return rplcmts;
            }
        }
        }
        catch (UnificationException e) { }
        rwc.caseAnalysesType = RewriteCalculus.CA_RECURSION_SHIFT;
        Pair<Vector,Vector<Vector<Vector<AlgebraTerm>>>> replacementsAndTermsTypes = rwc.proveStep(rwpair, rwpairTermsTypes);
        Vector replacements = replacementsAndTermsTypes.x;
        Vector<Vector<Vector<AlgebraTerm>>> replacementsTermsTypes = replacementsAndTermsTypes.y;
        rwc.caseAnalysesType = RewriteCalculus.CA_NORMAL;
        if (!replacements.isEmpty()) {
        Iterator nrwp_it = replacements.iterator();
        Iterator<Vector<Vector<AlgebraTerm>>> it_nrwpTermsTypes = replacementsTermsTypes.iterator();
        while (nrwp_it.hasNext()) {
            boolean mkdeepcopy = false;
            Vector<RewriteCalculusPair> newrwpairs = (Vector<RewriteCalculusPair>)nrwp_it.next();
            Vector<Vector<AlgebraTerm>> newrwpairsTermsTypes = it_nrwpTermsTypes.next();
            Vector<RewriteCalculusPair> nextrwpairs = new Vector<RewriteCalculusPair>();
            Vector<Vector<AlgebraTerm>> nextrwpairsTermsTypes = new Vector<Vector<AlgebraTerm>>();
            Iterator rwp_it = rwpairs.iterator();
            Iterator<Vector<AlgebraTerm>> it_rwpTermsTypes = rwpairsTermsTypes.iterator();
            while (rwp_it.hasNext()) {
                RewriteCalculusPair oldrwpair = (RewriteCalculusPair)rwp_it.next();
                Vector<AlgebraTerm> oldrwpairTermsTypes = it_rwpTermsTypes.next();
                nextrwpairs.add(mkdeepcopy ? oldrwpair.deepcopy() : oldrwpair);
                Vector<AlgebraTerm> oldrwpairTermsTypesDeepcopy = new Vector<AlgebraTerm>();
                if (mkdeepcopy) {
                    oldrwpairTermsTypesDeepcopy.addAll(oldrwpairTermsTypes);
                }
                nextrwpairsTermsTypes.add(mkdeepcopy ? oldrwpairTermsTypesDeepcopy : oldrwpairTermsTypes);
            }
            nextrwpairs.addAll(newrwpairs);
            nextrwpairsTermsTypes.addAll(newrwpairsTermsTypes);
            mkdeepcopy = true;
            tmp = new Object[4];
            tmp[0] = t;
            tmp[1] = nextrwpairs;
            tmp[2] = b;
            tmp[3] = nextrwpairsTermsTypes;
            mt.add(tmp);
        }
        }
    }
    return null;
    }

    private static boolean replacementIsCandidate(List<AlgebraTerm> xs, List<AlgebraTerm> rs, List<AlgebraVariable> zs, List<AlgebraTerm> ps, List<AlgebraTerm> qs, AlgebraSubstitution rsigma) {
    AlgebraSubstitution tau1 = AlgebraSubstitution.create();
    AlgebraSubstitution tau2 = AlgebraSubstitution.create();
    Iterator x_it = xs.iterator();
    Iterator p_it = ps.iterator();
    Iterator r_it = rs.iterator();
    Iterator q_it = qs.iterator();
    while (p_it.hasNext()) {
        AlgebraTerm p = (AlgebraTerm)p_it.next();
        AlgebraTerm r = (AlgebraTerm)r_it.next();
        AlgebraVariable x = (AlgebraVariable)x_it.next();
        VariableSymbol xsym = (VariableSymbol)x.getSymbol();
        AlgebraTerm q = (AlgebraTerm)q_it.next();
        if (p == null) {
        if (q == null) {
            q = r;
        }
        tau1.put(xsym, q);
        }
        else {
        tau2.put(xsym, p);
        }
    }
    x_it = xs.iterator();
    p_it = ps.iterator();
    r_it = rs.iterator();
    q_it = qs.iterator();
    while (p_it.hasNext()) {
        AlgebraTerm p = (AlgebraTerm)p_it.next();
        AlgebraVariable x = (AlgebraVariable)x_it.next();
        AlgebraTerm r = (AlgebraTerm)r_it.next();
        AlgebraTerm q = (AlgebraTerm)q_it.next();
        VariableSymbol xsym = (VariableSymbol)x.getSymbol();
//        if (p != null && rsigma.get(xsym) == null) {
        if (p != null && x.apply(rsigma).equals(x)) {
        if (q == null) {
            q = r;
        }
        if (!q.apply(tau2).equals(p.apply(tau1).apply(tau2))) {
            return false;
        }
        }
    }
    return true;
    }

    private boolean replacementIsSolution(DefFunctionSymbol fsym, AlgebraTerm b, AlgebraTerm t, List<AlgebraTerm> contexts, List<AlgebraTerm> conditions, List<AlgebraTerm> xs, AlgebraSubstitution sigma, AlgebraSubstitution tau, RewriteCalculus rwc) {
    Iterator cntxt_it = contexts.iterator();
    Iterator cond_it = conditions.iterator();
    while (cntxt_it.hasNext()) {
        AlgebraTerm context = (AlgebraTerm)cntxt_it.next();
        AlgebraTerm cond = (AlgebraTerm)cond_it.next();
        Vector<AlgebraTerm> tmpargs = new Vector<AlgebraTerm>();
        tmpargs.add(b);
        tmpargs.add(cond.apply(tau));
        cond = AlgebraFunctionApplication.create(this.obl.fAnd, tmpargs);

        AlgebraTerm contextType = null;
        // if the context is a variable, it must have been a fsym symbol before...
        if (context.apply(sigma).isVariable()) {
            contextType = TypeTools.getResultTerm(this.obl.typeContext.getSingleTypeOf(fsym).getTypeMatrix());
        }
        else {
            contextType = TypeTools.getResultTerm(this.obl.typeContext.getSingleTypeOf(context.apply(sigma).getSymbol()).getTypeMatrix());
        }

        if (!rwc.proveEquivalenceUnderCondition(context.apply(sigma), contextType, context.apply(tau), contextType, cond)) {
        return false;
        }
    }
    Iterator x_it = xs.iterator();
    while (x_it.hasNext()) {
        AlgebraVariable x = (AlgebraVariable)x_it.next();
        VariableSymbol xsym = (VariableSymbol)x.getSymbol();
//        if (!this.obl.proveDefEquivalenceUnderCondition(tau.get(xsym), sigma.get(xsym), b)) {
        if (!this.obl.proveDefEquivalenceUnderCondition(x.apply(tau), x.apply(sigma), b)) {
        return false;
        }
    }
    return true;
    }

}
