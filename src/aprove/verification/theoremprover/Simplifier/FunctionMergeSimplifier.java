package aprove.verification.theoremprover.Simplifier;

import java.util.*;
import java.util.logging.*;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

@NoParams
public class FunctionMergeSimplifier extends SimplifierProcessor {

    private SimplifierObligation obl;
    protected Map mergedWith;

    public FunctionMergeSimplifier(){
        super("Function Merge Simplifier","FM","Function Merge");
    }

    @Override
    public SimplifierObligation simplify(SimplifierObligation oobl) {
        this.obl = oobl.shallowcopy();
        this.mergedWith = new HashMap();
        if (this.functionMerge()) {
            //this.setMessage("Function Merge");
            this.setProof(new FunctionMergeProof(oobl,this.mergedWith,this.obl));
            return this.obl;
        }
        return null;
    }

     /*  Function-Merge */

    /** In every rule of every function f look for a call of a function
     *  g which depends on f and merge g into f.
     */
    public boolean functionMerge() {

    SimplifierProcessor.log.log(Level.FINER, "Simplifier: Performing merging of functions.\n");
    Vector fifo = new Vector();
    Set done = new HashSet();
    boolean anychange = false; // Tells whether anything has been changed.
    Iterator it = (new Vector(this.obl.defs)).iterator();
    while (it.hasNext()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)it.next();
        if (fsym.getSignatureClass() == Symbol.MAINSIG) {
        fifo.add(fsym);
        }
    }
    while (!fifo.isEmpty()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)fifo.remove(0);
        if (done.add(fsym)) {
        if (this.obl.defs.contains(fsym)) {
            boolean changed = false;
            DefFunctionSymbol gsym = null;
            Set<Rule> rules = (Set<Rule>)this.obl.defsrules.get(fsym);
            Set<Rule> newrules = new HashSet<Rule>();
            Iterator rule_it = rules.iterator();
            while (rule_it.hasNext()) {
            Rule rule = (Rule)rule_it.next();
            Set<Rule> replacements = this.functionMerge(fsym, rule);
            if (replacements != null) {
                changed = true;
                newrules.addAll(replacements);
            }
            else {
                newrules.add(rule);
            }
            }
            if (changed) {
            anychange = true;
            this.obl.defsrules.put(fsym, newrules);
            this.obl.updateSymbol(fsym, newrules);
            boolean b = false;
            while (this.obl.liftMatching(fsym) ||
                this.obl.conditionMatchTransformation(fsym)) {
                b = true;
            }
            if (b) {
                this.obl.symbolicEvaluation(fsym);
            }
            }
            else {
            rule_it = rules.iterator();
            while (rule_it.hasNext()) {
                Rule rule = (Rule)rule_it.next();
                Iterator gsym_it = rule.getRight().getDefFunctionSymbols().iterator();
                while (gsym_it.hasNext()) {
                gsym = (DefFunctionSymbol)gsym_it.next();
                int sig = gsym.getSignatureClass();
                if (sig == Symbol.DEFAULTSIG || sig == Symbol.MAINSIG) {
                    fifo.add(gsym);
                }
                }
                Iterator cond_it = rule.getConds().iterator();
                while (cond_it.hasNext()) {
                Rule cond = (Rule)cond_it.next();
                gsym_it = cond.getLeft().getDefFunctionSymbols().iterator();
                while (gsym_it.hasNext()) {
                    gsym = (DefFunctionSymbol)gsym_it.next();
                    int sig = gsym.getSignatureClass();
                    if (sig == Symbol.DEFAULTSIG || sig == Symbol.MAINSIG) {
                    fifo.add(gsym);
                    }
                }
                }
            }
            }
        }
        }
    }
    return anychange;
    }

    /** This functions returns true if (according to a certain heuristic) it is
     * adviseable to merge these two functions.
     */
    protected boolean isMergeable(DefFunctionSymbol fsym, DefFunctionSymbol gsym) {
    int sig = gsym.getSignatureClass();
    if (!(sig == Symbol.MAINSIG || sig == Symbol.DEFAULTSIG) || fsym.equals(gsym) || this.obl.isProjection(gsym)) {
        return false;
    }
    Set<DefFunctionSymbol> hs = new HashSet<DefFunctionSymbol>();
    Iterator r_it = ((Set)this.obl.defsrules.get(gsym)).iterator();
    while (r_it.hasNext()) {
        Rule r = (Rule)r_it.next();
        hs.addAll(r.getRight().getDefFunctionSymbols());
        Iterator c_it = r.getConds().iterator();
        while (c_it.hasNext()) {
        Rule c = (Rule)c_it.next();
        hs.addAll(c.getLeft().getDefFunctionSymbols());
        }
    }
    Iterator h_it = hs.iterator();
    while (h_it.hasNext()) {
        DefFunctionSymbol h = (DefFunctionSymbol)h_it.next();
        if (!h.equals(fsym) && this.obl.dependsOn(h, gsym)) {
        return false;
        }
    }
    return true;
    }

    /** Merges the rules of fsym into a given rule. */
    public Set<Rule> functionMerge(DefFunctionSymbol fsym, Rule rule) {
    boolean changed = false;
    Vector fifo = new Vector();
    fifo.add(rule);
    // The replacements for the rule.
    Set<Rule> replacements = new HashSet<Rule>();
    while (!fifo.isEmpty()) {
        Rule currule = (Rule)fifo.remove(0);
        AlgebraTerm right = currule.getRight();
        Position pi = null;
        DefFunctionSymbol gsym = null;
        AlgebraTerm t = null;
        Iterator p_it = right.getInnermostPositions().iterator();
        while (gsym == null && p_it.hasNext()) {
        pi = (Position)p_it.next();
        t = right.getSubterm(pi);
        try {
            gsym = (DefFunctionSymbol)t.getSymbol();
            if (!this.isMergeable(fsym, gsym)) {
            gsym = null;
            }
        }
        catch (ClassCastException e) { }
        }
        if (gsym != null) {
        // varren is used to rename the variables in g to unused names.
        AlgebraSubstitution varren = AlgebraSubstitution.create();
        Iterator r_it = ((Set)this.obl.defsrules.get(gsym)).iterator();
        while (r_it.hasNext()) {
            Rule gr = (Rule)r_it.next();
            Vector<Rule> newconds = new Vector<Rule>(currule.deepcopy().getConds());
            Iterator targ_it = t.getArguments().iterator();
            Iterator larg_it = gr.getLeft().getArguments().iterator();
            while (targ_it.hasNext()) {
            AlgebraTerm targ = (AlgebraTerm)targ_it.next();
            AlgebraTerm larg = (AlgebraTerm)larg_it.next();
            Iterator v_it = larg.getVars().iterator();
            while (v_it.hasNext()) {
                VariableSymbol vsym = (VariableSymbol)((AlgebraVariable)v_it.next()).getSymbol();
                if (varren.get(vsym) == null) {
                String name = this.obl.symbnames.getFreshName(vsym.getName()+"'", false);
                AlgebraVariable nv = AlgebraVariable.create(VariableSymbol.create(name, vsym.getSort()));
                varren.put(vsym, nv);
                }
            }
            newconds.add(Rule.create(targ.deepcopy(), larg.apply(varren)));
            }
            Iterator c_it = gr.getConds().iterator();
            while (c_it.hasNext()) {
            Rule c = (Rule)c_it.next();
            AlgebraTerm cleft = c.getLeft();
            AlgebraTerm cright = c.getRight();
            Iterator v_it = cright.getVars().iterator();
            while (v_it.hasNext()) {
                VariableSymbol vsym = (VariableSymbol)((AlgebraVariable)v_it.next()).getSymbol();
                if (varren.get(vsym) == null) {
                String name = this.obl.symbnames.getFreshName(vsym.getName()+"'", false);
                AlgebraVariable nv = AlgebraVariable.create(VariableSymbol.create(name, vsym.getSort()));
                varren.put(vsym, nv);
                }
            }
            newconds.add(Rule.create(cleft.apply(varren), cright.apply(varren)));
            }
            AlgebraTerm newright = right.replaceAt(gr.getRight().apply(varren), pi);
            fifo.add(Rule.create(newconds, currule.getLeft().deepcopy(), newright));
            changed = true;
                    this.mergedWith.put(fsym,gsym);
        }
        }
        else {
        replacements.add(currule);
        }
    }
    return changed ? replacements : null;
    }

}
