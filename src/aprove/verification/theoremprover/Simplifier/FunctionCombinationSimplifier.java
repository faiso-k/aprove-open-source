package aprove.verification.theoremprover.Simplifier;

import java.util.*;
import java.util.logging.*;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

@NoParams
public class FunctionCombinationSimplifier extends SimplifierProcessor {

    private SimplifierObligation obl;
    private Vector combineInfo;

    public FunctionCombinationSimplifier(){
        super("Function Combination Simplifier","FC","Function Combination");
    }

    @Override
    public SimplifierObligation simplify(SimplifierObligation oobl) {
        this.obl = oobl.shallowcopy();
        this.combineInfo = new Vector();
        if (this.combineFunctions()) {
           this.setProof(new FunctionCombinationProof(oobl,this.combineInfo,this.obl));
           this.combineInfo = null;
           return this.obl;
        }
        this.combineInfo = null;
        return null;
    }

    /* Function-Combination (Transformation) */

    /** Performs function-combinations on the current functions.
     */
    public boolean combineFunctions() {
    SimplifierProcessor.log.log(Level.FINER, "Simplifier: Performing combination of functions.\n");
    Hashtable origin = new Hashtable();
    Vector<DefFunctionSymbol> fifo = new Vector<DefFunctionSymbol>();
    boolean changed = false;
    Iterator it = this.obl.getDependenciesOrder().iterator();
    while (it.hasNext()) {
        DefFunctionSymbol f = (DefFunctionSymbol)it.next();
        origin.put(f,f);
        fifo.add(f);
    }
    while (!fifo.isEmpty()) {
        DefFunctionSymbol f = (DefFunctionSymbol)fifo.remove(0);
        Vector<AlgebraTerm> gterms = new Vector<AlgebraTerm>();
        Vector<VariableSymbol> ys = new Vector<VariableSymbol>();
        AlgebraTerm q = this.getCombineTerm(f, ys, gterms);
        if (q == null) {
        continue;
        }
        // check whether origin(f)>origin(g_i) f.a. i
        // and whether one of the g_i is directly recursive
        // and make the vector of function-symbols according to gterms
        boolean allgreater = true;
        boolean hasDirectRecursion = false;
        Vector<DefFunctionSymbol> gs = new Vector<DefFunctionSymbol>();
        Iterator it2 = gterms.iterator();
        while (it2.hasNext()) {
        DefFunctionSymbol g = (DefFunctionSymbol)((AlgebraTerm)it2.next()).getSymbol();
        gs.add(g);
        if (!this.obl.greater_dep((DefFunctionSymbol)origin.get(f), (DefFunctionSymbol)origin.get(g))) {
            allgreater = false;
        }
        if (this.obl.isDirectlyRecursive(g)) {
            hasDirectRecursion = true;
        }
        }
        if (!allgreater) {
        continue;
        }
        if (hasDirectRecursion) {
        it2 = q.getDefFunctionSymbols().iterator();
        boolean h_depends_on_f = false;
        while (it2.hasNext()) {
            DefFunctionSymbol h = (DefFunctionSymbol)it2.next();
            if (this.obl.dependsOn(h,f)) {
            h_depends_on_f = true;
            break;
            }
        }
        if (h_depends_on_f) {
            continue;
        }
        }
            Vector<DefFunctionSymbol> combi = new Vector<DefFunctionSymbol>(gs);
        DefFunctionSymbol gn = this.makeCombinedFunction(q, ys, gs);
            combi.add(0,gn);
            this.combineInfo.add(combi);
        // TODO The origin of the first g is not neccessarily the best.
        origin.put(gn, origin.get(gs.get(0)));
        fifo.add(gn);
        changed = true;
    }
        this.setMessage("Combine functions");
    return changed;
    }

    /** Makes a combined function according to the sample function g, the term q and
     *  the varibles ys.
     */
    public DefFunctionSymbol makeCombinedFunction(AlgebraTerm q, Vector<VariableSymbol> ys, Vector<DefFunctionSymbol> gs) {
    Set<Rule> gnrules = new HashSet<Rule>();
    DefFunctionSymbol g1 = (DefFunctionSymbol)gs.remove(0);
    VariableSymbol y1 = (VariableSymbol)ys.remove(0);
    String name = this.obl.symbnames.getFreshName("comb_"+g1.getName(), false);

    // TODO removal of sorts
    DefFunctionSymbol gn = DefFunctionSymbol.create(name, g1.getArgSorts(), q.getSymbol().getSort());

    // q \notin \mathcal{V} (c.f. daHaselbach pg. 75), otherwise function combination would not make sense
    // => q.getSymbol() is a FunctionSymbol and there exists a type for it
    AlgebraTerm qTypeM = this.obl.typeContext.getSingleTypeOf((SyntacticFunctionSymbol)q.getSymbol()).getTypeMatrix();

    Vector<AlgebraTerm> gnArgsTypeMs = new Vector<AlgebraTerm>();
    gnArgsTypeMs.addAll(TypeTools.getFunctionArgs(this.obl.typeContext.getSingleTypeOf(g1).getTypeMatrix()));
    Type gnType = new Type(TypeTools.function(gnArgsTypeMs, TypeTools.getResultTerm(qTypeM)));

    this.obl.typeContext.setSingleTypeOf(gn, gnType);

    // Iterate over all rules of one of the functions.
    Iterator it = ((Set)this.obl.defsrules.get(g1)).iterator();
    while (it.hasNext()) {
        Rule r = (Rule)it.next();
        AlgebraTerm left = AlgebraFunctionApplication.create(gn, r.getLeft().getArguments());
        AlgebraTerm right = r.getRight();
        List<Rule> conds = r.getConds();
        if (g1.equals(right.getSymbol())) {
        right = AlgebraFunctionApplication.create(gn, right.getArguments());
        } else {
        AlgebraSubstitution sub = AlgebraSubstitution.create();
        List<AlgebraTerm> args = left.getArguments();
        sub.put(y1, right);
        Iterator y_it = ys.iterator();
        Iterator g_it = gs.iterator();
        while (y_it.hasNext()) {
            VariableSymbol y = (VariableSymbol)y_it.next();
                    Set<Rule> g_rules = (Set<Rule>)this.obl.defsrules.get(g_it.next());
            AlgebraTerm t = SimplifierTools.getCorrespondentRuleRight(g_rules, args, r.getConds());
            sub.put(y, t);
        }
        right = q.apply(sub);
        }
            Rule nr = Rule.create(conds, left, right);
        gnrules.add(nr);
    }


        ys.insertElementAt(y1, 0);
    gs.insertElementAt(g1, 0);
    // Now replace all instantiations of q[y*/g_1(x*),...,g_m(x*)].
    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();

    Iterator s_it = gn.getArgSorts().iterator();
    for(int i=0; i<gn.getArity(); ++i) {
        Sort s = (Sort)s_it.next();
        name = this.obl.symbnames.getFreshName("x"+(i+1), true);
        VariableSymbol vsym = VariableSymbol.create(name, s);
        args.add(AlgebraVariable.create(vsym));
    }

    AlgebraSubstitution sub = AlgebraSubstitution.create();
    Iterator g_it = gs.iterator();
    Iterator y_it = ys.iterator();
    while (y_it.hasNext()) {
        VariableSymbol yi = (VariableSymbol)y_it.next();
        DefFunctionSymbol gi = (DefFunctionSymbol)g_it.next();
        sub.put(yi, AlgebraFunctionApplication.create(gi, args));
    }
    Rule rewriteRule = Rule.create(q.apply(sub), AlgebraFunctionApplication.create(gn, args));
    it = (new Vector(this.obl.defs)).iterator();
    while (it.hasNext()) {
        DefFunctionSymbol f = (DefFunctionSymbol)it.next();
        Iterator it2 = ((Set)this.obl.defsrules.get(f)).iterator();
        Set<Rule> newrules = new HashSet<Rule>();
        while (it2.hasNext()) {
        Rule r = (Rule)it2.next();
        AlgebraTerm left = r.getLeft();
        AlgebraTerm right = this.completeRewrite(r.getRight(), rewriteRule);
        if (!(right.equals(r.getRight()))) {
            Rule rn = Rule.create(r.getConds(), left, right);
            newrules.add(rn);
        }
        else {
            newrules.add(r);
        }
        }
        this.obl.defsrules.put(f, newrules);
        this.obl.updateSymbol(f, newrules);
    }
    this.obl.defsrules.put(gn, gnrules);
    this.obl.defs.add(gn);
    this.obl.updateSymbol(gn, gnrules);
    return gn;
    }

    /** Gets a possible combine-term of f. I.e. it searches for a term q
     *  in f with sigma(q[y* / g_1(t*),..,g_n(t*)]) */
    public AlgebraTerm getCombineTerm(DefFunctionSymbol f, Vector<VariableSymbol> ys, Vector<AlgebraTerm> gterms) {
    Iterator it = ((Set)this.obl.defsrules.get(f)).iterator();
    while (it.hasNext()) {
        Rule r = (Rule)it.next();
        AlgebraTerm right = r.getRight();
        List<Position> pos1 = right.getDefFunctionPositions();
        Vector<Position> pos2 = new Vector<Position>(pos1);
        Iterator it1 = pos1.iterator();
        while (it1.hasNext()) {
        pos2.remove(0);
        gterms.clear();
        ys.clear();
        Vector<Position> gpositions = new Vector<Position>();
        Position p1 = (Position)it1.next();
        AlgebraTerm t1 = right.getSubterm(p1);
        DefFunctionSymbol f1 = (DefFunctionSymbol)t1.getSymbol();
        int sig = f1.getSignatureClass();
        if (sig == Symbol.BOOLSIG || sig == Symbol.SELECTORSIG) {
            continue;
        }
        Iterator it2 = pos2.iterator();
        while (it2.hasNext()) {
            Position p2 = (Position)it2.next();
            if (p1.isIndependent(p2)) {
            AlgebraTerm t2 = right.getSubterm(p2);
            DefFunctionSymbol f2 = (DefFunctionSymbol)t2.getSymbol();
            sig = f2.getSignatureClass();
            String name = f2.getName();
            if (f1.equals(f2) || sig == Symbol.BOOLSIG || sig == Symbol.SELECTORSIG) {
                continue;
            }
            List<AlgebraTerm> args1 = t1.getArguments();
            List<AlgebraTerm> args2 = t2.getArguments();
            if (args1.size() != args2.size()) {
                continue;
            }
            boolean allequal = true;
            Iterator a_it1 = args1.iterator();
            Iterator a_it2 = args2.iterator();
            while (allequal && a_it1.hasNext()) {
                AlgebraTerm at1 = (AlgebraTerm)a_it1.next();
                AlgebraTerm at2 = (AlgebraTerm)a_it2.next();
                if (!at1.equals(at2)) {
                allequal = false;
                }
            }
            if (!allequal) {
                continue;
            }
            if (!this.functionsAreCombinable(f1, f2)) {
                continue;
            }
            // Found one suitable pair / found another suitable subterm.
            if (gterms.isEmpty()) {
                gterms.add(t1);
                gpositions.add(p1);
            }
            gterms.add(t2);
            gpositions.add(p2);
            }
        }
        if (!gterms.isEmpty()) {
            AlgebraTerm q = right;
            int i = 0;
            Iterator p_it = gpositions.iterator();
            Iterator t_it = gterms.iterator();
            while (p_it.hasNext()) {
            Position p = (Position)p_it.next();
            AlgebraTerm t = (AlgebraTerm)t_it.next();
            String name = this.obl.symbnames.getFreshName("y"+(++i), true);
            VariableSymbol y = VariableSymbol.create(name, t.getSymbol().getSort());
            q = q.replaceAt(AlgebraVariable.create(y), p);
            ys.add(y);
            }
            Position p = Position.getMaximalCommonPosition(gpositions);
            q = q.getSubterm(p);
            Vector qvsyms = new Vector();
            Iterator v_it = q.getVars().iterator();
            while (v_it.hasNext()) {
            qvsyms.add(((AlgebraTerm)v_it.next()).getSymbol());
            }
            if (ys.containsAll(qvsyms)) {
            return q;
            }
        }
        }
    }
    return null;
    }

    /** Checks whether two functions are combinable.
     */
    public boolean functionsAreCombinable(DefFunctionSymbol f, DefFunctionSymbol g) {
    if (f.getArity() != g.getArity()) {
        return false;
    }
    Set<Rule> frules = (Set<Rule>)this.obl.defsrules.get(f);
    Set<Rule> grules = new HashSet<Rule>((Set)this.obl.defsrules.get(g));
    if (frules.size() != grules.size()) {
        return false;
    }
    Iterator it = frules.iterator();
    while (it.hasNext()) {
        Rule fr = (Rule)it.next();
        AlgebraTerm fleft = fr.getLeft();
        AlgebraTerm fright = fr.getRight();
        List<Rule> fconds = fr.getConds();
        boolean fr_is_rec = f.equals(fr.getRight().getSymbol());
        boolean b = false;
        Iterator it2 = grules.iterator();
        while (it2.hasNext()) {
        Rule gr = (Rule)it2.next();
        AlgebraTerm gleft = gr.getLeft();
        AlgebraTerm gright = gr.getRight();
        List<Rule> gconds = gr.getConds();
        try {
            AlgebraSubstitution sub = AlgebraSubstitution.create();
            Iterator ga_it = gleft.getArguments().iterator();
            Iterator fa_it = fleft.getArguments().iterator();
            while (ga_it.hasNext()) {
            AlgebraTerm ga = (AlgebraTerm)ga_it.next();
            AlgebraTerm fa = (AlgebraTerm)fa_it.next();
            sub = ga.matches(fa, sub);
            }
            if (sub.isVariableRenaming() && fconds.size()==gconds.size()) {
            Iterator gc_it = gconds.iterator();
            Iterator fc_it = fconds.iterator();
            boolean allCondsAreEqual = true;
            while (allCondsAreEqual && gc_it.hasNext()) {
                Rule gc = (Rule)gc_it.next();
                Rule fc = (Rule)fc_it.next();
                allCondsAreEqual = fc.getLeft().equals(gc.getLeft().apply(sub)) && fc.getRight().equals(gc.getRight().apply(sub));
            }
            if (allCondsAreEqual) {
                boolean gr_is_rec = g.equals(gr.getRight().getSymbol());
                if (gr_is_rec && fr_is_rec) {
                ga_it = gleft.apply(sub).getArguments().iterator();
                fa_it = fleft.getArguments().iterator();
                boolean allequal = true;
                while (allequal && ga_it.hasNext()) {
                    AlgebraTerm ga = (AlgebraTerm)ga_it.next();
                    AlgebraTerm fa = (AlgebraTerm)fa_it.next();
                    allequal = ga.equals(fa);
                }
                if (allequal) {
                    b = true;
                    break;
                }
                else {
                    return false;
                }
                }
                if (!(gr_is_rec || fr_is_rec)) {
                b = true;
                break;
                }
                return false;
            }
            }
        }
        catch (Exception e) { }
        }
        if (b) {
        it2.remove();
        }
        else {
        return false;
        }
    }
    return true;
    }

    public AlgebraTerm completeRewrite(AlgebraTerm term, Rule rule) {
    Iterator it = SimplifierTools.getOutermostMatchingPositions(term, rule.getLeft()).iterator();
    while (it.hasNext()) {
        Position position = (Position)it.next();
        AlgebraTerm subterm = term.getSubterm(position);
        AlgebraTerm rewriteRight = rule.getRight();
        AlgebraTerm rewriteLeft = rule.getLeft();
        AlgebraTerm replaced = term.getSubterm(position);
        SyntacticFunctionSymbol replacedFun = (SyntacticFunctionSymbol)replaced.getSymbol();
        try {
        AlgebraSubstitution sub = rewriteLeft.matches(subterm);
        AlgebraTerm rewritten = rule.getRight().apply(sub);
        term = term.replaceAt(rewritten, position);
        }
        catch (UnificationException e) { }
    }
    return term;
    }

}
