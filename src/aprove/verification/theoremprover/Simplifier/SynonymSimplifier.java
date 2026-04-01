package aprove.verification.theoremprover.Simplifier;

import java.util.*;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** This class implements the synonym rule. For every main function
 *  that has only one rule and this rule has the form
 *  f(x*) -&gr; g(y*) with {x*} = {y*} the rule is replaced
 *  by the (adapted) rules of g. Every instantiation of g
 *  is replaced by a correspondent instantiation of f.
 *  Note that the synonym simplification is a special case of the
 *  function combination (with n=1). The chief difference is the
 *  heuristic of its application.
 */
@NoParams
public class SynonymSimplifier extends SimplifierProcessor {

    private SimplifierObligation obl;
    private Map synonymInfo;

    public SynonymSimplifier(){
        super("Synonym Simplifier","ST","Synonym Transfortmation");
    }

    @Override
    public SimplifierObligation simplify(SimplifierObligation oobl) {
        this.obl = oobl.shallowcopy();
        this.synonymInfo = new HashMap();
        if (this.synonymTransformation()) {
           this.setProof(new SynonymProof(oobl,this.synonymInfo,this.obl));
           this.synonymInfo = null;
           return this.obl;
        }
        this.synonymInfo = null;
        return null;
    }

    public boolean synonymTransformation() {
    boolean changed = false;
    Iterator it = (new Vector(this.obl.defs)).iterator();
    while (it.hasNext()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)it.next();
        if (fsym.getSignatureClass() != Symbol.MAINSIG) {
            continue;
        }
        Set<Rule> rules = (Set<Rule>)this.obl.defsrules.get(fsym);
        if (rules.size() != 1) {
            continue;
        }
        Iterator r_it = rules.iterator();
        Rule rule = (Rule)r_it.next();
        if (rule.getConds().size() == 0) {
        AlgebraTerm right = rule.getRight();
        Iterator p_it = right.getOutermostPositions().iterator();
        while (p_it.hasNext()) {
            Position pi = (Position)p_it.next();
            AlgebraTerm subright = right.getSubterm(pi);
            Symbol sym = subright.getSymbol();
            if ((sym instanceof DefFunctionSymbol) && !sym.equals(fsym)) {
            DefFunctionSymbol gsym = (DefFunctionSymbol)sym;
            Set<AlgebraVariable> vars = new HashSet<AlgebraVariable>();
            boolean all_vars_ok = true;
            Iterator a_it = subright.getArguments().iterator();
            while (all_vars_ok && a_it.hasNext()) {
                AlgebraTerm arg = (AlgebraTerm)a_it.next();
                if (!arg.isVariable()) {
                all_vars_ok = false;
                }
                else {
                if (!vars.add((AlgebraVariable)arg)) {
                    all_vars_ok = false;
                }
                }
            }
            if (all_vars_ok) {
                if (this.synonymTransformation(fsym, gsym, rule.getLeft(), right, pi)) {
                                this.synonymInfo.put(fsym,gsym);
                changed = true;
                break;
                }
            }
            }
        }
        }
    }
    return changed;
    }

    public boolean synonymTransformation(DefFunctionSymbol fsym, DefFunctionSymbol gsym, AlgebraTerm left, AlgebraTerm right, Position pi) {
    AlgebraTerm subright = right.getSubterm(pi);
    boolean contextIsNotEmpty = !pi.equals(Position.create());

    Set<AlgebraVariable> cntxtvars = right.replaceAt(AlgebraFunctionApplication.create(DefFunctionSymbol.create("hole",0)), pi).getVars();

    Set<Rule> newrules = new HashSet<Rule>();
    Iterator r_it = ((Set)this.obl.defsrules.get(gsym)).iterator();
    while (r_it.hasNext()) {
        Rule rule = (Rule)r_it.next();
        try {
        AlgebraSubstitution sigma = subright.matches(rule.getLeft());
        AlgebraTerm newleft = left.apply(sigma);
        AlgebraTerm newright = rule.getRight();
        if (newright.getSymbol().equals(gsym)) {
            if (contextIsNotEmpty) {
            Iterator t_it = newright.getArguments().iterator();
            while (t_it.hasNext()) {
                AlgebraTerm t = (AlgebraTerm)t_it.next();
                if (this.obl.gotDependencies(t,fsym) || this.obl.gotDependencies(t,gsym)) {
                return false;
                }
            }
            }
            // Direct recursive call: newright = f(x*)[y*/r*]
            try {
            AlgebraSubstitution tau = subright.matches(newright);
            // Check that variables occuring in the context are not changed.
            Iterator v_it = cntxtvars.iterator();
            while (v_it.hasNext()) {
                AlgebraVariable x = (AlgebraVariable)v_it.next();
                if (!x.apply(tau).equals(x.apply(sigma))) {
                return false;
                }
            }
            newright = left.apply(tau);
            }
            catch (UnificationException e) { }
        }
        else {
            if (contextIsNotEmpty && (this.obl.gotDependencies(newright,fsym) || this.obl.gotDependencies(newright,gsym))) {
            return false;
            }
            // replace all occurences of subright in right
            Set<Position> posns = right.getOutermostPositions();

            AlgebraTerm nrtmp = right.apply(sigma);
            for(Position pos : posns) {
                if (right.getSubterm(pos).equals(subright)) {
                        nrtmp = nrtmp.replaceAt(newright, pos);
                }
            }
            newright = nrtmp;
        }
        newrules.add(Rule.create(rule.getConds(), newleft, newright));
        }
        catch (UnificationException e) { }
    }
    this.obl.defsrules.put(fsym, newrules);
    this.obl.updateSymbol(fsym, newrules);
    Iterator h_it = (new Vector(this.obl.defsrules.keySet())).iterator();
    while (h_it.hasNext()) {
        DefFunctionSymbol hsym = (DefFunctionSymbol)h_it.next();
        int sig = hsym.getSignatureClass();
        if ((sig == Symbol.MAINSIG || sig == Symbol.DEFAULTSIG) && this.obl.directlyDependsOn(hsym, gsym)) {
        newrules = new HashSet<Rule>();
        r_it = ((Set)this.obl.defsrules.get(hsym)).iterator();
        while (r_it.hasNext()) {
            Rule rule = (Rule)r_it.next();
            Vector<Rule> newconds = new Vector<Rule>();
            Iterator c_it = rule.getConds().iterator();
            while (c_it.hasNext()) {
            Rule cond = (Rule)c_it.next();
            AlgebraTerm newleft = SynonymSimplifier.synonymTransformation(cond.getLeft(), left, right);
            newconds.add(Rule.create(newleft, cond.getRight()));
            }
            AlgebraTerm newright = SynonymSimplifier.synonymTransformation(rule.getRight(), left, right);
            newrules.add(Rule.create(newconds, rule.getLeft(), newright));
        }
        this.obl.defsrules.put(hsym, newrules);
        this.obl.updateSymbol(hsym, newrules);
        }
    }
    return true;
    }

    /** Every subterm that matches right with sigma is replaced by
     *  sigma(left).
     */
    public static AlgebraTerm synonymTransformation(AlgebraTerm t, AlgebraTerm left, AlgebraTerm right) {
    if (t.isVariable()) {
        return t;
    }
    SyntacticFunctionSymbol sym = (SyntacticFunctionSymbol)t.getSymbol();
    Vector<AlgebraTerm> newargs = new Vector<AlgebraTerm>();
    Iterator a_it = t.getArguments().iterator();
    while (a_it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)a_it.next();
        newargs.add(SynonymSimplifier.synonymTransformation(arg, left, right));
    }
    t = AlgebraFunctionApplication.create(sym, newargs);
    try {
        AlgebraSubstitution sigma = right.matches(t);
        t = left.apply(sigma);
    }
    catch (UnificationException e) { }
    return t;
    }

}
