package aprove.verification.theoremprover.Simplifier;
import java.util.*;

import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;

@NoParams
public class CaseMergeSimplifier extends SimplifierProcessor {

    private SimplifierObligation obl;

    public CaseMergeSimplifier(){
        super("Case Merge Simplifier","CaseM","Case Merge");
    }

    @Override
    public SimplifierObligation simplify(SimplifierObligation oobl) {
        this.obl = oobl.shallowcopy();
        Set<DefFunctionSymbol> fsymCh = this.caseMergeTransformation();
        if (fsymCh.isEmpty()) {
            return null;
        }
        this.setProof(new CaseMergeProof(oobl,fsymCh,this.obl));
        return this.obl;
    }

    /* Case-Merge-Transform */

    public Set<DefFunctionSymbol> caseMergeTransformation() {
    Set<DefFunctionSymbol> fsymCh = new HashSet<DefFunctionSymbol>();
        Iterator it = (new Vector(this.obl.defs)).iterator();
    while (it.hasNext()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)it.next();
        int sig = fsym.getSignatureClass();
        if (sig == Symbol.MAINSIG || (sig == Symbol.DEFAULTSIG && !this.obl.isProjection(fsym))) {
        if (this.caseMergeTransformation(fsym)) {
            while (this.caseMergeTransformation(fsym)) { }
                    fsymCh.add(fsym);
        }
        }
    }
    return fsymCh;
    }

    public boolean caseMergeTransformation(DefFunctionSymbol fsym) {
    Set<Rule> rules = (Set<Rule>)this.obl.defsrules.get(fsym);
    // Compute used functions and create new name-generator.
    Set<String> used = new HashSet<String>(this.obl.symbnames.getUsedNames());
    Iterator it = rules.iterator();
    while (it.hasNext()) {
        Rule rule = (Rule)it.next();
        Iterator it2 = rule.getLeft().getVars().iterator();
        while (it2.hasNext()) {
        AlgebraVariable v = (AlgebraVariable)it2.next();
        used.add(v.getSymbol().getName());
        }
    }
    FreshNameGenerator namegen = new FreshNameGenerator(used, FreshNameGenerator.VARIABLES);
    Position epsilon = Position.create();
    it = rules.iterator();
    while (it.hasNext()) {
        Rule r1 = (Rule)it.next();
        if (!r1.getConds().isEmpty()) {
        continue;
        }
        AlgebraTerm left1 = r1.getLeft();
        Iterator p_it = left1.getPositions().iterator();
        while (p_it.hasNext()) {
        Position pos = (Position)p_it.next();
        if (pos.equals(epsilon)) {
            continue;
        }
        AlgebraTerm t = left1.getSubterm(pos);
        if (t.isVariable()) {
            continue;
        }
        Iterator a_it = t.getArguments().iterator();
        boolean only_variables = true;
        while (only_variables && a_it.hasNext()) {
            AlgebraTerm arg = (AlgebraTerm)a_it.next();
            if (!arg.isVariable()) {
            only_variables = false;
            }
        }
        if (!only_variables) {
            continue;
        }
        // Generalize at position pos.
        String name = namegen.getFreshName("z", true);
        VariableSymbol zsym = VariableSymbol.create(name, t.getSymbol().getSort());
        AlgebraVariable z = AlgebraVariable.create(zsym);
        AlgebraTerm gleft1 = left1.replaceAt(z, pos);
        Hashtable replacements = new Hashtable();
        this.obl.getLiftReplacements(t, replacements, z);
        AlgebraTerm gright1 = r1.getRight().termReplace(replacements);
        // Now gleft1 -> gright1 is the generalized form of r1
        // Let us see which rules are matched by that.
        Vector<Rule> matchrules = new Vector<Rule>();
        boolean matches_too_much = false;
        Iterator r_it = rules.iterator();
        while (r_it.hasNext()) {
            Rule r2 = (Rule)r_it.next();
            AlgebraTerm left2 = r2.getLeft();
            try {
            AlgebraSubstitution sub = gleft1.matches(left2);
            sub.remove(zsym);
            if (!sub.isVariableRenaming()) {
                matches_too_much = true;
                break;
            }
            AlgebraTerm t2 = left1.getSubterm(pos);
            AlgebraTerm gleft2 = left2.replaceAt(z, pos);
            replacements = new Hashtable();
            this.obl.getLiftReplacements(t2, replacements, z);
            AlgebraTerm gright2 = r2.getRight().termReplace(replacements);
            matchrules.add(Rule.create(gleft2, gright2));
            }
            catch (UnificationException e) { }
        }
        if (matches_too_much || matchrules.size() < 2) {
            continue;
        }
        boolean all_equal = true;
        r_it = matchrules.iterator();
        while (all_equal && r_it.hasNext()) {
            Rule r2 = (Rule)r_it.next();
            AlgebraTerm gleft2 = r2.getLeft();
            AlgebraTerm gright2 = r2.getRight();
            AlgebraSubstitution sub = null;
            try {
            sub = gleft1.matches(gleft2);
            }
            catch (UnificationException e) { }
            all_equal = gright1.equals(gright2.apply(sub));
        }
        if (all_equal) {
            Set<Rule> newrules = new HashSet<Rule>();
            r_it = rules.iterator();
            while (r_it.hasNext()) {
            Rule r = (Rule)r_it.next();
            if (!gleft1.isMatchable(r.getLeft())) {
                newrules.add(r);
            }
            }
            newrules.add(Rule.create(gleft1, gright1));
            this.obl.defsrules.put(fsym, newrules);
            return true;
        }
        }
    }
    return false;
    }

}
