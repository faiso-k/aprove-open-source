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

@NoParams
public class ParameterEnlargementSimplifier extends SimplifierProcessor {

    private SimplifierObligation obl;
    private Map enlargements;

    public ParameterEnlargementSimplifier(){
        super("Parameter Enlargement Simplifier","PE","Parameter Enlargement");
    }

    @Override
    public SimplifierObligation simplify(SimplifierObligation oobl) {
        this.obl = oobl.shallowcopy();
        this.enlargements = new HashMap();
        if (this.parameterEnlargement()){
            this.setProof(new ParameterEnlargementProof(oobl,this.enlargements,this.obl));
            this.enlargements = null;
            return this.obl;
        }
        this.enlargements = null;
        return null;
    }

    public boolean parameterEnlargement() {
    SimplifierProcessor.log.log(Level.FINER, "Simplifier: Performing parameter-enlargement.\n");
    boolean changed = false;
    Iterator it = (new Vector(this.obl.defs)).iterator();
    while (it.hasNext()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)it.next();
            Object replacements = this.parameterEnlargement(fsym);
            if (replacements != null) {
                this.enlargements.put(fsym,replacements);
            }
        changed =  (replacements != null) || changed;
    }
    return changed;
    }

    public Object parameterEnlargement(DefFunctionSymbol fsym) {
    int sig = fsym.getSignatureClass();
    if (sig == Symbol.BOOLSIG || sig == Symbol.SELECTORSIG) {
        return null;
    }
    BigInteger suitablePositions = this.obl.getUnchangedPositions(fsym);
    suitablePositions = suitablePositions.and(this.obl.getPositionsWithoutMatching(fsym));
    if (suitablePositions.equals(BigInteger.ZERO)) {
        return null;
    }
    // In every rule the variables of the arguments given by
    // suitablePositions shall have the same names.
    Set<Rule> rules = new HashSet<Rule>();
    Iterator it = ((Set<Rule>)this.obl.defsrules.get(fsym)).iterator();
    Rule rule = (Rule)it.next();
    rules.add(rule);
    Vector<AlgebraTerm> normvars = new Vector<AlgebraTerm>();
    int i = 0;
    Iterator a_it = rule.getLeft().getArguments().iterator();
    while (a_it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)a_it.next();
        if (suitablePositions.testBit(i)) {
        normvars.add(arg);
        }
        i++;
    }
    while (it.hasNext()) {
        rule = (Rule)it.next();
        AlgebraTerm left = rule.getLeft();
        AlgebraTerm right = rule.getRight();
        AlgebraSubstitution sigma = AlgebraSubstitution.create();
        Iterator nv_it = normvars.iterator();
        i = 0;
        a_it = left.getArguments().iterator();
        while (a_it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)a_it.next();
        if (suitablePositions.testBit(i++)) {
            sigma.put((VariableSymbol)arg.getSymbol(), (AlgebraTerm)nv_it.next());
        }
        }
        rules.add(Rule.create(rule.getConds(), left.apply(sigma), right.apply(sigma)));
    }
    // Compute a set of subterms of the rhs of the rules
    Set<AlgebraTerm> terms = new LinkedHashSet<AlgebraTerm>();

    Set<AlgebraTerm> termsTypes = new LinkedHashSet<AlgebraTerm>();

    Vector<Pair<AlgebraTerm,AlgebraTerm>> fifo = new Vector<Pair<AlgebraTerm,AlgebraTerm>>();
    it = rules.iterator();
    while (it.hasNext()) {
        Rule r = (Rule)it.next();
        AlgebraTerm rLeftTypeM = this.obl.typeContext.getSingleTypeOf(r.getLeft().getSymbol()).getTypeMatrix();
        fifo.add(new Pair<AlgebraTerm,AlgebraTerm>(r.getRight() , rLeftTypeM));
    }
    while (!fifo.isEmpty()) {
        Pair<AlgebraTerm,AlgebraTerm> pair = fifo.remove(0);
        AlgebraTerm t = pair.x;
        AlgebraTerm tTypeM;
        if (!t.isVariable()) {
            tTypeM = this.obl.typeContext.getSingleTypeOf(t.getSymbol()).getTypeMatrix();
        }
        else {
            tTypeM = pair.y;
        }

        Set<AlgebraVariable> vars = t.getVars();
        if (!vars.isEmpty() && normvars.containsAll(vars)) {
        boolean b = true;
        Iterator f_it = t.getDefFunctionSymbols().iterator();
        while (b && f_it.hasNext()) {
            DefFunctionSymbol gsym = (DefFunctionSymbol)f_it.next();
            b = gsym.getTermination() && !this.obl.getDependencies(gsym).contains(fsym);
        }
        if (b) {
            terms.add(t);
            termsTypes.add(TypeTools.getResultTerm(tTypeM));
            continue;
        }
        }
        if (!t.isVariable()) {
        if (fsym.equals(t.getSymbol())) {
            i = 0;
            a_it = t.getArguments().iterator();
            Iterator<AlgebraTerm> argType_it = TypeTools.getFunctionArgs(tTypeM).iterator();
            while (a_it.hasNext()) {
            AlgebraTerm arg = (AlgebraTerm)a_it.next();
            AlgebraTerm argType = argType_it.next();
            if (!suitablePositions.testBit(i++)) {
                fifo.add(new Pair<AlgebraTerm,AlgebraTerm>(arg, argType));
            }
            }
        }
        else {
            a_it = t.getArguments().iterator();
            Iterator<AlgebraTerm> argType_it = TypeTools.getFunctionArgs(tTypeM).iterator();
            while(a_it.hasNext()) {
                AlgebraTerm arg = (AlgebraTerm)a_it.next();
                AlgebraTerm argType = argType_it.next();
                fifo.add(new Pair<AlgebraTerm,AlgebraTerm>(arg, argType));
            }
        }
        }
    }
    boolean b = true;
    while (b) {
        b = false;
        AlgebraTerm t1 = null;
        AlgebraTerm t1Type = null;
        AlgebraTerm t2 = null;
        AlgebraTerm t2Type = null;
        Position pi1 = null;
        Position pi2 = null;
        Iterator t_it1 = terms.iterator();
        Iterator<AlgebraTerm> tType_it1 = termsTypes.iterator();
        while (!b && t_it1.hasNext()) {
        t1 = (AlgebraTerm)t_it1.next();
        t1Type = tType_it1.next();
        Iterator t_it2 = terms.iterator();
        Iterator<AlgebraTerm> tType_it2 = termsTypes.iterator();
        while (!b && t_it2.hasNext()) {
            t2 = (AlgebraTerm)t_it2.next();
            t2Type = tType_it2.next();
            if (t1.equals(t2)) {
            continue;
            }
            Iterator p_it1 = t1.getPositions().iterator();
            while (!b && p_it1.hasNext()) {
            pi1 = (Position)p_it1.next();
            AlgebraTerm st1 = t1.getSubterm(pi1);
            if (st1.getVars().isEmpty()) {
                continue;
            }
            if (!pi1.isRootPosition() && t1.isVariable()) {
                continue;
            }
            Iterator p_it2 = t2.getPositions().iterator();
            while (!b && p_it2.hasNext()) {
                pi2 = (Position)p_it2.next();
                AlgebraTerm st2 = t2.getSubterm(pi2);
                if (!(st1.equals(st2))) {
                continue;
                }
                if (!pi1.isRootPosition() && !t1.getSubterm(pi1.pred()).isSubtermOf(st2)) {
                continue;
                }
                b = true;
            }
            }
        }
        }
        if (b) {
        terms.remove(t1);
        termsTypes.remove(t1Type);
        terms.remove(t2);
        termsTypes.remove(t2Type);
        AlgebraTerm subt1Type;
        if (pi1.isRootPosition()) {
            subt1Type = t1Type;
        }
        else {
            Position pi1pred = pi1.pred();
            int j = pi1.getLast();
            subt1Type = TypeTools.getFunctionArgAt(this.obl.typeContext.getSingleTypeOf(t1.getSubterm(pi1pred).getSymbol()).getTypeMatrix(), j);
        }
        terms.add(t1.getSubterm(pi1));
        termsTypes.add(subt1Type);
        if (!pi1.isRootPosition()) {
            i = pi1.getLast();
            Position pi = pi1.pred();
            AlgebraTerm t = t1.getSubterm(pi);
            AlgebraTerm tTypeM = this.obl.typeContext.getSingleTypeOf(t.getSymbol()).getTypeMatrix();
            int j = 0;
            a_it = t.getArguments().iterator();
            Iterator<AlgebraTerm> argType_it = TypeTools.getFunctionArgs(tTypeM).iterator();
            while (a_it.hasNext()) {
            AlgebraTerm arg = (AlgebraTerm)a_it.next();
            AlgebraTerm argType = argType_it.next();
            if (j!=i && !arg.getVars().isEmpty()) {
                terms.add(arg);
                termsTypes.add(argType);
            }
            j++;
            }
        }
        if (!pi2.isRootPosition()) {
            i = pi2.getLast();
            Position pi = pi2.pred();
            AlgebraTerm t = t2.getSubterm(pi);
            AlgebraTerm tTypeM = this.obl.typeContext.getSingleTypeOf(t.getSymbol()).getTypeMatrix();
            int j = 0;
            a_it = t.getArguments().iterator();
            Iterator<AlgebraTerm> argType_it = TypeTools.getFunctionArgs(tTypeM).iterator();
            while (a_it.hasNext()) {
            AlgebraTerm arg = (AlgebraTerm)a_it.next();
            AlgebraTerm argType = argType_it.next();
            if (j!=i && !arg.getVars().isEmpty()) {
                terms.add(arg);
                termsTypes.add(argType);
            }
            j++;
            }
        }
        }
    }
    if (normvars.containsAll(terms)) {
        return null;
    }
    // Do the transformation.
    Hashtable replacements = new Hashtable();
    Vector<AlgebraTerm> zs = new Vector<AlgebraTerm>();
    Vector<AlgebraTerm> zsTypes = new Vector<AlgebraTerm>();
    i = 0;
    it = terms.iterator();
    Iterator<AlgebraTerm> tType_it = termsTypes.iterator();
    while (it.hasNext()) {
        AlgebraTerm t = (AlgebraTerm)it.next();
        AlgebraTerm tType = tType_it.next();
        if (t.isVariable()) {
        zs.add(t);
        zsTypes.add(tType);
        }
        else {
        String name = this.obl.symbnames.getFreshName("z_"+(i+1), true);
        AlgebraVariable v = AlgebraVariable.create(VariableSymbol.create(name, t.getSymbol().getSort()));
        replacements.put(t, v);
        zs.add(v);
        zsTypes.add(tType);
        }
    }

    // TODO removal of sorts
    Vector<Sort> sorts = new Vector<Sort>();
    Iterator<Sort> s_it = fsym.getArgSorts().iterator();

    Vector<AlgebraTerm> argTypes = new Vector<AlgebraTerm>();

    i = 0;

    AlgebraTerm fsymTypeM = this.obl.typeContext.getSingleTypeOf(fsym).getTypeMatrix();
    Iterator<AlgebraTerm> argType_it = TypeTools.getFunctionArgs(fsymTypeM).iterator();

    while (argType_it.hasNext()) {
        AlgebraTerm argType = argType_it.next();

        // TODO removal of sorts
        Sort s = s_it.next();

        if (!suitablePositions.testBit(i++)) {
            argTypes.add(argType);

            // TODO removal of sorts
            sorts.add(s);

        }
    }
    it = zs.iterator();
    Iterator<AlgebraTerm> zsType_it = zsTypes.iterator();
    while (it.hasNext()) {
        AlgebraVariable v = (AlgebraVariable)it.next();
        sorts.add(v.getSymbol().getSort());
        argTypes.add(zsType_it.next());
    }
    String name = this.obl.symbnames.getFreshName(fsym.getName(), false);
    DefFunctionSymbol fnsym = DefFunctionSymbol.create(name, sorts, fsym.getSort());

    this.obl.typeContext.setSingleTypeOf(fnsym, new Type(TypeTools.function(argTypes, TypeTools.getResultTerm(fsymTypeM))));

    Set<Rule> newrules = new HashSet<Rule>();
    it = rules.iterator();
    while (it.hasNext()) {
        rule = (Rule)it.next();
        Vector<AlgebraTerm> newargs = new Vector<AlgebraTerm>();
        i = 0;
        a_it = rule.getLeft().getArguments().iterator();
        while (a_it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)a_it.next();
        if (!suitablePositions.testBit(i++)) {
            newargs.add(arg);
        }
        }
        a_it = zs.iterator();
        while (a_it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)a_it.next();
        newargs.add(arg.deepcopy());
        }
        AlgebraTerm newleft = AlgebraFunctionApplication.create(fnsym, newargs);
        AlgebraTerm newright = this.resolveEnlargeParameters(fsym, fnsym, rule.getRight(), replacements, zs, suitablePositions);
        Vector<Rule> newconds = new Vector<Rule>();
        Iterator c_it = rule.getConds().iterator();
        while (c_it.hasNext()) {
        Rule cond = (Rule)c_it.next();
        AlgebraTerm cl = this.resolveEnlargeParameters(fsym, fnsym, cond.getLeft(), replacements, zs, suitablePositions);
        newconds.add(Rule.create(cl, cond.getRight()));
        }
        newrules.add(Rule.create(newconds, newleft, newright));
    }
    this.obl.defsrules.put(fnsym, newrules);
    this.obl.defs.add(fnsym);
    this.obl.updateSymbol(fnsym, newrules);
    newrules = new HashSet<Rule>();
    Vector<AlgebraTerm> leftargs = new Vector<AlgebraTerm>();
    Vector<AlgebraTerm> rightargs = new Vector<AlgebraTerm>();
    Iterator nv_it = normvars.iterator();
    int n = fsym.getArity();
    for (i=0; i<n; i++) {
        if (suitablePositions.testBit(i)) {
        leftargs.add((AlgebraTerm) nv_it.next());
        }
        else {
        name = this.obl.symbnames.getFreshName("x_"+(i+1), true);
        AlgebraVariable v = AlgebraVariable.create(VariableSymbol.create(name, fsym.getArgSort(i)));
        leftargs.add(v);
        rightargs.add(v.deepcopy());
        }
    }
    rightargs.addAll(terms);
    AlgebraTerm newleft = AlgebraFunctionApplication.create(fsym, leftargs);
    AlgebraTerm newright = AlgebraFunctionApplication.create(fnsym, rightargs);
    newrules.add(Rule.create(newleft, newright));
    this.obl.defsrules.put(fsym, newrules);
    this.obl.updateSymbol(fsym, newrules);
    return new Object[]{fnsym,replacements};
    }

    protected AlgebraTerm resolveEnlargeParameters(DefFunctionSymbol fsym, DefFunctionSymbol fnsym, AlgebraTerm term, Hashtable replacements, Vector<AlgebraTerm> zs, BigInteger suitablePositions) {
    if (term.isVariable()) {
        return term;
    }
    AlgebraTerm rplc = (AlgebraTerm)replacements.get(term);
    if (rplc != null) {
        return rplc;
    }
    if (fsym.equals(term.getSymbol())) {
        Vector<AlgebraTerm> newargs = new Vector<AlgebraTerm>();
        int i = 0;
        Iterator a_it = term.getArguments().iterator();
        while (a_it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)a_it.next();
        if (!suitablePositions.testBit(i++)) {
            newargs.add(this.resolveEnlargeParameters(fsym, fnsym, arg, replacements, zs, suitablePositions));
        }
        }
        a_it = zs.iterator();
        while (a_it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)a_it.next();
        newargs.add(arg.deepcopy());
        }
        return AlgebraFunctionApplication.create(fnsym, newargs);
    }
    Vector<AlgebraTerm> newargs = new Vector<AlgebraTerm>();
    Iterator a_it = term.getArguments().iterator();
    while (a_it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)a_it.next();
        newargs.add(this.resolveEnlargeParameters(fsym, fnsym, arg, replacements, zs, suitablePositions));
    }
    return AlgebraFunctionApplication.create((SyntacticFunctionSymbol)term.getSymbol(), newargs);
    }

}
