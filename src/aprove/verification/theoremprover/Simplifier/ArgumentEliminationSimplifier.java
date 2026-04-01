package aprove.verification.theoremprover.Simplifier;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.SimplifierProblem.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Rewriting.Transformers.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

@NoParams
public class ArgumentEliminationSimplifier extends SimplifierProcessor {
    private SimplifierObligation obl;

    public ArgumentEliminationSimplifier(){
        super("Argument Elimination Simplifier","AE","Argument Elimination");
    }

    @Override
    public SimplifierObligation simplify(SimplifierObligation oobl) {
        this.obl = oobl.shallowcopy();
        Vector<Rule> filterRules = this.argumentElimination();
        if (filterRules.isEmpty()) {
            return null;
        }
        this.setProof(new ArgumentEliminationProof(oobl,filterRules,this.obl));
        return this.obl;
    }

    /* Argument-Elimination (Transformation) */

    public Vector<Rule> argumentElimination() {
    SimplifierProcessor.log.log(Level.FINER, "Simplifier: Performing argument-elimination.\n");
    Set<SimpleFormula<SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>,SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>>> con = this.necessarityConstraints();
    Hashtable<DefFunctionSymbol,BigInteger> minh = this.minimalHerbrandModel(con);
        return this.eliminateArguments(minh);
    }

    /** Reduces the arguments of all functions to a minium.
     */
    public Vector<Rule> eliminateArguments(Hashtable afs) {
    Hashtable f1 = new Hashtable();
    Hashtable f2 = new Hashtable();
    return this.eliminateArguments(afs, f1, f2);
    }

    /** Reduces the arguments of all functions to a minium.
     */
    public Vector<Rule> eliminateArguments(Hashtable afs, Map f1, Map f2) {
    // Make reduced functions.
        Vector<Rule> filterRules = new Vector<Rule>();
    Vector<Pair<DefFunctionSymbol,DefFunctionSymbol>> reducedFunctions = new Vector<Pair<DefFunctionSymbol,DefFunctionSymbol>>();
    Iterator it = (new Vector<DefFunctionSymbol>(this.obl.defs)).iterator();
    while (it.hasNext()) {
        DefFunctionSymbol def = (DefFunctionSymbol)it.next();
        BigInteger af = (BigInteger)afs.get(def);
        // This rule has to be reduced if the arguments of the
        // lhs-root-symbol has more arguments than necessary,
        // e.g. it occurs in the afs-hashtable and the
        // bitfield representing the necessary argument-positions
        // is less than 2^arity(f) - 1.
        if (af != null && af.compareTo(BigInteger.ONE.shiftLeft(def.getArity()).subtract(BigInteger.ONE)) < 0) {

        DefFunctionSymbol ndef = this.makeFilteredFunctionSymbol(def, af);

        Rule r = this.makeFilteredApplication(def, ndef, af);
                filterRules.add(r);
        Set<Rule> fr = new HashSet<Rule>();
        fr.add(r);
        Set<Rule> frn = new HashSet<Rule>();
        Iterator r_it = ((Set<Rule>)this.obl.defsrules.get(def)).iterator();
        while (r_it.hasNext()) {
            r = (Rule)r_it.next();
            AlgebraTerm newleft = this.makeFilteredApplication(r.getLeft(), ndef, af);
            r = Rule.create(r.getConds(), newleft, r.getRight());
            frn.add(r);
        }
        f1.put(def, fr);
        f2.put(ndef, frn);
        reducedFunctions.add(new Pair<DefFunctionSymbol, DefFunctionSymbol>(def, ndef));
        }
        else {
        Set<Rule> fr = (Set<Rule>)this.obl.defsrules.get(def);
        f2.put(def, fr);
        }
    }
    // Rewrite all rules in f2 with the rewrite-rules in f1 and
    // check whether the rules in f2 are valid.
    Iterator<Pair<DefFunctionSymbol, DefFunctionSymbol>> redFunc_it = reducedFunctions.iterator();
    while (redFunc_it.hasNext()) {
        Pair<DefFunctionSymbol, DefFunctionSymbol> item = redFunc_it.next();
        DefFunctionSymbol fsym = item.x;
        DefFunctionSymbol fnsym = item.y;
        Set<Rule> rules = (Set<Rule>)f2.get(fnsym);
        Set<Rule> newrules = new HashSet<Rule>();
        Iterator r_it = rules.iterator();
        while (r_it.hasNext()) {
        Rule rule = (Rule)r_it.next();
                AlgebraTerm newright = this.obl.symbolicEvaluation(rule.getRight(), f1);
                if (newright == null) {
                    newright = rule.getRight();
                }
        newrules.add(Rule.create(rule.getConds(), rule.getLeft(), newright));
        }
        if (SimplifierTools.isValidSetOfRules(newrules)) {
        Set<Rule> f1rules = (Set<Rule>)f1.get(fsym);
        this.obl.defsrules.put(fsym, f1rules);
        this.obl.updateSymbol(fsym, f1rules);
        this.obl.defsrules.put(fnsym, newrules);
        this.obl.defs.add(fnsym);

        this.obl.updateSymbol(fnsym, newrules);
        }
    }
        return filterRules;
    }

    public DefFunctionSymbol makeFilteredFunctionSymbol(DefFunctionSymbol def, BigInteger af) {
    String name = this.obl.symbnames.getFreshName(def.getName(), false);

    // TODO removal of sorts
    Vector<Sort> sorts = new Vector<Sort>();

    AlgebraTerm defTypeM = this.obl.typeContext.getSingleTypeOf(def).getTypeMatrix();
    List<AlgebraTerm> defArgTypes = TypeTools.getFunctionArgs(defTypeM);
    Vector<AlgebraTerm> newArgTypes = new Vector<AlgebraTerm>();

    int arity = def.getArity();
    for (int i=0; i<arity; i++) {
        if (af.testBit(i)) {
        sorts.add(def.getArgSort(i));

        newArgTypes.add(defArgTypes.get(i));
        }
    }

    Type newDefFuncType = new Type(TypeTools.function(newArgTypes, TypeTools.getResultTerm(defTypeM)));
    DefFunctionSymbol nDefFunc = DefFunctionSymbol.create(name, sorts, def.getSort());

    this.obl.typeContext.setSingleTypeOf(nDefFunc, newDefFuncType);

    return nDefFunc;
    }

    /** Creates a rule whose lhs-rootsymbol is def and whose rhs-root-symbol
     *  is ndef. Basicly this calls the reduced ndef.
     *  @param def Old function
     *  @param ndef New filtered function
     *  @param af Argument-filter
     *  @return A rule representing the call of ndef.
     */
    public Rule makeFilteredApplication(DefFunctionSymbol def, DefFunctionSymbol ndef, BigInteger af) {
    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
    Vector<AlgebraTerm> nargs = new Vector<AlgebraTerm>();
    int arity = def.getArity();
    for (int i=0; i<arity; i++) {

        // TODO remove sorts
        Sort s = def.getArgSort(i);

        VariableSymbol sym = VariableSymbol.create(this.obl.getAVariableName(i), s);
        args.add(AlgebraVariable.create(sym));
        if (af.testBit(i)) {
        nargs.add(AlgebraVariable.create(sym));
        }
    }
    AlgebraTerm left = AlgebraFunctionApplication.create(def, args);
    AlgebraTerm right = AlgebraFunctionApplication.create(ndef, nargs);
    return Rule.create(left, right);
    }

    /** Transforms a term to use the reduced ndef. The root-symbol of t
     *  should be a corresponding def.
     *  @param t The term that is to be transformed.
     *  @param ndef The new (reduced) function.
     *  @param af Argument-filter
     *  @return the transformed term
     */
    public AlgebraTerm makeFilteredApplication(AlgebraTerm t, DefFunctionSymbol ndef, BigInteger af) {
    Vector<AlgebraTerm> nargs = new Vector<AlgebraTerm>();
    int arity = t.getArguments().size();
    for (int i=0; i<arity; i++) {
        if (af.testBit(i)) {
        try {
            nargs.add(t.getArgument(i));
        }
        catch (Exception e) { }
        }
    }
    return AlgebraFunctionApplication.create(ndef, nargs);
    }

    /** Calculates the neccessarity-constraints for a given term.
     */
    public Set<SimpleFormula<SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>,SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>>> necessarityConstraints(AlgebraTerm term, SimpleFormula<SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>,SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>> phi, SyntacticFunctionSymbol fsym, Hashtable varpos) {
    Set<SimpleFormula<SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>,SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>>> result = new HashSet<SimpleFormula<SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>,SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>>>();
    Symbol sym = term.getSymbol();
    switch (sym.getSignatureClass()) {
        case Symbol.VARSIG:
                Integer ii = (Integer) varpos.get(sym);
                if (Globals.DEBUG_MATRAF || Globals.DEBUG_SWISTE) {
                    if (ii == null) {
                        System.out.println("varpos: null for "+sym);
                    }
                }
        int pos = ii.intValue();
        result.add(SimpleFormula.createImplication(phi, SimpleFormulaPairLiteral.createLiteral(fsym, Integer.valueOf(pos))));
        break;
        case Symbol.CONSSIG:
        case Symbol.BOOLSIG:
        case Symbol.SELECTORSIG:
        Iterator it = term.getArguments().iterator();
        while (it.hasNext()) {
            AlgebraTerm t = (AlgebraTerm)it.next();
            result.addAll(this.necessarityConstraints(t, phi, fsym, varpos));
        }
        break;
        case Symbol.DEFAULTSIG:
        if (this.obl.isProjection(sym)) {
            it = term.getArguments().iterator();
            while (it.hasNext()) {
            AlgebraTerm t = (AlgebraTerm)it.next();
            result.addAll(this.necessarityConstraints(t, phi, fsym, varpos));
            }
            break;
        }
        default:
        if (((DefFunctionSymbol)sym).getTermination()) {
            int j = 0;
            it = term.getArguments().iterator();
            while (it.hasNext()) {
            AlgebraTerm t = (AlgebraTerm)it.next();
            result.addAll(this.necessarityConstraints(t, SimpleFormula.createConjunction(phi, SimpleFormulaPairLiteral.createLiteral((SyntacticFunctionSymbol)sym, Integer.valueOf(j))), fsym, varpos));
            j++;
            }
        }
        else {
            int j = 0;
            it = term.getArguments().iterator();
            while (it.hasNext()) {
            AlgebraTerm t = (AlgebraTerm)it.next();
            SimpleFormula<SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>,SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>> phiprime = SimpleFormula.createConjunction(SimpleFormulaPairLiteral.createLiteral((SyntacticFunctionSymbol)sym, Integer.valueOf(j)));
            result.addAll(this.necessarityConstraints(t, phiprime, fsym, varpos));
            j++;
            }
        }
    }
    return result;
    }

    /** Calculates the neccessarity-constraints for the current
     *  rule-set.
     */
    public Set<SimpleFormula<SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>,SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>>> necessarityConstraints() {
    Set<SimpleFormula<SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>,SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>>> result = new HashSet<SimpleFormula<SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>,SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>>>();
    Iterator it = this.obl.getDependencies(this.obl.defs).iterator();
    while (it.hasNext()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)it.next();
        Set<Rule> rules = (Set<Rule>)this.obl.defsrules.get(fsym);
        Vector<AlgebraTerm> conditions = new Vector<AlgebraTerm>();
        Vector<Rule> liftedrules = new Vector<Rule>();
        this.obl.liftRules(rules, liftedrules, conditions);
        Iterator rule_it = liftedrules.iterator();
        Iterator cond_it = conditions.iterator();
        while (rule_it.hasNext()) {
            Rule r = (Rule)rule_it.next();
            AlgebraTerm cond = (AlgebraTerm)cond_it.next();
            Hashtable<Symbol, Integer> varpos = new Hashtable<Symbol, Integer>();
            Iterator arg_it = r.getLeft().getArguments().iterator();
            int i = 0;
            while (arg_it.hasNext()) {
                AlgebraVariable v = (AlgebraVariable)arg_it.next();
                varpos.put(v.getSymbol(), Integer.valueOf(i++));
            }
            result.addAll(this.necessarityConstraints(r.getRight(), SimpleFormula.createConjunction(), fsym, varpos));
            result.addAll(this.necessarityConstraints(cond, SimpleFormula.createConjunction(), fsym, varpos));
        }
    }
    return result;
    }

    /** Calculates a minimal Herbrand-model for the given set of
     *  formulas.
     */
    public Hashtable<DefFunctionSymbol,BigInteger> minimalHerbrandModel(Set<SimpleFormula<SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>,SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>>> constraints) {
    Set<SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>> minModel = new HashSet<SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>>();
    Set<SimpleFormula<SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>,SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>>> newconstraints = new HashSet<SimpleFormula<SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>,SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>>>();
    for (SimpleFormula<SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>,SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>> phi : constraints) {
        if (phi.isFact()) {
        minModel.add(phi.getConclusion());
        }
        else {
        newconstraints.add(phi);
        }
    }
    constraints = newconstraints;
    boolean changed = true;
    while (changed) {
        changed = false;
        newconstraints = new HashSet<SimpleFormula<SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>,SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>>>();
        for (SimpleFormula<SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>,SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer>> phi : constraints) {
        if (phi.premiseContainedIn(minModel)) {
            changed = true;
            minModel.add(phi.getConclusion());
        }
        else {
            newconstraints.add(phi);
        }
        }
        constraints = newconstraints;
    }
    // Transform the set into a hashtable that assigns argument-filters
    // to function-symbols.
    Hashtable<DefFunctionSymbol,BigInteger> result = new Hashtable<DefFunctionSymbol,BigInteger>();
    for (DefFunctionSymbol def : this.obl.defsrules.keySet()) {
        result.put(def, BigInteger.ZERO);
    }
    for (SimpleFormulaPairLiteral<SyntacticFunctionSymbol,Integer> l : minModel) {
        SimplifierObligation.setArgNeeded(result, l.getKey(), l.getValue().intValue());
    }
    return result;
    }

}
