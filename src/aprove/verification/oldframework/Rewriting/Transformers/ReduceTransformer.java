package aprove.verification.oldframework.Rewriting.Transformers;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/** This transformer reduces a program by removing rules that are
 *  marked deleted. It is also rechecked which symbols are functions
 *  and which are constructors.
 *  @author Christian Haselbach
 *  @version $Id$
 */

public class ReduceTransformer implements ProgramTransformer {

    protected Program program;
    protected Hashtable defsrules;
    protected Hashtable newconstructors;

    public ReduceTransformer() {
    super();
    }

    public static ReduceTransformer create() {
    return new ReduceTransformer();
    }

    @Override
    public Program transform(Program prog) {
    this.defsrules = new Hashtable();
    this.program = prog;
    Iterator it = prog.getDefFunctionSymbols().iterator();
    while (it.hasNext()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)it.next();
        this.defsrules.put(fsym, this.getRules(fsym));
    }
    this.makeConstructors();
    Program newprog = Program.create(this.makeNewRules(), prog, prog.getOriginType());
    EquationalTheory newEqns = this.makeNewEquations();
    try {
        this.addConstructors(newprog, newEqns.getConstructorSymbols());
    }
    catch(ProgramException e) {
        return null;
    }
    newprog.addEquations(this.makeNewEquations());
    newprog.isReduced = true;
    return newprog;
    }

    private void addConstructors(Program newprog, Set<SyntacticFunctionSymbol> newCons) throws ProgramException {
    newCons.removeAll(newprog.getConstructorSymbols());
    Iterator i = newCons.iterator();
    while(i.hasNext()) {
        newprog.addConstructorSymbol((ConstructorSymbol)i.next());
    }
    }

    /** Gets the rules for fsym without the deleted rules.
     */
    protected Set<Rule> getRules(DefFunctionSymbol fsym) {
    Set<Rule> rules = this.program.getRules(fsym);
    Set<Rule> newrules = new HashSet<Rule>();
    Iterator it = rules.iterator();
    while (it.hasNext()) {
        Rule r = (Rule)it.next();
        if (!this.program.getDeleted().contains(r)) {
        newrules.add(r);
        }
    }
    return newrules;
    }

    /** Makes constructors out of functions that do not have rules.
     */
    protected void makeConstructors() {
    this.newconstructors = new Hashtable();
    Iterator it = this.defsrules.entrySet().iterator();
    while (it.hasNext()) {
        Map.Entry entry = (Map.Entry)it.next();
        DefFunctionSymbol fsym = (DefFunctionSymbol)entry.getKey();
        Set<Rule> rules = (Set<Rule>)entry.getValue();
        if (rules.isEmpty()) {
        String name = fsym.getName();
        List<Sort> argsorts = fsym.getArgSorts();
        Sort sort = fsym.getSort();
        ConstructorSymbol csym = ConstructorSymbol.create(name, argsorts, sort);
        this.newconstructors.put(fsym, csym);
        }
    }
    }

    protected Set<Rule> makeNewRules() {
    Set<Rule> newrules = new HashSet<Rule>();
    Iterator it = this.defsrules.values().iterator();
    while (it.hasNext()) {
        Set<Rule> rules = (Set<Rule>)it.next();
        Iterator it2 = rules.iterator();
        while (it2.hasNext()) {
        Rule rule = (Rule)it2.next();
        newrules.add(this.makeNewRule(rule));
        }
    }
    return newrules;
    }

    protected EquationalTheory makeNewEquations() {
    EquationalTheory newequations = EquationalTheory.create();
    Iterator it = this.program.getEquations().iterator();
    while (it.hasNext()) {
        TRSEquation eq = (TRSEquation)it.next();
        newequations.add(this.makeNewEquation(eq));
    }
    return newequations;
    }

    protected Rule makeNewRule(Rule rule) {
    return Rule.create(this.makeNewTerm(rule.getLeft()), this.makeNewTerm(rule.getRight()));
    }

    protected TRSEquation makeNewEquation(TRSEquation eq) {
    return TRSEquation.create(this.makeNewTerm(eq.getOneSide()), this.makeNewTerm(eq.getOtherSide()));
    }

    protected AlgebraTerm makeNewTerm(AlgebraTerm term) {
    if (term.isVariable()) {
        return term;
    }
    SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol)term.getSymbol();
    SyntacticFunctionSymbol gsym = (SyntacticFunctionSymbol)this.newconstructors.get(fsym);
    if (gsym != null) {
        fsym = gsym;
    }
    Vector<AlgebraTerm> newargs = new Vector<AlgebraTerm>();
    Iterator it = term.getArguments().iterator();
    while (it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)it.next();
        newargs.add(this.makeNewTerm(arg));
    }
    return AlgebraFunctionApplication.create(fsym, newargs);
    }

}
