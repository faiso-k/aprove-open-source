package aprove.verification.oldframework.Rewriting;

import static aprove.verification.oldframework.Logic.YNM.*;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Algebra.Terms.Visitors.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Programs.*;
import aprove.verification.oldframework.Rewriting.Transformers.*;
import aprove.verification.oldframework.Rippling.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;
import aprove.verification.oldframework.Unification.*;
import aprove.verification.oldframework.Unification.Utility.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/** Representation of term rewriting programs.
 * Bug: We should have HashtableOfSymbols or something like that. Also make CollectionOf the base class.<br>
 * Bug: Implement a new method that returns how many non-terminating defined functions a defined function depends on. Alternatively use a graph aproach to get the true hierarchy of the program. Then slice according to equivalent functions and use this for termination proofs.<br>
 * Bug: Two def functions should be compatible if they are unifiable under a variable substitution.<br>
 * @author Peter Schneider-Kamp, Burak Emir
 * @version $Id$
 */
public class Program extends AbstractProgram implements Checkable, Serializable, HTML_Able, LaTeX_Able, PLAIN_Able, Exportable {

    private static Logger log = Logger.getLogger("aprove.verification.oldframework.Rewriting.Program");

    protected Map sig; // signature of the program
    protected Map presig; // signature of the unused predefined functions
    protected Set<Sort> sorts;  // list of all sorts
    protected Set<ConstructorSymbol> cons;   // list of all constructors
    protected Set<DefFunctionSymbol> defs;   // list of all defined functions
    protected Set<DefFunctionSymbol> predefs; // list of all unused predefined functions
    protected Map<String, Set<Rule>> defsrules; // mapping from defined function symbols to rules
    protected Map defsequations; // mapping from defined function symbols to equations
    protected Map consequations; // mapping from constructor symbols to equations
    protected Set<TRSEquation> collapse; // equations that have a variable on one side
    protected Map<Boolean, FunctionSymbolGraph> callgraph; // call structure of this program
    protected Map<Boolean, SCCGraph<DefFunctionSymbol,Object>> scc_callgraph; // condensed call structure graph
    protected DoubleHash<Boolean, DefFunctionSymbol, Set<DefFunctionSymbol>> mutrecs; // mutually recursive functions
    protected Set<Rule> deleted; // deleted rules
    protected Set<TRSEquation> deletedEqns;  // deleted equations
    protected boolean hasFriendlyNames = false;
    public boolean isReduced = false;
    private Program equationalExt = null;
    protected boolean isSimplifiable = false;
    protected boolean isFromProlog = false;

    public static final int ALL = 2107;           // all strategies
    public static final int INNERMOST = Program.ALL + 1;  // innermost strategy
    public static final int NONE = Program.ALL - 1;       // no strategy specified

    protected int strategy;
    protected boolean strategyNeeded = false;
    protected boolean complete;
    protected boolean isCS;

    protected TypeContext typeContext;

    protected Set<WaveRule> waveRules;

    protected WaveHole     waveHole;
    protected WaveFrontIn  waveFrontIn;
    protected WaveFrontOut waveFrontOut;

    // cached values
    private YNM nonOverlapping = MAYBE; // nonOverlapping and not Equational
    private YNM overlaying = MAYBE; // overlaying and not Equational
    private YNM unarySymbols = MAYBE; // only unary symbols and not Equational
    private YNM maxUnarySymbols = MAYBE; // only unary symbols and constants, not
    private YNM deterministic = MAYBE; // variable condition is satisfied

    public LAProgramProperties laProgramProperties = null;

    /*-**************
     * constructors *
     ****************/

    /* internal constructor */
    protected Program(Map sig, Map presig, Set<Sort> sorts, Set<ConstructorSymbol> cons, LinkedHashSet<DefFunctionSymbol> defs, Set<DefFunctionSymbol> predefs, Map<String,Set<Rule>> defsrules, Map defsequations, Map consequations, Set<TRSEquation> collapse, Predefined predefined) {
        this.sig = sig;
        this.presig = presig;
        this.sorts = sorts;
        this.cons = cons;
        this.defs = defs;
        this.predefs = predefs;
        this.callgraph = new Hashtable();
        this.scc_callgraph = new Hashtable();
        this.mutrecs = DoubleHash.create();
        this.defsrules = defsrules;
        this.defsequations = defsequations;
        this.consequations = consequations;
        this.collapse = collapse;

        this.type = AbstractProgram.DEFAULT;
        this.deleted = new LinkedHashSet<Rule>();
        this.deletedEqns = new LinkedHashSet<TRSEquation>();

        this.predefined = predefined;
        this.strategy = Program.NONE;
        this.complete = false;
        this.typeContext = null;

        this.waveRules = new LinkedHashSet<WaveRule>();
        this.waveHole    = null;
        this.waveFrontIn = null;
        this.waveFrontOut= null;
    }

    /** Public constructor for an empty Program.
      */
    public static Program create() {
    return new Program(new LinkedHashMap(), new LinkedHashMap(), new LinkedHashSet<Sort>(), new LinkedHashSet<ConstructorSymbol>(), new LinkedHashSet<DefFunctionSymbol>(), new LinkedHashSet<DefFunctionSymbol>(), new LinkedHashMap(), new LinkedHashMap(), new LinkedHashMap(), new HashSet<TRSEquation>(), Predefined.create());
    }
    public static Program create(Program Org) {
        return Program.create().setContext(Org);
    }

    /**
     * Create a TRS from a set of rules
     * @param prog -the program the rules where taken from
     * @param rules - the new set of rules
     */
    public static Program createWithLessRulesAs(Program prog, Set<Rule> rules) {
        Program p = Program.create(rules);
        p.nonOverlapping = (YNM)prog.nonOverlapping.or(YNM.MAYBE);
        p.overlaying = (YNM)prog.overlaying.or(MAYBE);
        p.unarySymbols = (YNM)prog.unarySymbols.or(MAYBE);
        return p;
    }

    /** Public constructor using a set of rules to create the
     *  the new program.
     */
    public static Program create(Set<Rule> rules) {
    ProgramFromRules ps = new ProgramFromRules();
    Set<Rule> r = Program.updateConsDefs(rules);
    ps.setRules(r);
    return  ps.getProgram();
    }
     public static Program create(Program Org,Set<Rule> rules) {
        return Program.create(rules).setContext(Org);
    }

    /** Public constructor using a set of rules and a set of equations to create
     *  the new program.
     */
    public static Program create(Set<Rule> rules, Set<TRSEquation> eqns) {
        ProgramFromRulesAndEquations ps = new ProgramFromRulesAndEquations();
        ps.setRules(rules);
        ps.setEquations(eqns);
        return ps.getProgram();
    }
    public static Program create(Program Org, Set<Rule> rules, Set<TRSEquation> eqns) {
        return Program.create(rules,eqns).setContext(Org);
    }

    /** Public constructor using a set of rules to create the
     *  the new program which originated from another program.
     */
    public static Program create(Set<Rule> rules, Program origin, int type) {
    Program result = Program.create(rules);
    result.origin = origin;
    result.setSimplifiable(origin.isSimplifiable());
    result.setFromProlog(origin.isFromProlog());
    result.type = type;
    return result;
    }

    protected Program setContext(Program prog){
        this.setTypeContext(prog.getTypeContext());
    return this;
    }

    public void setTypeContext(TypeContext tct) {
        this.typeContext = tct;
    }

    public TypeContext getTypeContext() {
        return this.typeContext;
    }

    public void setStrategy(int strategy) {
        this.strategy = strategy;
    }

    public int getStrategy() {
        return this.strategy;
    }

    public boolean getStrategyNeeded() {
        return this.strategyNeeded;
    }

    public void setStrategyNeeded(boolean needed) {
        this.strategyNeeded = needed;
    }

    public void setComplete(boolean complete) {
        this.complete = complete;
    }

    public boolean isComplete() {
        return this.complete;
    }

    protected void setFriendlyNames(boolean b) {
    this.hasFriendlyNames = b;
    }

    public Program createWithFriendlyNames() {
    return this.createWithFriendlyNames(AbstractProgram.TO_DEFAULT);
    }

    public Program createWithFriendlyNames(int mode) {
    Program newprog = Program.create();
    newprog.setFriendlyNames(true);
    NameGenerator ngen_mode = FreshNameGenerator.FRIENDLYNAMES;
    if (mode == AbstractProgram.TO_TTT) {
        ngen_mode = FreshNameGenerator.TTT_FRIENDLYNAMES;
    }
    else if (mode == AbstractProgram.TO_CiME) {
        ngen_mode = FreshNameGenerator.CiME_FRIENDLYNAMES;
    }
    FreshNameGenerator ngen = new FreshNameGenerator(ngen_mode);
    Iterator it = this.sorts.iterator();
    while (it.hasNext()) {
        Sort s = (Sort)it.next();
        try {
        String news = ngen.getFreshName(s.getName(),true);
        newprog.addSort(Sort.create(news));
        }
        catch (Exception e) {
                e.printStackTrace();
                throw new RuntimeException("APROVE: Internal Error");
        }
    }
    it = this.sorts.iterator();
    while (it.hasNext()) {
        Sort s = (Sort)it.next();
        String news = ngen.getFreshName(s.getName(),true);
        Sort ns = newprog.getSort(news);
        Iterator c_it = s.getConstructorSymbols().iterator();
        while (c_it.hasNext()) {
        ConstructorSymbol c = (ConstructorSymbol)c_it.next();
        List<Sort> nas = new Vector<Sort>();
        Iterator a_it = c.getArgSorts().iterator();
        while (a_it.hasNext()) {
            Sort s1 = (Sort)a_it.next();
            nas.add(newprog.getSort(ngen.getFreshName(s1.getName(), true)));
        }
        ConstructorSymbol c1 = ConstructorSymbol.create(ngen.getFreshName(c.getName(), true), nas, ns);
        if (mode == AbstractProgram.TO_CiME || (mode == AbstractProgram.TO_TTT  && c1.isTTTValid())) {
            c1.setFixity(c.getFixity(), c.getFixityLevel());
        }
        ns.addConstructorSymbol(c1);
        try {
            newprog.addFunctionSymbol(c1);
        }
        catch (Exception e) {
                    e.printStackTrace();
                    throw new RuntimeException("APROVE: Internal Error");
        }
        }
    }
    it = this.defs.iterator();
    while (it.hasNext()) {
        SyntacticFunctionSymbol f = (SyntacticFunctionSymbol)it.next();
        List<Sort> nas = new Vector<Sort>();
        Iterator a_it = f.getArgSorts().iterator();
        while (a_it.hasNext()) {
        Sort s1 = (Sort)a_it.next();
        nas.add(newprog.getSort(ngen.getFreshName(s1.getName(), true)));
        }
        String s = ngen.getFreshName(f.getName(),true);
        DefFunctionSymbol f1 = DefFunctionSymbol.create(s,nas,newprog.getSort(ngen.getFreshName(f.getSort().getName(),true)));
        if (mode == AbstractProgram.TO_CiME || (mode == AbstractProgram.TO_TTT && f1.isTTTValid())) {
        f1.setFixity(f.getFixity(), f.getFixityLevel());
        }
        try {
        newprog.addDefFunctionSymbol(f1);
        }
        catch (Exception e) {
                e.printStackTrace();
                throw new RuntimeException("APROVE: Internal Error");
        }
    }
    it = this.defsrules.keySet().iterator();
    while (it.hasNext()) {
        String f = (String)it.next();
        // Ignore rules of unused predefined functions.
        if (this.getDefFunctionSymbol(f) == null) {
        continue;
        }
        Set<Rule> rules = this.defsrules.get(f);
        Iterator r_it = rules.iterator();
        while (r_it.hasNext()) {
        Rule r = (Rule)r_it.next();
        newprog.addRule(r.createWithFriendlyNames(ngen, newprog));
        }
    }
    it = this.defsequations.keySet().iterator();
    while (it.hasNext()) {
        String f = (String)it.next();
        EquationalTheory et = (EquationalTheory)this.defsequations.get(f);
        EquationalTheory net = EquationalTheory.create();
        Iterator e_it = et.iterator();
        while (e_it.hasNext()) {
        TRSEquation eq = (TRSEquation)e_it.next();
        TRSEquation neq = eq.createWithFriendlyNames(ngen, newprog);
        if (neq == null) {
            Program.log.log(Level.SEVERE, "In creating with friendly names:\n   unable to convert equation "+eq+
                ".\n   This is probably due to a known bug. Output might be incorrect.\n");
            continue;
        }
        net.add(neq);
        }
        if (!net.isEmpty()) {
            newprog.addEquations(net);
        }
    }
    it = this.consequations.keySet().iterator();
    while (it.hasNext()) {
        String f = (String)it.next();
        EquationalTheory et = (EquationalTheory)this.consequations.get(f);
        EquationalTheory net = EquationalTheory.create();
        Iterator e_it = et.iterator();
        while (e_it.hasNext()) {
        TRSEquation eq = (TRSEquation)e_it.next();
        TRSEquation neq = eq.createWithFriendlyNames(ngen, newprog);
        if (neq == null) {
            Program.log.log(Level.SEVERE, "In creating with friendly names:\n   unable to convert equation "+eq+
                ".\n   This is probably due to a known bug. Output might be incorrect.\n");
            continue;
        }
        net.add(neq);
        }
        if (!net.isEmpty()) {
            newprog.addEquations(net);
        }
    }
    it = this.collapse.iterator();
    EquationalTheory net = EquationalTheory.create();
    while (it.hasNext()) {
        TRSEquation eq = (TRSEquation)it.next();
        TRSEquation neq = eq.createWithFriendlyNames(ngen, newprog);
        if (neq == null) {
           Program.log.log(Level.SEVERE, "In creating with friendly names:\n   unable to convert equation "+eq+
                ".\n   This is probably due to a known bug. Output might be incorrect.\n");
        continue;
        }
        net.add(neq);
    }
    if (!net.isEmpty()) {
        newprog.addEquations(net);
    }
        newprog.setStrategy(this.getStrategy());
    return newprog;
    }

    /*-******************
     * accessor methods *
     ********************/

    /**
     * Get the call structure graph for this program.
     */
    public FunctionSymbolGraph getCallGraph(boolean onlyRight) {
        FunctionSymbolGraph result = this.callgraph.get(onlyRight);
        if (result != null) {
            return result;
        }
        result = new FunctionSymbolGraph(this, onlyRight);
        this.callgraph.put(onlyRight, result);
        return result;
    }

    public SCCGraph<DefFunctionSymbol,Object> getSccCallGraph(boolean onlyRight) {
        SCCGraph<DefFunctionSymbol,Object> result = this.scc_callgraph.get(onlyRight);
        if (result != null) {
            return result;
        }
        result = new SCCGraph<DefFunctionSymbol,Object>(this.getCallGraph(onlyRight));
        this.scc_callgraph.put(onlyRight, result);
        return result;
    }

    /**
     * Get all mutual recursive functions for a given function symbol.
     */
    public Set<DefFunctionSymbol> getMutualRecursiveFunctions(DefFunctionSymbol def, boolean onlyRight) {
        Set<DefFunctionSymbol> result = this.mutrecs.get(onlyRight, def);
        if (result != null) {
            return result;
        }
        SCCGraph scc_callgraph = this.getSccCallGraph(onlyRight);
        Cycle scc = scc_callgraph.getSccFromObject(def);
        result = new LinkedHashSet<DefFunctionSymbol>();
        Iterator i = scc.getNodeObjects().iterator();
        while (i.hasNext()) {
            result.add((DefFunctionSymbol)i.next());
        }
        this.mutrecs.put(onlyRight, def, result);
        return result;
    }

    /**
     * Get direct dependencies of this symbol not regarding mutual recursion.
     */
    public Set<DefFunctionSymbol> getDirectDependencies(DefFunctionSymbol def, Comparator comp) throws InterruptedException {
        Set<DefFunctionSymbol> defs = new TreeSet<DefFunctionSymbol>(comp);
        FunctionSymbolGraph fsg = this.getCallGraph(true);
        Iterator i = fsg.getOut(fsg.getNodeFromObject(def)).iterator();
        while (i.hasNext()) {
            Node node = (Node)i.next();
            defs.add((DefFunctionSymbol) node.getObject());
        }
        defs.removeAll(this.getMutualRecursiveFunctions(def, true));
        return defs;
    }


    public Set<DefFunctionSymbol> getDependencies(Set<DefFunctionSymbol> defs) {
        FunctionSymbolGraph fsg = this.getCallGraph(true);
        Cycle reach = new Cycle();
        reach.addAll(fsg.determineReachableNodes(fsg.getNodesFromObjects(defs)));
        Set<DefFunctionSymbol> res = new LinkedHashSet<DefFunctionSymbol>(reach.getNodeObjects());
        res.removeAll(defs);
        return res;
    }

    /** Accessor function returning a list of this program's sorts.
     */
    public List<Sort> getListOfSorts() {
    return new Vector<Sort>(this.sorts);
    }

    /** Accessor function returning the set of sorts.
     *  <p>
     *  Note: Changing the returned set changes the program.
     */
    public Set<Sort> getSorts() {
    return this.sorts;
    }

    /** Accessor function for a sort using its name
     */
    public Sort getSort(String name) {
    Object o = this.sig.get(name);
    if (o instanceof Sort) {
        return (Sort)o;
    } else {
        return null;
    }
    }

    /** Adds a sort to the program.
     *  <p>
     *  Note: Trying to add a sort with a name that is already used will
     *  throw a ProgramException.
     */
    public void addSort(Sort sort) throws ProgramException {
    if (sort != null) {
        if (this.sig.get(sort.getName()) == null) {
            this.sorts.add(sort);
            this.sig.put(sort.getName(), sort);
        } else {
            throw new ProgramException("program already has sort '"+sort.getName()+"'");
        }
    }
    }

    /** Accessor function returning a list of this program's constructor symbols.
     */
    public List<ConstructorSymbol> getListOfConstructorSymbols() {
        return new Vector<ConstructorSymbol>(this.cons);
    }

    /** Accessor function returning a list of constructor symbols.
     *  <p>
     *  Note: Changing the returned set changes the program.
     */
    public Set<ConstructorSymbol> getConstructorSymbols() {
    return this.cons;
    }

    /** Accessor function for a constructor symbol using its name.
     */
    public ConstructorSymbol getConstructorSymbol(String name) {
    Object o = this.sig.get(name);
    if (o instanceof ConstructorSymbol) {
        return (ConstructorSymbol)o;
    } else {
        return null;
    }
    }

    /** Adds a constructor symbol to the program.
     *  <p>
     *  Note: Trying to add a constructor symbol with a name that is already used will
     *  throw a ProgramException.
     */
    public void addConstructorSymbol(ConstructorSymbol con) throws ProgramException {
    if (this.sig.get(con.getName()) == null) {
        this.cons.add(con);
        this.sig.put(con.getName(), con);
    } else {
        throw new ProgramException("program already has constructor '"+con.getName()+"'");
    }
    }

    /** Adds a set of constructor symbols to the program.
     *  <p>
     *  Note: Trying to add a constructor symbol with a name that is already used will
     *  throw a ProgramException.
     */
    public void addConstructorSymbols(Set<ConstructorSymbol> con) throws ProgramException {
    Iterator iterator = con.iterator();
    while (iterator.hasNext()) {
        this.addConstructorSymbol((ConstructorSymbol) iterator.next());
    };
    }

    /** Accessor function returning a list of this program's defined function symbols.
     */
    public List<DefFunctionSymbol> getListOfDefFunctionSymbols() {
    return new Vector<DefFunctionSymbol>(this.defs);
    }

    /** Accessor function returning a list of defined function symbols.
     *  <p>
     *  Note: Changing the returned set changes the program.
     */
    public Set<DefFunctionSymbol> getDefFunctionSymbols() {
    return this.defs;
    }

    /**
     * Check whether the program is empty (has no Rules)
     */
    public boolean isEmpty() {
        return this.defs.isEmpty();
    }

    /** Accessor function for a defined function symbol using its name.
     */
    public DefFunctionSymbol getDefFunctionSymbol(String name) {
    Object o = this.sig.get(name);
    if (o instanceof DefFunctionSymbol) {
        return (DefFunctionSymbol)o;
    } else {
        return null;
    }
    }

    /** Adds a defined function symbol to the program.
     *  <p>
     *  Note: Trying to add a defined function symbol with a name that is already used will
     *  throw a ProgramException.
     */
    public void addDefFunctionSymbol(DefFunctionSymbol def) throws ProgramException {
        if (this.sig.get(def.getName()) == null) {
        this.defs.add(def);
        this.sig.put(def.getName(), def);
        } else {
            throw new ProgramException("program already has defining function '"+def.getName()+"'");
    }
    }

    /** Adds a set of defined function symbols to the program.
     *  <p>
     *  Note: Trying to add a defined function symbol with a name that is already used will
     *  throw a ProgramException.
     */
    public void addDefFunctionSymbols(Set<DefFunctionSymbol> def) throws ProgramException {
    Iterator iterator = def.iterator();
    while (iterator.hasNext()) {
        this.addDefFunctionSymbol((DefFunctionSymbol) iterator.next());
    };
    }

    /** Accessor function returning a list of predefined function symbols.
     *  <p>
     *  Note: Changing the returned set changes the program.
     */
    public Set<DefFunctionSymbol> getPredefFunctionSymbols() {
    return this.predefs;
    }

    /** Accessor function for a predefined function symbol using its name.
     */
    public DefFunctionSymbol getPredefFunctionSymbol(String name) {
    Object o = this.presig.get(name);
    if (o instanceof DefFunctionSymbol) {
        return (DefFunctionSymbol)o;
    } else {
        return null;
    }
    }

    /** Move a predefined function symbol and all dependend predefined
     *  function symbol into the list of defined function symbols.
     */
    public void activatePredefFunctionSymbol(String name) throws ProgramException {
    DefFunctionSymbol def = (DefFunctionSymbol) this.presig.get(name);
        if (def == null) {
            throw new ProgramException("could not locate predefined function "+name);
        }
        if (this.sig.get(def.getName()) == null) {
            this.addDefFunctionSymbol(def);
        }
    Set<DefFunctionSymbol> dependencies = new HashSet<DefFunctionSymbol>();
    Iterator it = this.getRules(def).iterator();
    while (it.hasNext()) {
        Rule rule = (Rule)it.next();
        dependencies.addAll(rule.getLeft().getDefFunctionSymbols());
        dependencies.addAll(rule.getRight().getDefFunctionSymbols());
    }
    it = dependencies.iterator();
    while (it.hasNext()) {
        DefFunctionSymbol dep = (DefFunctionSymbol)it.next();
        if (!this.defs.contains(dep)) {
        this.activatePredefFunctionSymbol(dep.getName());
        }
    }
    }

    /** Adds a predefined function symbol to the program.
     *  <p>
     *  Note: Trying to add a defined function symbol with a name that is already used will
     *  throw a ProgramException.
     */
    public void addPredefFunctionSymbol(DefFunctionSymbol predef) throws ProgramException {
    if (this.presig.get(predef.getName()) == null) {
        this.predefs.add(predef);
        this.presig.put(predef.getName(), predef);
    } else {
        throw new ProgramException("program already has predefined function '"+predef.getName()+"'");
    }
    }

    /** Defines what kind of defining function this function-symbol is.
     */
    public void setFunctionSignature(DefFunctionSymbol sym, int sigclass) throws ProgramException {
    if (!this.defs.contains(sym) && !this.predefs.contains(sym)) {
        throw new ProgramException("Signature does not contain ''"+sym.getName()+"''");
    }
    sym.setSignatureClass(sigclass);
    }

    /** Returns the signature-class to which the given function-symbol belongs
     */
    public int getFunctionSignature(Symbol sym) {
    return sym.getSignatureClass();
    }

    /** Accessor method for getting a symbol.
     *  <p>
     *  Note: Changing the returned set changes the program.
     */
    public Symbol getSymbol(String name) {
    Object o = this.sig.get(name);
    if (o instanceof Symbol) {
        return (Symbol)o;
    } else {
        return null;
    }
    }

    /** Accessor function for a function symbol using its name.
     */
    public SyntacticFunctionSymbol getFunctionSymbol(String name) {
    Object o = this.sig.get(name);
    if (o instanceof SyntacticFunctionSymbol) {
        return (SyntacticFunctionSymbol)o;
    } else {
        return null;
    }
    }

    /** Adds a function symbol to the program.
     *  <p>
     *  Note: Trying to add a function symbol with a name that is already used will
     *  throw a ProgramException.
     */
    public void addFunctionSymbol(SyntacticFunctionSymbol f) throws ProgramException {
    if (f instanceof DefFunctionSymbol) {
        this.addDefFunctionSymbol((DefFunctionSymbol)f);
    } else {
        this.addConstructorSymbol((ConstructorSymbol)f);
    }
    }

    /*-************************
     * miscellaneous methods *
     *************************/

    /** Return a string representation of this program.
     */
    @Override
    public String toString() {
    StringBuffer temp = new StringBuffer();
    for (Iterator i = this.sorts.iterator(); i.hasNext();) {
        for (Iterator j = ((Sort)i.next()).getConstructorSymbols().iterator(); j.hasNext();){
        temp.append(((ConstructorSymbol)j.next()).toString(this)+"\n");
        }
        temp.append("\n");
        }
    for (Iterator i = this.defs.iterator(); i.hasNext();) {
        temp.append(((DefFunctionSymbol)i.next()).toString(this)+"\n");
        temp.append("\n");
    }
    if (!this.collapse.isEmpty()) {
        temp.append("collapse equations [\n");
        for (Iterator i = this.collapse.iterator(); i.hasNext();) {
        temp.append("  " + ((TRSEquation)i.next()).toString() + "\n");
        }
        temp.append("]\n");
    }
    return temp.toString();
    }

    /* extremely verbose string serialization -- DEBUG */
    public String verboseToString() {
    StringBuffer temp = new StringBuffer();
    for (Iterator i = this.sorts.iterator(); i.hasNext();) {
        Sort s = (Sort)i.next();
        temp.append("Listing constructors for sort '"+s.getName()+"':\n");
        for (Iterator j = s.getConstructorSymbols().iterator(); j.hasNext();) {
        temp.append(((ConstructorSymbol)j.next()).verboseToString());
        temp.append("\n");
        }
        temp.append("\n");
    }
    for (Iterator i = this.defs.iterator(); i.hasNext();) {
        DefFunctionSymbol f = (DefFunctionSymbol)i.next();
        temp.append("Listing rules for defined function '"+f.getName()+"':\n");
        temp.append(f.verboseToString());
        temp.append("\n\n");
    }
    return temp.toString();
    }

    public String toTRS() {
        //if (!this.hasFriendlyNames) return this.createWithFriendlyNames().toTRS();
    StringBuffer temp = new StringBuffer();
        Set<AlgebraVariable> vars = new LinkedHashSet<AlgebraVariable>();
        for (Iterator i = this.getAllRules().iterator(); i.hasNext();) {
            Rule rule = (Rule)i.next();
            temp.append(rule.toString()+"\n");
            vars.addAll(rule.getUsedVariables());
        }
    Set<TRSEquation> eqns = this.getAllEquations();
    for (Iterator i = this.getACSymbols().iterator(); i.hasNext();) {
        eqns.removeAll(this.getAllEquations((SyntacticFunctionSymbol)i.next()));
    }
    for (Iterator i = this.getCSymbols().iterator(); i.hasNext();) {
        eqns.removeAll(this.getAllEquations((SyntacticFunctionSymbol)i.next()));
    }
        for (Iterator i = eqns.iterator(); i.hasNext();) {
            TRSEquation equation = (TRSEquation)i.next();
            temp.append(equation.toString()+"\n");
            vars.addAll(equation.getUsedVariables());
        }
        StringBuffer temp2 = new StringBuffer();
        Set varnames = new LinkedHashSet();
        for (Iterator i = vars.iterator(); i.hasNext();) {
            AlgebraVariable var = (AlgebraVariable)i.next();
            String name = var.getName();
            varnames.add(name);
        }
        for (Iterator i = varnames.iterator(); i.hasNext();) {
            String name = (String)i.next();
            temp2.append(name);
            if (i.hasNext()) {
                temp2.append(", ");
            }
        }
    StringBuffer eq = new StringBuffer();
    boolean hasEq = false;
    Set<SyntacticFunctionSymbol> symbs = this.getACSymbols();
    if(!symbs.isEmpty()) {
        hasEq = true;
        eq.append("AC [");
        for (Iterator i = symbs.iterator(); i.hasNext();) {
            eq.append(((SyntacticFunctionSymbol)i.next()).getName());
            if (i.hasNext()) {
            eq.append(", ");
            }
        }
        eq.append("]\n");
    }
    symbs = this.getCSymbols();
    if(!symbs.isEmpty()) {
        hasEq = true;
        eq.append("C [");
        for (Iterator i = symbs.iterator(); i.hasNext();) {
            eq.append(((SyntacticFunctionSymbol)i.next()).getName());
            if (i.hasNext()) {
            eq.append(", ");
            }
        }
        eq.append("]\n");
    }

    if(hasEq) {
            return "["+temp2.toString()+"]\n"+eq.toString()+temp.toString();
    }
    else {
            return "["+temp2.toString()+"]\n"+temp.toString();
    }
    }

    @Override
    public String export(Export_Util o) {
        if (o instanceof HTML_Util) {
            return this.toHTML();
        } else if (o instanceof LaTeX_Util) {
            return this.toLaTeX();
        } else if (o instanceof PLAIN_Util) {
            return this.toPLAIN();
        } else {
            return this.toString();
        }
    }

    /**
     * Return a HTML representation of this program.
     */
    @Override
    public String toHTML() {
        StringBuffer temp = new StringBuffer();
        Set<AlgebraVariable> vars = new LinkedHashSet<AlgebraVariable>();
        for (Iterator i = this.getAllRules().iterator(); i.hasNext();) {
            Rule rule = (Rule)i.next();
            if (this.deleted.contains(rule)) {
                temp.append("<FONT COLOR=#CCCCCC>"+ToHTMLVisitor.escape(rule.toString())+"</FONT><BR>\n");
            } else {
                temp.append(rule.toHTML()+"<BR>\n");
            }
            vars.addAll(rule.getUsedVariables());
        }
        for (Iterator i = this.getAllEquations().iterator(); i.hasNext();) {
            TRSEquation equation = (TRSEquation)i.next();
            if (this.deletedEqns.contains(equation)) {
                temp.append("<FONT COLOR=#CCCCCC>"+equation.toString()+"</FONT><BR>\n");
            } else {
                temp.append(equation.toHTML()+"<BR>\n");
            }
            vars.addAll(equation.getUsedVariables());
        }
        Set varnames = new LinkedHashSet();
        for (Iterator i = vars.iterator(); i.hasNext();) {
            AlgebraVariable var = (AlgebraVariable)i.next();
            String name = var.getName();
            varnames.add(name);
        }
        StringBuffer temp2 = new StringBuffer();
        for (Iterator i = varnames.iterator(); i.hasNext();) {
            String name = (String)i.next();
            temp2.append(AlgebraVariable.create(VariableSymbol.create(name,null)).toHTML());
            if (i.hasNext()) {
                temp2.append(", ");
            }
        }
        String res1 = "<B>["+temp2.toString()+"]<BR>\n"+temp.toString()+"</B>";
        /*if (this.repMap != null) {
            StringBuffer dummy = new StringBuffer(this.repMap.toHTML());
            dummy.append(res1);
            res1 = dummy.toString();
        }*/
        return res1;
    }

    @Override
    public String toLaTeX() {
        StringBuffer temp = new StringBuffer();
        for (Iterator i = this.getAllRules().iterator(); i.hasNext();) {
            Rule rule = (Rule)i.next();
            if (this.isConditional()) {
                temp.append(rule.toCondLaTeX());
            } else {
              if (this.deleted.contains(rule)) {
                  temp.append(rule.toGrayLaTeX());
              } else {
                  temp.append(rule.toLaTeX());
              }
          //              temp.append(rule.toLaTeX());
            }
            if (i.hasNext()) {
                temp.append("\\\\");
            }
            temp.append("\n");
        }

    if (this.isEquational() && (temp.length()>0)) {
        temp.deleteCharAt(temp.length()-1);
        temp.append("\\\\");
        temp.append("\n");
    }

    for (Iterator i = this.getAllEquations().iterator(); i.hasNext();) {
        TRSEquation eq = (TRSEquation)i.next();
            if (this.deletedEqns.contains(eq)) {
                temp.append(eq.toGrayLaTeX());
            } else {
                temp.append(eq.toLaTeX());
            }
        //temp.append(eq.toLaTeX());
            if (i.hasNext()) {
                temp.append("\\\\");
            }
            temp.append("\n");
    }
        String res1 = "\\begin{longtable}{rcl}\n"+temp.toString()+"\\end{longtable}\n";
        /*if (this.repMap != null) {
            StringBuffer dummy = new StringBuffer(this.repMap.toLaTeX());
            dummy.append(res1);
            res1 = dummy.toString();
        }*/
        return res1;
    }

    public String toSimpleLaTeX() {
        StringBuffer temp = new StringBuffer();
    StringBuffer newcomms = new StringBuffer();
    for (Iterator i = this.getFunctionSymbols().iterator(); i.hasNext();){
        SyntacticFunctionSymbol tmp = (SyntacticFunctionSymbol) i.next();
            String newName = ToSimpleLaTeXVisitor.escape(tmp.getName());
            String newFunName = ToLaTeXVisitor.escape(tmp.getName());
            String newDef;
            if(newFunName.equals("+") || newFunName.equals("*")) {
                newDef = newFunName;
            }
            else {
                newDef = "\\mathsf{"+newFunName+"}";
            }
            newcomms.append("\\def\\AProVEf"+newName+"{"+newDef+"}\n");
    }
        for (Iterator i = this.getAllRules().iterator(); i.hasNext();) {
            Rule rule = (Rule)i.next();
            if (this.isConditional()) {
                temp.append(rule.toCondSimpleLaTeX());
            } else {
              if (this.deleted.contains(rule)) {
                  temp.append(rule.toGraySimpleLaTeX());
              } else {
                  temp.append(rule.toSimpleLaTeX());
              }
          //              temp.append(rule.toLaTeX());
            }
            if (i.hasNext()) {
                temp.append("\\\\");
            }
            temp.append("\n");
        }
    if (this.isEquational()) {
        temp.deleteCharAt(temp.length()-1);
        temp.append("\\\\");
        temp.append("\n");
    }
    for (Iterator i = this.getAllEquations().iterator(); i.hasNext();) {
        TRSEquation eq = (TRSEquation)i.next();
            if (this.deletedEqns.contains(eq)) {
                temp.append(eq.toGraySimpleLaTeX());
            } else {
                temp.append(eq.toSimpleLaTeX());
            }
        //temp.append(eq.toLaTeX());
            if (i.hasNext()) {
                temp.append("\\\\");
            }
            temp.append("\n");
    }
        String res1 = newcomms.toString()+"\\begin{longtable}[l]{rcl}\n"+temp.toString()+"\\end{longtable}\n";
        /*if (this.repMap != null) {
            StringBuffer dummy = new StringBuffer(this.repMap.toLaTeX());
            dummy.append(res1);
            res1 = dummy.toString();
        }*/
        return res1;
    }

    @Override
    public String toPLAIN() {

    String indent = "   ";
    StringBuffer temp = new StringBuffer();
        Set<AlgebraVariable> vars = new LinkedHashSet<AlgebraVariable>();

        for (Iterator i = this.getAllRules().iterator(); i.hasNext();) {
            Rule rule = (Rule)i.next();
            temp.append(indent + rule.toString() + "\n");
            vars.addAll(rule.getUsedVariables());
        }

    Set<TRSEquation> eqns = this.getAllEquations();
    for (Iterator i = this.getACSymbols().iterator(); i.hasNext();) {
        eqns.removeAll(this.getAllEquations((SyntacticFunctionSymbol) i.next()));
    }
    for (Iterator i = this.getCSymbols().iterator(); i.hasNext();) {
        eqns.removeAll(this.getAllEquations((SyntacticFunctionSymbol) i.next()));
    }
        for (Iterator i = eqns.iterator(); i.hasNext();) {
            TRSEquation equation = (TRSEquation)i.next();
            temp.append(indent + equation.toString()+"\n");
            vars.addAll(equation.getUsedVariables());
        }

        StringBuffer temp2 = new StringBuffer();
        Set varnames = new LinkedHashSet();
        for (Iterator i = vars.iterator(); i.hasNext();) {
            AlgebraVariable var = (AlgebraVariable)i.next();
            String name = var.getName();
            varnames.add(name);
        }
        for (Iterator i = varnames.iterator(); i.hasNext();) {
            String name = (String)i.next();
            temp2.append(name);
            if (i.hasNext()) {
                temp2.append(", ");
            }
        }
    StringBuffer eq = new StringBuffer();
    boolean hasEq = false;
    Set<SyntacticFunctionSymbol> symbs = this.getACSymbols();
    if(!symbs.isEmpty()) {
        hasEq = true;
        eq.append(indent + "AC [");
        for (Iterator i = symbs.iterator(); i.hasNext();) {
            eq.append(((SyntacticFunctionSymbol) i.next()).getName());
            if (i.hasNext()) {
            eq.append(", ");
            }
        }
        eq.append("]\n");
    }
    symbs = this.getCSymbols();
    if(!symbs.isEmpty()) {
        hasEq = true;
        eq.append(indent + "C [");
        for (Iterator i = symbs.iterator(); i.hasNext();) {
            eq.append(((SyntacticFunctionSymbol) i.next()).getName());
            if (i.hasNext()) {
            eq.append(", ");
            }
        }
        eq.append("]\n");
    }

    if (hasEq) {
            return indent + "[" + temp2.toString() + "]\n" + eq.toString() + temp.toString();
    } else {
            return indent + "[" + temp2.toString() + "]\n" + temp.toString();
    }

    }

    public String toTTT() {
    if (!this.hasFriendlyNames) {
        return this.createWithFriendlyNames(AbstractProgram.TO_TTT).toTTT();
    }
    if (this.isEquational()) {
        return "Equational Rewriting not supported by TTT!\n";
    }
        if (this.isConditional()) {
            return "Conditional Rewriting not supported by TTT!\n";
        }
        StringBuffer temp = new StringBuffer();
        for (Iterator i = this.getAllRules().iterator(); i.hasNext();) {
            Rule rule = (Rule)i.next();
            temp.append(rule.toTTT());
            if (i.hasNext()) {
                temp.append(";");
            }
            temp.append("\n");
        }
        return temp.toString();
    }

    public String toXTRS() {
    // if (!this.hasFriendlyNames) return createWithFriendlyNames().toXTRS(); AAAAAAAAAAAARGH!!!
        Set vars = new LinkedHashSet();
    StringBuffer tmp = new StringBuffer("(RULES\n");
    Iterator it = this.getAllRules().iterator();
    while (it.hasNext()) {
        Rule rule = (Rule)it.next();
        tmp.append("  "+rule.toString()+"\n");
        Iterator v_it = rule.getUsedVariables().iterator();
        while (v_it.hasNext()) {
        vars.add(((AlgebraVariable)v_it.next()).getName());
        }
    }
    tmp.append(")\n");
        StringBuffer theo = new StringBuffer();
        EquationalTheory strange = this.getEquations();
    if (!this.getASymbols().isEmpty()) {
        StringBuffer tmp2 = new StringBuffer("(THEORY (A ");
        it = this.getASymbols().iterator();
        while (it.hasNext()) {
                SyntacticFunctionSymbol fun = (SyntacticFunctionSymbol)it.next();
                strange.removeAll(this.getEquations(fun));
        tmp2.append(fun.getName());
        if (it.hasNext()) {
            tmp2.append(" ");
        }
        }
        tmp2.append("))\n");
            theo.insert(0, tmp2);
    }
    if (!this.getCSymbols().isEmpty()) {
        StringBuffer tmp2 = new StringBuffer("(THEORY (C ");
        it = this.getCSymbols().iterator();
        while (it.hasNext()) {
                SyntacticFunctionSymbol fun = (SyntacticFunctionSymbol)it.next();
                strange.removeAll(this.getEquations(fun));
        tmp2.append(fun.getName());
        if (it.hasNext()) {
            tmp2.append(" ");
        }
        }
        tmp2.append("))\n");
            theo.insert(0, tmp2);
    }
    if (!this.getACSymbols().isEmpty()) {
        StringBuffer tmp2 = new StringBuffer("(THEORY (AC ");
        it = this.getACSymbols().iterator();
        while (it.hasNext()) {
                SyntacticFunctionSymbol fun = (SyntacticFunctionSymbol)it.next();
                strange.removeAll(this.getEquations(fun));
        tmp2.append(fun.getName());
        if (it.hasNext()) {
            tmp2.append(" ");
        }
        }
        tmp2.append("))\n");
            theo.insert(0, tmp2);
    }
        if (!strange.isEmpty()) {
            StringBuffer tmp2 = new StringBuffer("(THEORY (EQUATIONS\n");
            it = strange.iterator();
            while (it.hasNext()) {
                TRSEquation equat = (TRSEquation)it.next();
                tmp2.append("  " + equat.getOneSide().toString() + " == " + equat.getOtherSide().toString() + "\n");
            }
            tmp2.append("))\n");
            theo.append(tmp2);
        }
        tmp.insert(0, theo);

    if (!vars.isEmpty()) {
        StringBuffer tmp2 = new StringBuffer("(VAR ");
        it = vars.iterator();
        while (it.hasNext()) {
        tmp2.append(it.next());
        if (it.hasNext()) {
            tmp2.append(" ");
        }
        }
        tmp2.append(")\n");
        tmp.insert(0,tmp2);
    }
        if (this.getStrategy() == Program.INNERMOST) {
            tmp.append("(STRATEGY INNERMOST)");
        }
    return tmp.toString();
    }

    public String toCiME(BetterBoolean flag) {
    if (!this.hasFriendlyNames) {
        return this.createWithFriendlyNames(AbstractProgram.TO_CiME).toCiME(flag);
    }
    flag.setValue(true);
    Set<SyntacticFunctionSymbol> s = this.getStrangeEquationalSymbols();
    Set<SyntacticFunctionSymbol> a = this.getASymbols();
    if (!(s.isEmpty() && a.isEmpty() && this.collapse.isEmpty())) {
        flag.setValue(false);
        return "General Equational Rewriting not supported by CiME export!\n";
    }
        if (this.isConditional()) {
        flag.setValue(false);
            return "Conditional Rewriting not supported by CiME!";
        }
        StringBuffer temp = new StringBuffer();
        Set<SyntacticFunctionSymbol> funcs = new LinkedHashSet<SyntacticFunctionSymbol>();
        Set vars = new LinkedHashSet();
        for (Iterator i = this.getAllRules().iterator(); i.hasNext();) {
            Rule rule = (Rule)i.next();
            funcs.addAll(rule.getFunctionSymbols());
            for (Iterator j = rule.getUsedVariables().iterator(); j.hasNext();) {
                AlgebraVariable v = (AlgebraVariable)j.next();
                vars.add(v.getName());
            }
        }
        for (Iterator i = this.getAllEquations().iterator(); i.hasNext();) {
            TRSEquation eqn = (TRSEquation)i.next();
            funcs.addAll(eqn.getFunctionSymbols());
            for (Iterator j = eqn.getUsedVariables().iterator(); j.hasNext();) {
                AlgebraVariable v = (AlgebraVariable)j.next();
                vars.add(v.getName());
            }
        }
    Set<SyntacticFunctionSymbol> ac = this.getACSymbols();
    Set<SyntacticFunctionSymbol> c = this.getCSymbols();
        temp.append("let F = signature \"\n");
        for (Iterator i = funcs.iterator(); i.hasNext();) {
            SyntacticFunctionSymbol f = (SyntacticFunctionSymbol)i.next();
            temp.append("  "+f.getName()+" : ");
        if(ac.contains(f)) {
        if (f.getFixity() == SyntacticFunctionSymbol.NOTINFIX) {
            temp.append("prefix AC");
        }
        else {
            // infix AC
            temp.append("AC");
        }
        }
        else if(c.contains(f)) {
        if (f.getFixity() == SyntacticFunctionSymbol.NOTINFIX) {
            temp.append("prefix commutative");
        }
            else {
            // infix C
            temp.append("commutative");
        }
        }
        else {
                int arity = f.getArity();
                switch (arity) {
                    case 0:
                      temp.append("constant");
                      break;
                    case 1:
                      temp.append("unary");
                      break;
                    case 2:
              if (f.getFixity() != SyntacticFunctionSymbol.NOTINFIX) {
              temp.append("infix ");
              }
                      temp.append("binary");
                      break;
                    default:
                      temp.append(Integer.valueOf(arity).toString());
                      break;
                }
        }
            temp.append(";\n");
        }
        temp.append("\";\n");
        temp.append("let X = vars \"");
        for (Iterator i = vars.iterator(); i.hasNext();) {
            String name = (String)i.next();
            temp.append(name);
            if (i.hasNext()) {
                temp.append(" ");
            }
        }
        temp.append("\";\n");
        temp.append("let thetrs = HTRS {} F X \"\n");
        for (Iterator i = this.getAllRules().iterator(); i.hasNext();) {
            Rule rule = (Rule)i.next();
            temp.append("  "+rule.toString()+";\n");
        }
        temp.append("\";\n");
        return temp.toString();
    }

    public String toFP() {
    if (!this.hasFriendlyNames) {
        return this.createWithFriendlyNames().toFP();
    }
    StringBuffer out = new StringBuffer();
    if (this.isEquational()) {
        out.append("# WARNING: There were equational symbols!\n");
    }
        if (this.isConditional()) {
            return "Conditional Rewriting not supported by FP!";
        }
    Iterator it = this.sorts.iterator();
    while (it.hasNext()) {
        Sort s = (Sort)it.next();
        // Ignore sort bool, since it is predefined in FP.
        // TODO: Add check whether bool is what we think it is.
        if (s.getName().equals("bool")) {
        continue;
        }
        out.append("structure "+s.getName()+"\n");
        Iterator c_it = s.getConstructorSymbols().iterator();
        while (c_it.hasNext()) {
        ConstructorSymbol c = (ConstructorSymbol)c_it.next();
        out.append("  "+c.getName()+" : ");
        Iterator s_it = c.getArgSorts().iterator();
        while (s_it.hasNext()) {
            Sort cs = (Sort)s_it.next();
            out.append(cs.getName());
            if (s_it.hasNext()) {
            out.append(", ");
            }
        }
        if (!c.getArgSorts().isEmpty()) {
            out.append(" -> ");
        }
        out.append(c.getSort().getName()+"\n");
        }
        out.append("\n");
    }
    it = this.defs.iterator();
    while (it.hasNext()) {
        DefFunctionSymbol f = (DefFunctionSymbol)it.next();
        // Ignore function and, since it is predefined in FP.
        // TODO: Add check whether "and" is what we think it is.
        if (f.getName().equals("and")) {
        continue;
        }
        out.append("function "+f.getName()+" : ");
        Iterator s_it = f.getArgSorts().iterator();
        while (s_it.hasNext()) {
        Sort s = (Sort)s_it.next();
        out.append(s.getName());
        if (s_it.hasNext()) {
            out.append(", ");
        }
        }
        if (!f.getArgSorts().isEmpty()) {
        out.append(" -> ");
        }
        out.append(f.getSort().getName()+"\n");
        Iterator r_it = this.getRules(f).iterator();
        while (r_it.hasNext()) {
        Rule r = (Rule)r_it.next();
        out.append("  "+r.getLeft().toString()+" = "+r.getRight().toString()+"\n");
        }
        out.append("\n");
    }
    return out.toString();
    }

    public String toTERMPTATION(BetterBoolean flag) {
    if (!this.hasFriendlyNames) {
        return this.createWithFriendlyNames().toTERMPTATION(flag);
    }
    flag.setValue(true);
    if (this.isEquational()) {
        flag.setValue(false);
        return "Equational Rewriting not supported by TERMPTATION!\n";
    }
        if (this.isConditional()) {
        flag.setValue(false);
            return "Conditional Rewriting not supported by TERMPTATION!";
        }
        StringBuffer temp = new StringBuffer();
        FreshNameGenerator vars = new FreshNameGenerator(FreshNameGenerator.TERMPTATION_VARS);
        FreshNameGenerator funcs = new FreshNameGenerator(FreshNameGenerator.TERMPTATION_FUNCS);
        for (Iterator i = this.getAllRules().iterator(); i.hasNext();) {
            Rule rule = (Rule)i.next();
            temp.append(rule.toTERMPTATION(vars, funcs)+".\n");
        }
        return temp.toString();
    }

    public String toARTS(BetterBoolean flag) {
    if (!this.hasFriendlyNames) {
        return this.createWithFriendlyNames().toARTS(flag);
    }
    flag.setValue(true);
    if (this.isEquational()) {
        flag.setValue(false);
        return "Equational Rewriting not supported by ARTS!\n";
    }
        if (this.isConditional()) {
        flag.setValue(false);
            return "Conditional Rewriting not supported by ARTS!";
        }
        StringBuffer temp = new StringBuffer();
        FreshNameGenerator vars = new FreshNameGenerator(FreshNameGenerator.TERMPTATION_VARS);
        FreshNameGenerator funcs = new FreshNameGenerator(FreshNameGenerator.TERMPTATION_FUNCS);
        for (Iterator i = this.getAllRules().iterator(); i.hasNext();) {
            Rule rule = (Rule)i.next();
            temp.append(rule.toTERMPTATION(vars, funcs)+"\n");
        }
        return temp.toString();
    }

    public String toHASKELL() {
    if (!this.hasFriendlyNames) {
        return this.createWithFriendlyNames().toHASKELL();
    }
        StringBuffer temp = new StringBuffer();
    if (this.isEquational()) {
        temp.append("-- WARNING: There were equational symbols!\n");
    }
        if (this.isConditional()) {
            return "Conditional Rewriting not supported!";
        }
        for (Iterator i = this.sorts.iterator(); i.hasNext();) {
            Sort s = (Sort)i.next();
            temp.append("data "+s.getName()+" = ");
            for (Iterator j = s.getConstructorSymbols().iterator(); j.hasNext();) {
                ConstructorSymbol cons = (ConstructorSymbol)j.next();
                temp.append(ToHASKELLVisitor.escape(cons));
                for (Iterator k = cons.getArgSorts().iterator(); k.hasNext();) {
                    Sort argsort = (Sort)k.next();
                    temp.append(" "+argsort.getName());
                }
                if (j.hasNext()) {
                    temp.append(" | ");
                }
            }
            temp.append(" deriving Show\n");
        }
        for (Iterator i = this.defs.iterator(); i.hasNext();) {
            temp.append("\n");
            DefFunctionSymbol def = (DefFunctionSymbol)i.next();
            temp.append(ToHASKELLVisitor.escape(def)+" :: ");
            for (Iterator j = def.getArgSorts().iterator(); j.hasNext();) {
                Sort s = (Sort)j.next();
                temp.append(" "+s.getName()+" -> ");
            }
            temp.append(def.getSort().getName()+"\n");
            for (Iterator j = this.getAllRules(def).iterator(); j.hasNext();) {
                Rule rule = (Rule)j.next();
                temp.append(rule.toHASKELL()+"\n");
            }
        }
        return temp.toString();
    }

    /** Return the names of all constructors and defined functions.
     */
    public List<String> getSignature() {
    List<String> sig = new Vector<String>();
    Iterator e;
    e = this.getConstructorSymbols().iterator();
    while (e.hasNext()) {
        sig.add(((Symbol)e.next()).getName());
    }
    e = this.getDefFunctionSymbols().iterator();
    while(e.hasNext()) {
        sig.add(((Symbol) e.next()).getName());
    }
    return sig;
    }

    /** Slice a program according to a function symbol.
     */
    public Program slice(SyntacticFunctionSymbol f) {
    Program prog = Program.create();
    for (Iterator i=f.dependsOn(this).iterator(); i.hasNext();) {
        SyntacticFunctionSymbol g=(SyntacticFunctionSymbol)i.next();
        try {
        if (g instanceof ConstructorSymbol) {
            prog.addConstructorSymbol((ConstructorSymbol)g);
        }
        if (g instanceof DefFunctionSymbol) {
            prog.addDefFunctionSymbol((DefFunctionSymbol)g);
        }
        for (int j=0; j<g.getArity(); j++) {
            prog.addSort(g.getArgSort(j));
        }
        prog.addSort(g.getSort());
        } catch (ProgramException e) {
        // do nothing
        }
    }
    return prog;
    }

    /** Simple check for empty data structures.
     *  <p>
     *  Note: EXPERIMENTAL
     */
    public boolean hasEmptyStructures() {
        boolean any = false;
        Iterator i = this.sorts.iterator();
        while (i.hasNext()) {
        Sort s = (Sort)i.next();
        boolean empty = s.isEmpty();
        any = any || empty;
    }
    return any;
    }

    protected static List<AlgebraTerm> getLeftHandSides(Set<Rule> rules) {
        // important to use List her because we might have rules
        // with the same left hand side
        List<AlgebraTerm> lefts = new Vector<AlgebraTerm>();
        Iterator i = rules.iterator();
        while (i.hasNext()) {
            Rule rule = (Rule)i.next();
            lefts.add(rule.getLeft());
        }
        return lefts;
    }

    /**
     * Checks if a right-hand-side of any condition contains a
     * potentially reducible expression by unification with left-hand-sides
     * of any program rule.
     */
    public boolean isInnermostQuasiDecreasingnessCompatible() {
        Iterator i = this.getRules().iterator();
        while (i.hasNext()) {
            Rule r = (Rule)i.next();
            Iterator j = r.getConds().iterator();
            while (j.hasNext()) {
                Rule c = (Rule)j.next();
                AlgebraTerm t = c.getRight();
                Iterator k = t.getDefFunctionSubterms().iterator();
                while (k.hasNext()) {
                    DefFunctionApp tsub = (DefFunctionApp)k.next();
                    Iterator l = this.getRules(tsub.getDefFunctionSymbol()).iterator();
                    while (l.hasNext()) {
                        Rule test = (Rule)l.next();
                        FreshVarGenerator fg = new FreshVarGenerator(tsub.getVars());
                        if (tsub.isUnifiable(test.getLeft().ren(fg, true))) {
                            return false;
                        }
                    }
                }
            }
        }
        return true;
    }

    /**
     * Invalidate cached values.
     */
    public void invalidateCaches(boolean add) {
        if (add) {
            this.nonOverlapping = (YNM)this.nonOverlapping.and(MAYBE);
            this.overlaying = (YNM)this.overlaying.and(MAYBE);
            this.unarySymbols = (YNM)this.unarySymbols.and(MAYBE);
            this.maxUnarySymbols = (YNM)this.maxUnarySymbols.and(MAYBE);
            this.deterministic = (YNM)this.deterministic.and(MAYBE);
        } else {
            this.nonOverlapping = (YNM)this.nonOverlapping.or(MAYBE);
            this.overlaying = (YNM)this.overlaying.or(MAYBE);
            this.unarySymbols = (YNM)this.unarySymbols.or(MAYBE);
            this.maxUnarySymbols = (YNM)this.maxUnarySymbols.or(MAYBE);
            this.deterministic = (YNM)this.deterministic.or(MAYBE);
        }
    }

    /**
     * Check if this CTRS is deterministic.
     * @return True, iff all rules of this CTRS are deterministic.
     */
    public boolean isDeterministic() {
        if (this.deterministic == MAYBE) {
            Iterator i = this.getRules().iterator();
            this.deterministic = YES;
            while (i.hasNext()) {
                Rule r = (Rule)i.next();
                if (!r.isDeterministic()) {
                    this.deterministic = NO;
                    break;
                }
            }
        }
        return this.deterministic.toBool();
    }

    /** Check if the rules of this program are non-overlapping.
     * @return True if the rules are non-overlapping and the prog is not
     * equational.
     */
    public boolean isNonOverlapping() {
        if (this.nonOverlapping == MAYBE) {
            this.nonOverlapping = YNM.fromBool(this.isNonOverlapping(null));
        }
        return this.nonOverlapping.toBool();
    }

    /** Check if the rules for the given defined function symbol
     * are non-overlapping. Passing a null value will check
     * the rules for all defined function symbols of this program.
     * <p>
     * This check is implemented by comparing all left
     * hand sides of all rules to all subterms of
     * all left hand sides besides the trivial
     * subterm of themselves.
     * @param def The defined function symbol for which to check
     * non-overlappingness of rules.
     * @return True if the rules are non-overlapping.
     */
    public boolean isNonOverlapping(DefFunctionSymbol def) {
        List<AlgebraTerm> lefts = Program.getLeftHandSides(this.getRules());
        List<AlgebraTerm> subLefts = new Vector<AlgebraTerm>();
        Iterator i = lefts.iterator();
        while (i.hasNext()) { // collect all subterms of left hand sides
            AlgebraTerm left = (AlgebraTerm)i.next();
            subLefts.addAll(left.getAllSubterms());
        }
        if (def == null) {
            i = lefts.iterator();
        } else {
            i = Program.getLeftHandSides(this.getRules(def)).iterator();
        }
        while (i.hasNext()) { // check for non-overlappingness
            AlgebraTerm left = (AlgebraTerm)i.next();
            FreshVarGenerator fv = new FreshVarGenerator(left);
            Iterator j = subLefts.iterator();
            while (j.hasNext()) {
                AlgebraTerm subLeft = (AlgebraTerm)j.next();
                // The identity check on left and subLeft depends
                // on getAllSubterms not returning copies.
                if ((!subLeft.isVariable()) && (left != subLeft)) {
                    if (subLeft.ren(fv, true).isUnifiable(left)) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    /** Check if the rules of this program are overlaying.
     * @return True iff the rules are overlaying.
     */
    public boolean isOverlaying() {
        if (this.overlaying == MAYBE) {
            this.overlaying = YNM.fromBool(this.isOverlaying(null));
        }
        return this.overlaying.toBool();
    }

    /** Check if the rules for the given defined function symbol
     * are overlaying. Passing a null value will check
     * the rules for all defined function symbols of this program.
     * <p>
     * This check is implemented by comparing all left
     * hand sides of all rules to all proper subterms of
     * all left hand sides.
     * @param def The defined function symbol for which to check
     * overlaying of rules.
     * @return True iff the rules are overlaying.
     */
    public boolean isOverlaying(DefFunctionSymbol def) {
        List<AlgebraTerm> lefts = Program.getLeftHandSides(this.getRules());
        List<AlgebraTerm> subLefts = new Vector<AlgebraTerm>();
        Iterator i = lefts.iterator();
        while (i.hasNext()) { // collect all subterms of left hand sides
            AlgebraTerm left = (AlgebraTerm)i.next();
            subLefts.addAll(left.getAllProperSubterms());
        }
        if (def == null) {
            i = lefts.iterator();
        } else {
            i = Program.getLeftHandSides(this.getRules(def)).iterator();
        }
        while (i.hasNext()) { // check for overlays
            AlgebraTerm left = (AlgebraTerm)i.next();
            FreshVarGenerator fv = new FreshVarGenerator(left);
            Iterator j = subLefts.iterator();
            while (j.hasNext()) {
                AlgebraTerm subLeft = (AlgebraTerm)j.next();
                if (!subLeft.isVariable()) {
                    if (subLeft.ren(fv, true).isUnifiable(left)) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    /** Check if the rules of this program are left-linear.
     * @return True iff all the rules are left-linear.
     */
    public boolean isLeftLinear() {
        return this.isLeftLinear(null);
    }

    /** Check if the rules for the given defined function symbol
     * are left-linear. Passing a null value will check
     * the rules for all defined function symbols of this program.
     * @return True if the rules are left-linear.
     */
    public boolean isLeftLinear(DefFunctionSymbol def) {
        Iterator i;
        if (def == null) {
            i = Program.getLeftHandSides(this.getRules()).iterator();
        } else {
            i = Program.getLeftHandSides(this.getRules(def)).iterator();
        }
        while (i.hasNext()) {
            if (!CheckLinearVisitor.apply((AlgebraTerm)i.next())) {
                return false;
            }
        }
        return true;
    }

    protected static AlgebraTerm getInstance(ConstructorSymbol cons) {
        List<AlgebraTerm> args = new Vector<AlgebraTerm>();
        Iterator i = cons.getArgSorts().iterator();
        while (i.hasNext()) {
            Sort sort = (Sort)i.next();
            args.add(AlgebraVariable.create(VariableSymbol.create("x1", sort)));
        }
        return ConstructorApp.create(cons, args);
    }

    protected static List<AlgebraTerm> getAllInstances(DefFunctionSymbol def, List<AlgebraTerm> args, List<Sort> argsorts) {
        List<AlgebraTerm> instances = new Vector<AlgebraTerm>();
        if (argsorts.isEmpty()) {
            instances.add(DefFunctionApp.create(def, args).ren(new FreshVarGenerator(), false));
        } else {
            List<Sort> newargsorts = new Vector<Sort>(argsorts);
            Sort argsort = newargsorts.remove(0);
            Iterator i = argsort.getConstructorSymbols().iterator();
            while (i.hasNext()) {
                ConstructorSymbol cons = (ConstructorSymbol)i.next();
                List<AlgebraTerm> newargs = new Vector<AlgebraTerm>(args);
                newargs.add(Program.getInstance(cons));
                instances.addAll(Program.getAllInstances(def, newargs, newargsorts));
            }
        }
        return instances;
    }

    /* Test function
    public List<Term> getAllInstances(DefFunctionSymbol def) {
        return getAllInstances(def, new Vector<Term>(), def.getArgSorts());
    }*/

    /** Check if the rules of this program are completely defined.
     * @return True if the rules are completely defined, false if complete definition cannot be shown.
     */
    public boolean isCompletelyDefined() {
        Iterator i = this.defs.iterator();
        while (i.hasNext()) {
            DefFunctionSymbol def = (DefFunctionSymbol)i.next();
            if (!this.isCompletelyDefined(def, this.getRules(def))) {
                return false;
            }
        }
        return true;
    }

    /** Check if the rules for the given defined function symbol
     * are completely defined.
     * @param def The defined function symbol to test.
     * @param rules The rules that define the function.
     * @return True if the rules are completely defined, false if complete definition cannot be shown.
     */
    public boolean isCompletelyDefined(DefFunctionSymbol def, Set<Rule> rules) {
    return Program.checkApplicabilityByRules(def,rules, this.typeContext).isEmpty();
    }

    /** Checks the applicability for the given defined function symbol
     *  which is defined by the given set of rules.
     *  @param def The defined function symbol to test.
     *  @param rules The rules that define the function.
     *  @param typeContext The Type Context defining types for def and all function-symbols in rules
     *  @return A set of terms (potential left hand sides) that still need
     *  to get a defining equation.
     */
    public static Set<AlgebraTerm> checkApplicabilityByRules(DefFunctionSymbol def, Set<Rule> rules, TypeContext typeContext) {
    Set<AlgebraTerm> defpatterns = new HashSet<AlgebraTerm>();
    Iterator it = rules.iterator();
    while (it.hasNext()) {
        Rule r = (Rule)it.next();
        // Ignore Rules with conditions.
        if (r.getConds().isEmpty()) {
        defpatterns.add(r.getLeft());
        }
    }
    return Program.checkApplicabilityByTerms(def, defpatterns, typeContext);
    }

    public static Set<AlgebraTerm> checkApplicabilityByTerms(DefFunctionSymbol def, Set<AlgebraTerm> defpatterns, TypeContext typeContext) {
    Set<AlgebraVariable> vars = new HashSet<AlgebraVariable>();
    Iterator it = defpatterns.iterator();
    while (it.hasNext()) {
        Set<AlgebraVariable> newvars = ((AlgebraTerm)it.next()).getVars();
        vars.addAll(newvars);
    }
    Vector<String> usednames = new Vector<String>();
    it = vars.iterator();
    while (it.hasNext()) {
        usednames.add(((AlgebraVariable)it.next()).getSymbol().getName());
    }
    FreshNameGenerator namegen = new FreshNameGenerator(usednames, FreshNameGenerator.VARIABLES);
    List<AlgebraTerm> args = new Vector<AlgebraTerm>();
    for (int i=0; i<def.getArity(); i++) {
        String name = namegen.getFreshName("x", false);
        args.add(AlgebraVariable.create(VariableSymbol.create(name, def.getArgSort(i))));
    }
    Vector patterns_todo = new Vector();
    patterns_todo.add(args);
    it = defpatterns.iterator();
    while (it.hasNext()) {
        AlgebraTerm t = (AlgebraTerm)it.next();
        Program.considerPatternInToDoPatterns(patterns_todo, t.getArguments(), namegen, typeContext);
    }
    Set<AlgebraTerm> terms_todo = new HashSet<AlgebraTerm>();
    it = patterns_todo.iterator();
    while (it.hasNext()) {
        terms_todo.add(AlgebraFunctionApplication.create(def,(List<AlgebraTerm>)it.next()));
    }
    return terms_todo;
    }

    /** Updates a list of todo-patterns with respect to a new pattern,
     *  that "is done".
     *  @param patterns The list of todo-patterns.
     *  @param np The pattern that is to be considered "done".
     */
    public static void considerPatternInToDoPatterns(Vector patterns, List<AlgebraTerm> np, FreshNameGenerator namegen, TypeContext typeContext) {
    // First check whether the pattern contains a variable twice.
    /*
    Set vars = new HashSet();
    Iterator it = nt.getPositions().iterator();
    while (it.hasNext()) {
        Term tp = nt.getSubterm((Position)it.next());
        if (tp.isVariable()) {
        if (!vars.add(tp.getSymbol().getName())) {
            return;
        }
        }
    }
    */
    int pi = 0;
    while (pi < patterns.size()) {
        List<AlgebraTerm> pattern = (List<AlgebraTerm>)patterns.get(pi);
        Iterator p1_it = pattern.iterator();
        Iterator p2_it = np.iterator();
        boolean matches = true;
        boolean unifies = true;
        int firstunify = -1;
        // Compare every element of the patterns.
        for (int i=0; p1_it.hasNext(); i++) {
        AlgebraTerm t1 = (AlgebraTerm)p1_it.next();
        AlgebraTerm t2 = (AlgebraTerm)p2_it.next();
        if (!t2.isMatchable(t1)) {
            matches = false;
            if (firstunify == -1) {
            firstunify = i;
            }
            if (!t1.isUnifiable(t2)) {
            unifies = false;
            }
        }
        }
        // If the current pattern of the todo-list is matched by the new
        // pattern, the current pattern can be removed from the todo-list
        if (matches) {
        patterns.removeElementAt(pi);
        continue;
        }
        // If the current pattern of the todo-list unifies the new
        // pattern, the current pattern can be replaced
        if (unifies) {
        List<AlgebraTerm> rs = (List<AlgebraTerm>)patterns.remove(pi);
        AlgebraTerm r = rs.get(firstunify);
        AlgebraTerm t = np.get(firstunify);

        Pair<AlgebraVariable,AlgebraTerm> varAndType = Program.getLeftmostDiffVariableWithType(r,t, typeContext);
        AlgebraVariable v = varAndType.x;
        AlgebraTerm vType = varAndType.y;

        Set<Symbol> constrsyms = typeContext.getTypeDef(vType.getSymbol().getName()).getDeclaredSymbols();

        // For every constructor-symbol of the sort in question create a new pattern.
        Iterator c_it = constrsyms.iterator();
        while (c_it.hasNext()) {
            List<AlgebraTerm> newpattern = new Vector<AlgebraTerm>(pattern);
            ConstructorSymbol cs = (ConstructorSymbol)c_it.next();
            List<AlgebraTerm> args = new Vector<AlgebraTerm>();
            for (int j=0; j<cs.getArity(); j++) {
            String name = namegen.getFreshName("x",false);
            args.add(AlgebraVariable.create(VariableSymbol.create(name, cs.getArgSort(j))));
            }
            AlgebraSubstitution sigma = AlgebraSubstitution.create();
            sigma.put((VariableSymbol)v.getSymbol(), ConstructorApp.create(cs,args));
            newpattern.set(firstunify, (newpattern.get(firstunify)).apply(sigma));
            patterns.add(newpattern);
        }
        continue;
        }
        pi++;
    }
    }

    private static Pair<AlgebraVariable,AlgebraTerm> getLeftmostDiffVariableWithType(AlgebraTerm r, AlgebraTerm t, TypeContext typeContext) {
    if (r.isVariable()) {
        if (t.isVariable()) {
        return null;
        }
        Type resultType = typeContext.getSingleTypeOf(t.getSymbol());
        AlgebraTerm resultTypeTerm = null;
        if (resultType != null) {
            resultTypeTerm = TypeTools.getResultTerm(resultType.getTypeMatrix());
        }
        return new Pair<AlgebraVariable,AlgebraTerm>( (AlgebraVariable)r , resultTypeTerm );
    }
    if (!r.getSymbol().equals(t.getSymbol())) {
        return null;
    }
    Iterator ra_it = r.getArguments().iterator();
    Iterator ta_it = t.getArguments().iterator();
    while (ra_it.hasNext()) {
        AlgebraTerm ra = (AlgebraTerm)ra_it.next();
        AlgebraTerm ta = (AlgebraTerm)ta_it.next();
        Pair<AlgebraVariable,AlgebraTerm> varAndType = Program.getLeftmostDiffVariableWithType(ra,ta, typeContext);
        if (varAndType != null) {
        return varAndType;
        }
    }
    return null;
    }

    /**
     * Returns a subset of the given rules that completely defines the given
     * defined function symbol if def is completely defined.
     * @param def The defined function symbol to get the rules for.
     * @param rules The set of rules that are to be considered.
     * @return Set of complete rules if possible, unchanged rules otherwise.
     */
    public Set<Rule> getCompleteRules(DefFunctionSymbol def, Set<Rule> rules) {
        boolean success = true;
        while (success) {
            success = false;
            Set<Rule> defrules = null;
            Iterator i = rules.iterator();
            while (i.hasNext()) {
                defrules = new LinkedHashSet<Rule>(rules);
                defrules.remove(i.next());
                if (this.isCompletelyDefined(def, defrules)) {
                    success = true;
                    break;
                }
            }
            if (success) {
                rules = defrules;
            }
        }
        return rules;
    }

    /* consistency check */
    @Override
    public void check() {
    this.check(new HashSet());
    }

    @Override
    public void check(Set checked) {
    if (!checked.contains(this)) {
        checked.add(this);
        if (this.sig ==  null) {
        throw new RuntimeException("sig must not be null");
        }
        if (this.cons == null) {
        throw new RuntimeException("cons must not be null");
        }
        if (this.defs == null) {
        throw new RuntimeException("defs must not be null");
        }
        if (this.sorts == null) {
        throw new RuntimeException("sorts must not be null");
        }
        for (Iterator i=this.sig.keySet().iterator(); i.hasNext();) {
        Object o = this.sig.get(i.next());
        if (o instanceof Symbol) {
            if ((!this.cons.contains(o)) && (!this.defs.contains(o))) {
            throw new RuntimeException("invalid function symbol "+((Symbol)o).getName()+" in sig");
            }
            ((Symbol)o).check(checked);
        } else if (o instanceof Sort) {
            if (!this.sorts.contains(o)) {
            throw new RuntimeException("invalid sort "+((Sort)o).getName()+" in sig");
            }
            ((Sort)o).check(checked);
        } else {
            throw new RuntimeException("function or sort symbol expected");
        }
        }
        for (Iterator i=this.cons.iterator(); i.hasNext();) {
        ((ConstructorSymbol)i.next()).check(checked);
        }
        for (Iterator i=this.defs.iterator(); i.hasNext();) {
        ((DefFunctionSymbol)i.next()).check(checked);
        }
        for (Iterator i=this.sorts.iterator(); i.hasNext();) {
        ((Sort)i.next()).check(checked);
        }
    }
    }

    /** Returns all rules that belong to the given defined function symbol.
     */
    public Set<Rule> getAllRules(SyntacticFunctionSymbol def) {
        String defname = def.getName();
        Set<Rule> rules = this.defsrules.get(defname);
        if (rules == null) {
            rules = new LinkedHashSet<Rule>();
            this.defsrules.put(defname, rules);
        // Added by chang: Shouldn't we update this.defs here?
        if (def instanceof DefFunctionSymbol) {
        this.defs.add((DefFunctionSymbol) def);
        }
        }
        return rules;
    }

    /** Returns all rules that belong to the given defined function symbol.
     */
    public Set<Rule> getRules( SyntacticFunctionSymbol def) {
        Set<Rule> rules = new LinkedHashSet<Rule>(this.getAllRules(def));
        rules.removeAll(this.deleted);
        return rules;
    }

    /** Remove a set of rules from this program.
     */
    public void removeRules(Set<Rule> rules) {
        Iterator i = rules.iterator();
        while (i.hasNext()) {
            this.removeRule((Rule)i.next());
        }
    }

    /** Remove a rule from this program.
     */
    public void removeRule(Rule rule) {
        this.removeRule(rule.getRootSymbol(), rule);
        this.invalidateCaches(false);
    }

    /** Really remove rule from program.
     *  Method provided, because Symbolic Evaluator doesn't care shit about the this.deleted set.
     */
    public void reallyRemoveRule(Rule rule) {
        String defname = rule.getRootSymbol().getName();
        Set<Rule> rules = this.defsrules.get(defname);
        rules.remove(rule);
    }

    /** Remove a rule from a given defined function symbol.
     */
    public void removeRule(SyntacticFunctionSymbol def, Rule rule) {
//        String defname = def.getName();
//        Set<Rule> rules = (Set<Rule>)this.defsrules.get(defname);
//        rules.remove(rule);
        this.deleted.add(rule);
    }

    /** Add a rule to this program.
     */
    public void addRule(Rule rule) {
        this.addRule(rule.getRootSymbol(), rule);
    }

    public void addRules(Collection<Rule> rules) {
    Iterator i = rules.iterator();
    while(i.hasNext()) {
        this.addRule((Rule)i.next());
    }
    }

    /** Add a rule to a certain defined function symbol.
     */
    public void addRule(SyntacticFunctionSymbol def, Rule rule) {
        Set<Rule> rules = this.getAllRules(def);
        rules.add(rule);
        this.invalidateCaches(true);
    }

    /** Return all function symbols.
     */
    public Set<SyntacticFunctionSymbol> getFunctionSymbols() {
    LinkedHashSet<SyntacticFunctionSymbol> ret = new LinkedHashSet<SyntacticFunctionSymbol>();
    Iterator e;
    e = this.getConstructorSymbols().iterator();
    while (e.hasNext()) {
        ret.add((SyntacticFunctionSymbol)e.next());
    }
    e = this.getDefFunctionSymbols().iterator();
    while (e.hasNext()) {
        ret.add((SyntacticFunctionSymbol) e.next());
    }

    if( this.waveHole != null ) {
        ret.add(this.waveHole);
    }

    if( this.waveFrontIn != null) {
        ret.add(this.waveFrontIn);
    }

    if( this.waveFrontOut != null) {
        ret.add(this.waveFrontOut);
    }

    return ret;
    }

    /**
     * @return the set of all equations, where the rules are expressed
     *  using DPFramework equations
     */
    public Set<aprove.verification.dpframework.BasicStructures.Equation> getNewEquations() {
        Set<aprove.verification.dpframework.BasicStructures.Equation> newRules = new LinkedHashSet<aprove.verification.dpframework.BasicStructures.Equation>();
        for (TRSEquation equation : this.getEquations()) {
            newRules.add(aprove.verification.dpframework.BasicStructures.Equation.create(equation.getOneSide().toNewTerm(), equation.getOtherSide().toNewTerm()));
        }
        return newRules;
    }

    /**
     * @return the set of all rules, where the rules are expressed
     *  using DPFramework terms
     */
    public Set<aprove.verification.dpframework.BasicStructures.Rule> getNewRules() {
        Set<aprove.verification.dpframework.BasicStructures.Rule> newRules = new LinkedHashSet<aprove.verification.dpframework.BasicStructures.Rule>();
        for (Rule rule : this.getRules()) {
            newRules.add(aprove.verification.dpframework.BasicStructures.Rule.create((aprove.verification.dpframework.BasicStructures.TRSFunctionApplication)rule.getLeft().toNewTerm(), rule.getRight().toNewTerm()));
        }
        return newRules;
    }

    /** Return a set of all rules.
     */
    public Set<Rule> getRules() {
        return this.getRules(this.defs);
    }

    /** Return a set of all rules.
     */
    public Set<Rule> getAllRules() {
        return this.getAllRules(this.defs);
    }

    public Set<Rule> getAllRules(Set<DefFunctionSymbol> defs) {
        Set<Rule> rules = new LinkedHashSet<Rule>();
        Iterator i = defs.iterator();
        while (i.hasNext()) {
            DefFunctionSymbol def = (DefFunctionSymbol)i.next();
            rules.addAll(this.getAllRules(def));
        }
        return rules;
    }

    /** Returns a map that maps a function symbol to its rules.
     */
    public Map<String,Set<Rule>> getRuleMapping() {
    return this.defsrules;
    }

    /** Returns all rules that belong to the given function symbols.
     */
    public Set<Rule> getRules(Set<? extends SyntacticFunctionSymbol> defs) {
        Set<Rule> rules = new LinkedHashSet<Rule>();
        Iterator i = defs.iterator();
        while (i.hasNext()) {
            SyntacticFunctionSymbol def = (SyntacticFunctionSymbol) i.next();
            rules.addAll(this.getRules(def));
        }
        return rules;
    }

    @Override
    public boolean equals(Object o) {

    if (!(o instanceof Program)) {
        return false;
    }
        Program p = (Program)o;

    boolean bSorts = new HashSet(this.sorts).equals(new HashSet(p.sorts));
    boolean bCons = new HashSet(this.cons).equals(new HashSet(p.cons));
    boolean bDefs = new HashSet(this.defs).equals(new HashSet(p.defs));
    boolean bDeleted = this.deleted.equals(p.deleted);
    boolean bDefsRules = this.getRules().equals(p.getRules());
    boolean bDefsEqs = this.getEquations().equals(p.getEquations());
    boolean bcol = this.collapse.equals(p.collapse);
    //System.out.println(this.defsequations + " and " + p.defsequations);
    //System.out.println("sorts: " + bSorts + " cons: " +  bCons + " defs: " + bDefs + "deleted: " + bDeleted + " defrules: " + bDefsRules + " defeq: " + bDefsEqs + " col: " + bcol);
    return (bSorts && bCons && bDefs && bDeleted && bDefsRules && bDefsEqs && bcol);


    }

    @Override
    public int hashCode() {
    return this.toString().hashCode();
    }

    /* Forbidden for security's and sanity's sake */
    @Override
    protected Object clone() {
    throw new RuntimeException("clone deprecated -- use deepcopy / shallowcopy instead");
    }

    /** Returns a shallow copy of this object, i.e. a program that uses the
     *  same sorts, type context, constructors and defined functions.
     *  <p>
     *  Note: Changing the sorts, type context, constructors or defined functions
     *  of the copied program will
     *  result in changes to the original program!
     */
    public Program shallowcopy() {
    Program res = new Program(new LinkedHashMap(this.sig),
                           new LinkedHashMap(this.presig),
               new LinkedHashSet<Sort>(this.sorts),
               new LinkedHashSet<ConstructorSymbol>(this.cons),
               new LinkedHashSet<DefFunctionSymbol>(this.defs),
               new LinkedHashSet<DefFunctionSymbol>(this.predefs),
                           new LinkedHashMap(this.defsrules),
               new LinkedHashMap(this.defsequations),
               new LinkedHashMap(this.consequations),
               new HashSet<TRSEquation>(this.collapse),
               this.predefined);
    res.deleted = new LinkedHashSet<Rule>(this.deleted);
    res.deletedEqns = new LinkedHashSet<TRSEquation>(this.deletedEqns);
    res.setOrigin(this.origin);
    res.setType(this.type);
    if(this.equationalExt!=null) {
        res.equationalExt = this.equationalExt.shallowcopy();
        }
    res.setSimplifiable(this.isSimplifiable);
    res.setFromProlog(this.isFromProlog());
        res.setStrategy(this.getStrategy());
        res.setComplete(this.isComplete());
        res.setStrategyNeeded(this.getStrategyNeeded());
    res.setTypeContext(this.getTypeContext());
    return res;
    }

    public Program deepercopy() {
    LinkedHashMap sig = new LinkedHashMap(this.sig);
    LinkedHashMap presig = new LinkedHashMap(this.presig);
        LinkedHashSet<Sort> sorts = new LinkedHashSet<Sort>(this.sorts);
        LinkedHashSet<ConstructorSymbol> cons = new LinkedHashSet<ConstructorSymbol>(this.cons);
        LinkedHashSet<DefFunctionSymbol> defs = new LinkedHashSet<DefFunctionSymbol>(this.defs);
    LinkedHashSet<DefFunctionSymbol> predefs = new LinkedHashSet<DefFunctionSymbol>(this.predefs);
        LinkedHashMap defsrules = new LinkedHashMap();
    LinkedHashMap defsequations = new LinkedHashMap();
    LinkedHashMap consequations = new LinkedHashMap();
    HashSet<TRSEquation> collapse = new HashSet<TRSEquation>(this.collapse);
    Program res = new Program(sig, presig, sorts, cons, defs, predefs, defsrules, defsequations, consequations, collapse, this.predefined);
    Iterator i = this.cons.iterator();
    while(i.hasNext()) {
        res.addEquations(this.getAllEquations((SyntacticFunctionSymbol)i.next()));
    }
    i = this.defs.iterator();
    while(i.hasNext()) {
        SyntacticFunctionSymbol symb = (SyntacticFunctionSymbol)i.next();
        res.addEquations(this.getAllEquations(symb));
        res.addRules(this.getAllRules(symb));
    }
    res.deleted = new LinkedHashSet<Rule>(this.deleted);
    res.deletedEqns = new LinkedHashSet<TRSEquation>(this.deletedEqns);
    res.setOrigin(this.origin);
    res.setType(this.type);
    if(this.equationalExt!=null) {
        res.equationalExt = this.equationalExt.deepercopy();
    }
    res.setSimplifiable(this.isSimplifiable);
    res.setFromProlog(this.isFromProlog());
        res.setStrategy(this.getStrategy());
        res.setComplete(this.isComplete());
        res.setStrategyNeeded(this.getStrategyNeeded());
    if (this.getTypeContext() != null) {
        res.setTypeContext(this.getTypeContext().deepcopy());
    } else {
        res.setTypeContext(null);
    }

    res.waveHole     = this.waveHole     == null ? null : WaveHole.create(this.waveHole.getName(),1);
    res.waveFrontIn  = this.waveFrontIn  == null ? null : WaveFrontIn.create(this.waveFrontIn.getName(),1);
    res.waveFrontOut = this.waveFrontOut == null ? null : WaveFrontOut.create(this.waveFrontOut.getName(),1);

    res.laProgramProperties = this.laProgramProperties;

    return res;
    }


    /**
     * Try to infer as much about the sorts of this program.
     * <P>
     * Note: This is a destructive operation.
     */
    public Set<Sort> inferType() throws InterruptedException {
    Set<Sort> res = this.inferType(this.getRules(), this.getEquations());
    return res;
    }

    /**
     * Try to infer as much about the sorts of the given rules.
     * <P>
     * Note: This is a destructive operation.
     */
    public Set<Sort> inferType(Set<Rule> rules, Set<TRSEquation> equations) throws InterruptedException {
        SortMap sorted = new SortMap();
        Iterator i = rules.iterator();
        while (i.hasNext()) {
            Rule rule = (Rule)i.next();
            sorted.add(rule.getFunctionSymbols());
            sorted.update(rule.getLeft(), rule.getRight(), rule);
            rule.getLeft().inferType(sorted, rule);
            rule.getRight().inferType(sorted, rule);
        }
    i = equations.iterator();
        while (i.hasNext()) {
            TRSEquation rule = (TRSEquation)i.next();
            sorted.add(rule.getFunctionSymbols());
            sorted.update(rule.getOneSide(), rule.getOtherSide(), rule);
            rule.getOneSide().inferType(sorted, rule);
            rule.getOtherSide().inferType(sorted, rule);
        }
        Set<Sort> result = sorted.computeSorts();
        this.sorts = new LinkedHashSet<Sort>();
        i = result.iterator();
        while (i.hasNext()) {
            Sort s = (Sort)i.next();
            try {
                this.addSort(s);
            } catch (ProgramException e) {
                // should not happen
                throw new RuntimeException("internal error in type inference");
            }
        }
        return result;
    }

    public class SortMap extends LinkedHashMap {

        Map name2funcs;

        public SortMap() {
            super();
            this.name2funcs = new HashMap();
        }

        public void add(Collection<SyntacticFunctionSymbol> funcs) {
            Iterator i = funcs.iterator();
            while (i.hasNext()) {
                SyntacticFunctionSymbol func = (SyntacticFunctionSymbol)i.next();
                String fname = func.getName();
                this.name2funcs.put(fname, func);
                if (this.containsKey(fname)) {
                    continue;
                }
                int arity = func.getArity();
                LinkedHashSet[] entries = new LinkedHashSet[arity+1];
                for (int j = 0; j < arity+1; j++) {
                    entries[j] = new LinkedHashSet();
                }
                entries[arity].add(new Entry(func));
                this.put(fname, entries);
            }
        }

        public void update(AlgebraTerm fterm, AlgebraTerm term, Object rule) {
            this.update(fterm, -1, term, rule);
        }

        public void update(AlgebraTerm fterm, int index, AlgebraTerm term, Object rule) {
            if (index == -1) {
                if (fterm instanceof AlgebraVariable) {
                    if (term instanceof AlgebraVariable) {
                        return; // Don't care about type
                    } else {
                        this.update(term, index, fterm, rule); // swap
                    }
                }
            }
            SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol)fterm.getSymbol();
            LinkedHashSet[] entries = (LinkedHashSet[])this.get(fsym.getName());
            if (index == -1) {
                index = entries.length-1;
            }
            if (term instanceof AlgebraVariable) {
                VariableSymbol v = (VariableSymbol)term.getSymbol();
                entries[index].add(new Entry(v, rule));
            } else {
                SyntacticFunctionSymbol f = (SyntacticFunctionSymbol)term.getSymbol();
                entries[index].add(new Entry(f));
            }
        }

        public Set computeClosure() throws InterruptedException {

            Set results = new LinkedHashSet();
            Graph closure = new Graph();
            // define sets as nodes of a graph
            for(Object o: this.entrySet()) {
                Map.Entry e = (Map.Entry) o;
                String fname = (String) e.getKey();
                LinkedHashSet[] entries = (LinkedHashSet[]) e.getValue();
                for (int j = 0; j < entries.length; j++) {
                    LinkedHashSet entrys = entries[j];
                    closure.addNode(new Node(entrys));
                }
            }
            // add an edge from nodes which have a non-empty intersection
            Iterator i = closure.getNodes().iterator();
            while (i.hasNext()) {
                Node these_node = (Node)i.next();
                Set these = (Set)these_node.getObject();
                Iterator j = closure.getNodes().iterator();
                while (j.hasNext()) {
                    Node those_node = (Node)j.next();
                    Set those = (Set)those_node.getObject();
                    if (this.nonEmptyIntersection(these, those)) {
                        closure.addEdge(these_node, those_node);
                        closure.addEdge(those_node, these_node);
                    }
                }
            }
            // calculate sccs
            Set<Cycle> sccs = closure.getSCCs();
            i = sccs.iterator();
            while (i.hasNext()) {
                Cycle scc = (Cycle)i.next();
                Set new_set = new LinkedHashSet();
                Iterator j = scc.getNodeObjects().iterator();
                while (j.hasNext()) {
                    Set set = (Set)j.next();
                    new_set.addAll(set);
                }
                results.add(new_set);
            }
            return results;
        }

        private boolean nonEmptyIntersection(Set these, Set those) {

        Iterator k = these.iterator();
        while (k.hasNext()) {
        if (those.contains(k.next())) {
            return true;
        }
        }
        return false;

        }

        public Set<Sort> computeSorts() throws InterruptedException {

            FreshNameGenerator fg = new FreshNameGenerator(FreshNameGenerator.TYPE_INFERENCE);
            Set<Sort> results = new LinkedHashSet<Sort>();
            Set closure = this.computeClosure();
            Iterator i = closure.iterator();
            while (i.hasNext()) {
                Set set = (Set)i.next();
                Sort result = Sort.create(fg.getFreshName("S", false));
                Iterator j = set.iterator();
                while (j.hasNext()) {
                    Entry entry = (Entry)j.next();
                    Symbol sym = entry.getSymbol();
                    if (sym instanceof ConstructorSymbol) {
                        result.addConstructorSymbol((ConstructorSymbol)sym);
                    }
                    sym.setSort(result);
                }
        // BUG?!
                //if (result.getConstructorSymbols().size() > 0) {
                    results.add(result);
                //}
            }
            for(Object o: this.entrySet()) {
                Map.Entry e = (Map.Entry) o;
                String fname = (String) e.getKey();
                SyntacticFunctionSymbol f = (SyntacticFunctionSymbol)this.name2funcs.get(fname);
                LinkedHashSet[] entries = (LinkedHashSet[]) e.getValue();
                for (int j = 0; j < entries.length-1; j++) {
                    LinkedHashSet entrys = entries[j];
                    Entry entry = (Entry)entrys.iterator().next();
                    Symbol sym = entry.getSymbol();
                    f.setArgSort(j, sym.getSort());
                }
            }
            return results;

        }

        @Override
        public String toString() {

            StringBuffer result = new StringBuffer();
            for(Object o: this.entrySet()) {
                Map.Entry e = (Map.Entry) o;
                String fname = (String) e.getKey();
                result.append(fname+": ");
                LinkedHashSet[] entries = (LinkedHashSet[]) e.getValue();
                for (int j = 0; j < entries.length-1; j++) {
                    result.append(entries[j]);
                    if (j == entries.length-2) {
                        result.append(" -> ");
                    } else {
                        result.append(", ");
                    }
                }
                result.append(entries[entries.length-1]);
                result.append("\n");
            }
            return result.toString();

        }

        public class Entry {

            Object origin;
            Symbol symbol;

            public Entry(SyntacticFunctionSymbol f) {
                this.origin = null;
                this.symbol = f;
            }

            public Entry(VariableSymbol v, Object rule) {
                this.origin = rule;
                this.symbol = v;
            }

            public Symbol getSymbol() {
                return this.symbol;
            }

            @Override
            public int hashCode() {
                return this.symbol.getName().hashCode();
            }

            @Override
            public boolean equals(Object o) {
                Entry entry = (Entry)o;
        boolean res;
                if (this.origin == null) {
                    res = (entry.origin == null) && this.symbol.getName().equals(entry.symbol.getName());
                }
        else {
            if(this.origin instanceof Rule) {
            if(!(entry.origin instanceof Rule)) {
                res = false;
            }
            else {
                            res = this.origin.equals(entry.origin) && this.symbol.getName().equals(entry.symbol.getName());
            }
            }
            else { /* TRSEquation */
            if(!(entry.origin instanceof TRSEquation)) {
                res = false;
            }
            else {
                            res = this.origin.equals(entry.origin) && this.symbol.getName().equals(entry.symbol.getName());
            }
            }
        }
        return res;
            }

            @Override
            public String toString() {
                return this.symbol.getName();
            }

        }
    }

    /**
     * Tranform this program into an unconditional term rewriting
     * system.
     * @return A new unconditional program.
     */
    public Program transformConditional() {
        return ConditionalTransformer.create().transform(this);
    }

    /**
     * Transform this program into a reduced program. I.e. rules that
     * are marked deleted will be removed and functions that do not
     * have rules anymore will be constructors.
     */
    public Program transformToReduced() {
    return ReduceTransformer.create().transform(this);
    }

    public boolean isConditional() {
        Iterator i = this.getRules().iterator();
        while (i.hasNext()) {
            Rule rule = (Rule)i.next();
            if (!rule.getConds().isEmpty()) {
                return true;
            }
        }
        return false;
    }

    public void rremoveGZ(boolean dummy) {
        return;
    }


    public boolean isDuplicating() {
    Iterator i = this.getRules().iterator();
    while (i.hasNext()) {
        Rule rule = (Rule) i.next();
        Iterator j = rule.getRight().getVars().iterator();
            while (j.hasNext()) {
                AlgebraVariable x = (AlgebraVariable) j.next();
                VariableSymbol v = x.getVariableSymbol();
//                System.err.println("Checking "+v);
//                System.err.println("left = "+rule.getLeft().count(v)+", right ="+rule.getRight().count(v));
                if (rule.getLeft().count(v) < rule.getRight().count(v)) {
                    return true;
                }
            }
        }
        return false;
    }

    public void removeLHSRedexes() {
        Set<Rule> prog_rules = this.getRules();
        Iterator i = prog_rules.iterator();
        while (i.hasNext()) {
            Rule rule = (Rule)i.next();
            int normal = 0;
            Iterator j = rule.getLeft().getArguments().iterator();
            while (j.hasNext()) {
                AlgebraTerm arg = (AlgebraTerm)j.next();
                if (!arg.isNormal(prog_rules)) {
                    normal++;
                }
            }
            if (normal > 0) {
                Program.log.log(Level.FINE, "Removing rule {0} as it contains {1} redexes.\n", new Object[] {rule, Integer.valueOf(normal)});
                this.removeRule(rule);
            }
        }
    }

    public Set<Rule> getDeleted() {
        return this.deleted;
    }


    // BEGIN equational stuff


    /** Determines if this program has equations.
     */
    public boolean isEquational() {
    Iterator i = this.defs.iterator();
    while(i.hasNext()) {
        if(!((Set<TRSEquation>)this.getEquations((DefFunctionSymbol)i.next())).isEmpty()) {
        return true;
        }
    }
    i = this.cons.iterator();
    while(i.hasNext()) {
        if(!((Set<TRSEquation>)this.getEquations((ConstructorSymbol)i.next())).isEmpty()) {
        return true;
        }
    }
    return this.hasCollapseEquations();
    }

    /**
     * Determines, whether a program is a String Rewriting
     * System. That is the case, if all symbols have one and only one
     * argument.
     *
     * @return <code>true</code> if the program is a String Rewriting
     * System, <code>false</code> otherwise
     */
    public boolean isStringRewriting() {
    return this.isMaxUnary();
    }


    /** Determines if this program has collapse equations.
     */
    public boolean hasCollapseEquations() {
    return !this.collapse.isEmpty();
    }

    /** Add an equation to this program.
     */
    public void addEquation(TRSEquation equation) {
    Set<Symbol> funs = new HashSet<Symbol>();
    funs.add(equation.getOneSide().getSymbol());
    funs.add(equation.getOtherSide().getSymbol());

    Iterator i = funs.iterator();

    while(i.hasNext()) {
        Symbol symbol = (Symbol)i.next();
        if((symbol instanceof SyntacticFunctionSymbol)) {
            if((symbol instanceof DefFunctionSymbol && this.defs.contains(symbol))
            || (symbol instanceof ConstructorSymbol && this.cons.contains(symbol))) {
                    this.addEquation((SyntacticFunctionSymbol)symbol, equation);
        }
        }
        else if(symbol instanceof VariableSymbol) {
        this.collapse.add(equation);
        }
    }
    }

    /** Add an equation to a certain function symbol.
     */
    public void addEquation(SyntacticFunctionSymbol fun, TRSEquation equation) {
        Set<TRSEquation> equations = this.getAllEquations(fun);
        equations.add(equation);
        this.invalidateCaches(true);
    }

    /** Add a collection of equations to this program.
     */
    public void addEquations(EquationalTheory equations) {
    Iterator i = equations.iterator();
    while(i.hasNext()) {
        this.addEquation((TRSEquation)i.next());
    }
    }

    /** Remove an equation from this program.
     */
    public void removeEquation(TRSEquation eqn) {
        this.deletedEqns.add(eqn);
        this.invalidateCaches(false);
    }

    /** Removes a set of equations from this program.
     */
    public void removeEquations(Set<TRSEquation> eqns) {
    Iterator i = eqns.iterator();
    while(i.hasNext()) {
        this.removeEquation((TRSEquation)i.next());
    }
    }

    /** Returns the set of deleted equations.
     */
    public Set<TRSEquation> getDeletedEquations() {
    return this.deletedEqns;
    }

    /** Returns the set of all equations.
     */
    public EquationalTheory getAllEquations() {
    EquationalTheory res = this.getAllEquations(this.defs);
    res.addAll(this.getAllEquations(this.cons));
    res.addAll(this.collapse);
    return res;
    }

    /** Returns the set of all not deleted equations.
     */
    public EquationalTheory getEquations() {
    EquationalTheory res = this.getEquations(this.defs);
    res.addAll(this.getEquations(this.cons));
    res.addAll(this.collapse);
    return res;
    }

    /** Returns the set of all equations containing an occurence of a function
     * symbol from funs at the root position.
     */
    public EquationalTheory getAllEquations(Set<? extends SyntacticFunctionSymbol> funs) {
        EquationalTheory equations = EquationalTheory.create();
        Iterator i = funs.iterator();
        while (i.hasNext()) {
            SyntacticFunctionSymbol fun = (SyntacticFunctionSymbol)i.next();
            equations.addAll(this.getAllEquations(fun));
        }
        return equations;
    }

    /** Returns the set of all not deleted equations containing an occurence of a function
     * symbol from funs at the root position.
     */
    public EquationalTheory getEquations(Set<? extends SyntacticFunctionSymbol> funs) {
        EquationalTheory equations = EquationalTheory.create();
        Iterator i = funs.iterator();
        while (i.hasNext()) {
            SyntacticFunctionSymbol fun = (SyntacticFunctionSymbol)i.next();
            equations.addAll(this.getEquations(fun));
        }
        return equations;
    }

    /** Returns all equations that belong to the given function symbol.
     */
    public EquationalTheory getAllEquations(SyntacticFunctionSymbol fun) {
        String funname = fun.getName();
        EquationalTheory equations;
    if(fun instanceof DefFunctionSymbol) {
           equations = (EquationalTheory)this.defsequations.get(funname);
    }
    else {
           equations = (EquationalTheory)this.consequations.get(funname);
    }

        if (equations == null) {
            equations = EquationalTheory.create(new LinkedHashSet<TRSEquation>());
        if(fun instanceof DefFunctionSymbol) {
                this.defsequations.put(funname, equations);
        }
        else {
                this.consequations.put(funname, equations);
        }
        }
        return equations;
    }
    /** Returns all equations that belong to the given function symbol and
     * are not deleted.
     */
    public EquationalTheory getEquations(SyntacticFunctionSymbol fun) {
    EquationalTheory res = EquationalTheory.create((this.getAllEquations(fun)));
    res.removeAll(this.deletedEqns);
    return res;
    }

    /** Returns the symbols that have equations. */
    public Set<SyntacticFunctionSymbol> getEquationalSymbols() {
    Set<SyntacticFunctionSymbol> res = new HashSet<SyntacticFunctionSymbol>();
    Set<SyntacticFunctionSymbol> funs = new HashSet<SyntacticFunctionSymbol>();
    funs.addAll(this.defs);
    funs.addAll(this.cons);
    Iterator i = funs.iterator();
    while(i.hasNext()) {
        SyntacticFunctionSymbol symb = (SyntacticFunctionSymbol)i.next();
        if(!this.getEquations(symb).isEmpty()) {
        res.add(symb);
        }
    }
    return res;
    }

    /** Returns the symbols that have no equations. */
    public Set<SyntacticFunctionSymbol> getFreeSymbols() {
    Set<SyntacticFunctionSymbol> res = new HashSet<SyntacticFunctionSymbol>();
    Set<SyntacticFunctionSymbol> funs = new HashSet<SyntacticFunctionSymbol>();
    funs.addAll(this.defs);
    funs.addAll(this.cons);
    Iterator i = funs.iterator();
    while(i.hasNext()) {
        SyntacticFunctionSymbol symb = (SyntacticFunctionSymbol)i.next();
        if(this.getEquations(symb).isEmpty()) {
        res.add(symb);
        }
    }
    return res;
    }

    /** Returns the function symbols that are exactly associative and
     * commutative.
     */
    public Set<SyntacticFunctionSymbol> getACSymbols() {
    Set<SyntacticFunctionSymbol> res = new HashSet<SyntacticFunctionSymbol>();
    Set<SyntacticFunctionSymbol> funs = this.getEquationalSymbols();
    Iterator i = funs.iterator();
    while(i.hasNext()) {
        SyntacticFunctionSymbol symb = (SyntacticFunctionSymbol)i.next();
        if(this.getEquations(symb).isACTheory()) {
        res.add(symb);
        }
    }
    return res;
    }

    /** Returns the names of the function symbols that are exactly associative and
     * commutative.
     */
    public List<String> getACSignature() {
    List<String> res = new Vector<String>();
    Set<SyntacticFunctionSymbol> funs = this.getACSymbols();
    Iterator i = funs.iterator();
    while(i.hasNext()) {
        SyntacticFunctionSymbol symb = (SyntacticFunctionSymbol)i.next();
        res.add(symb.getName());
    }
    return res;
    }

    /** Returns the function symbols that are exactly commutative.
     */
    public Set<SyntacticFunctionSymbol> getCSymbols() {
    Set<SyntacticFunctionSymbol> res = new HashSet<SyntacticFunctionSymbol>();
    Set<SyntacticFunctionSymbol> funs = this.getEquationalSymbols();
    Iterator i = funs.iterator();
    while(i.hasNext()) {
        SyntacticFunctionSymbol symb = (SyntacticFunctionSymbol)i.next();
        if(this.getEquations(symb).isCTheory()) {
        res.add(symb);
        }
    }
    return res;
    }

    /** Returns the names of the function symbols that are exactly commutative.
     */
    public List<String> getCSignature() {
    List<String> res = new Vector<String>();
    Set<SyntacticFunctionSymbol> funs = this.getCSymbols();
    Iterator i = funs.iterator();
    while(i.hasNext()) {
        SyntacticFunctionSymbol symb = (SyntacticFunctionSymbol)i.next();
        res.add(symb.getName());
    }
    return res;
    }

    /** Returns the function symbols that are exactly associative.
     */
    public Set<SyntacticFunctionSymbol> getASymbols() {
    Set<SyntacticFunctionSymbol> res = new HashSet<SyntacticFunctionSymbol>();
    Set<SyntacticFunctionSymbol> funs = this.getEquationalSymbols();
    Iterator i = funs.iterator();
    while(i.hasNext()) {
        SyntacticFunctionSymbol symb = (SyntacticFunctionSymbol)i.next();
        if(this.getEquations(symb).isATheory()) {
        res.add(symb);
        }
    }
    return res;
    }

    /** Returns the names of the function symbols that are exactly associative.
     */
    public List<String> getASignature() {
    List<String> res = new Vector<String>();
    Set<SyntacticFunctionSymbol> funs = this.getASymbols();
    Iterator i = funs.iterator();
    while(i.hasNext()) {
        SyntacticFunctionSymbol symb = (SyntacticFunctionSymbol)i.next();
        res.add(symb.getName());
    }
    return res;
    }

    /** Returns the function symbols that have equations but are neither
     * AC nor C nor A.
     */
    public Set<SyntacticFunctionSymbol> getStrangeEquationalSymbols() {
    Set<SyntacticFunctionSymbol> res = this.getEquationalSymbols();
    res.removeAll(this.getACSymbols());
    res.removeAll(this.getCSymbols());
    res.removeAll(this.getASymbols());
    return res;
    }

    /** Determines whether this program has equational symbols that are neither A nor AC nor C.
     */
    public boolean hasStrangeEquationalSymbols() {
    return !this.getStrangeEquationalSymbols().isEmpty();
    }

    /** Transforms the A symbols into AC symbols. This is destructive!
     */
    public void transformAtoAC() {
    this.origin = this.deepercopy();
    this.origin.setType(AbstractProgram.A_TO_AC);
    Iterator i = this.getASymbols().iterator();
    while(i.hasNext()) {
        SyntacticFunctionSymbol f = (SyntacticFunctionSymbol)i.next();
        TRSEquation eq = this.getEquations(f).iterator().next();
        Set<AlgebraVariable> vars = eq.getOneSide().getVars();
        Iterator j = vars.iterator();
        AlgebraVariable x = (AlgebraVariable)j.next();
        AlgebraVariable y = (AlgebraVariable)j.next();
        Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
        args.add(x);
        args.add(y);
        AlgebraTerm fxy = AlgebraFunctionApplication.create(f, args);
        args = new Vector<AlgebraTerm>();
        args.add(y);
        args.add(x);
        AlgebraTerm fyx = AlgebraFunctionApplication.create(f, args);
        this.addEquation(TRSEquation.create(fxy, fyx));
    }
    }

    /** Returns an extension of this program suitable for equational DP proofs.
     */
    public Program equationalExt() {
    if(this.equationalExt==null) {
        this.createEquationalExt();
    }
    return this.equationalExt;
    }

    /** Creates an extension of this program suitable for equational DP proofs.
     */
    private void createEquationalExt() {
    if(this.getEquationalSymbols().isEmpty()) {
        this.equationalExt = this;
        return;
    }

    Set<SyntacticFunctionSymbol> strange = this.getStrangeEquationalSymbols();
    // Set<FunctionSymbol> ACnC = this.getACnCSymbols();
    if(!this.getASymbols().isEmpty()) {
        throw new RuntimeException("A is not yet supported by equational stuff!");
    }

    if(!strange.isEmpty()) {
        EquationalTheory eqns = this.getEquations(strange);
        if(!eqns.isConstructorTheory()) {
            throw new RuntimeException("This is not yet supported by equational stuff!");
        }
        /* no extension needed for constructor theory */
    }

    /* ACnC case */
        this.equationalExt = this.deepercopy();
    this.equationalExt.origin = this;
    this.equationalExt.getOrigin().setType(AbstractProgram.EQUATIONAL);

    FreshVarGenerator fvg = new FreshVarGenerator(this.getVars());
    Set<SyntacticFunctionSymbol> ACs = this.getACSymbols();
        Set<SyntacticFunctionSymbol> Cs = this.getCSymbols();
    Iterator i = ACs.iterator();
    while(i.hasNext()) {
        SyntacticFunctionSymbol f = (SyntacticFunctionSymbol)i.next();
        Sort sort = f.getSort();
        AlgebraVariable y = fvg.getFreshVariable("ext", sort, true);
        Set<Rule> rules = this.getRules(f);
        Iterator j = rules.iterator();
            LightweightRules fRules = LightweightRules.create(rules);
        while(j.hasNext()) {
        Rule rule = (Rule)j.next();
        if(!this.noACExtensionNeeded(rule, ACs)) {
             AlgebraTerm l = this.extAC(f, rule.getLeft(), y);
            AlgebraTerm r = this.extAC(f, rule.getRight(), y);
                    Rule newRule = Rule.create(l, r);
                    if(!this.hasEquivalentRule(newRule, fRules, ACs, Cs)) {
                        this.equationalExt.addRule(newRule);
                    }
        }
        }
    }
    }

    private boolean noACExtensionNeeded(Rule rule, Set<SyntacticFunctionSymbol> ACs) {
    AlgebraTerm l = rule.getLeft();
    AlgebraTerm r = rule.getRight();
    boolean sameSymbol = l.getSymbol().equals(r.getSymbol());
    boolean res = false;
    Set<AlgebraVariable> lCand = ACTerm.create(l, ACs).getLinearImmediateVars();
    if(r.isVariable()) {
        res = lCand.contains(r);
    }
    else {
        if(sameSymbol) {
        Set<AlgebraVariable> rCand = ACTerm.create(r, ACs).getLinearImmediateVars();
        rCand.retainAll(lCand);
        res = !rCand.isEmpty();
        }
    }
    return res;
    }

    private boolean hasEquivalentRule(Rule rule, LightweightRules rules, Set<SyntacticFunctionSymbol> ACs, Set<SyntacticFunctionSymbol> Cs) {
        LightweightRule newRule = LightweightRule.create(rule);
        Iterator i = rules.iterator();
        while(i.hasNext()) {
            LightweightRule testR = (LightweightRule)i.next();
            if(ACnCTerm.create(testR.getTransLeft(), ACs, Cs).equals(ACnCTerm.create(newRule.getTransLeft(), ACs, Cs)) &&
               ACnCTerm.create(testR.getTransRight(), ACs, Cs).equals(ACnCTerm.create(newRule.getTransRight(), ACs, Cs))) {
                return true;
            }
        }
        return false;
    }

    private AlgebraTerm extAC(SyntacticFunctionSymbol f, AlgebraTerm t, AlgebraVariable y) {
    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
    args.add(t);
    args.add(y);
    return AlgebraFunctionApplication.create(f, args);
    }

    /** Returns an unification procedure suitable for unification in the context of this program.
     */
    public GeneralUnification getUnificator() {
    if(!this.isEquational()) {
        return new SyntacticUnification();
    }

    GeneralUnification res;
    Set<SyntacticFunctionSymbol> ACs = this.getACSymbols();
    Set<SyntacticFunctionSymbol> Cs = this.getCSymbols();
    Set<SyntacticFunctionSymbol> As = this.getASymbols();
    // Set<FunctionSymbol> AnACnC = this.getAnACnCSymbols();
    Set<SyntacticFunctionSymbol> strange = this.getStrangeEquationalSymbols();

    if(!As.isEmpty()) {
        throw new RuntimeException("A unification is not yet supported!");
    }
    if(Cs.isEmpty()) {
        res = new GeneralAC(ACs);
    }
    else {
        res = new GeneralACnC(ACs, Cs);
    }

    if(!strange.isEmpty()) {
        EquationalTheory eqns = this.getEquations(strange);
        Map theoryIndices = eqns.getTheoryIndices();
        res = new CrudeApproxUnification(res, this.getFreeSymbols(), eqns.getRootSymbols(), theoryIndices);
    }

    return res;
    }

    /** Determines whether all equations are permutative equations.
     * @see TRSEquation#isPermutative()
     */
    public boolean isPermutative() {
    boolean res = true;
        Iterator i = this.getEquations().iterator();
    while(res && i.hasNext()) {
        res = ((TRSEquation)i.next()).isPermutative();
    }
    return res;
    }

    /** Returns the set of A and AC and C symbols for this program.
     */
    public Set<SyntacticFunctionSymbol> getAnACnCSymbols() {
    Set<SyntacticFunctionSymbol> res = this.getASymbols();
    res.addAll(this.getACSymbols());
    res.addAll(this.getCSymbols());
    return res;
    }

    /** Returns the set of AC and C symbols for this program.
     */
    public Set<SyntacticFunctionSymbol> getACnCSymbols() {
    Set<SyntacticFunctionSymbol> res = this.getACSymbols();
    res.addAll(this.getCSymbols());
    return res;
    }

    /** Determines whether Dependeny Pairs proofs can be done with this program.
     */
    public boolean isDpAble() {
        if (!this.collapse.isEmpty()) {
            /* no way! */
            return false;
        }
    Set<SyntacticFunctionSymbol> sFuns = this.getStrangeEquationalSymbols();
    if(sFuns.isEmpty()) {
        /* at most A and AC and C */
        return true;
    }

    /* strange symbols and possibly A or AC or C symbols */
    EquationalTheory sEqns = this.getEquations(sFuns);
    return sEqns.isDpSuitable() && sEqns.isConstructorTheory();
    }

    /** Determines whether Dp proofs for this program can use Ce criteria.
     */
    public boolean isCeAble() {
    return this.isPermutative();
    //Set<FunctionSymbol> sFuns = this.getStrangeEquationalSymbols();
    //if(sFuns.isEmpty()) {
        /* at most A and AC and C */
        //return true;
    //}
    //return false;
    }

    // END of equational stuff


    /** Returns the used variables of this program.
     */
    public Set<AlgebraVariable> getVars() {
    Set<AlgebraVariable> vars = new LinkedHashSet<AlgebraVariable>();
    Iterator i = this.getRules().iterator();
    while(i.hasNext()) {
        Rule rule = (Rule)i.next();
        vars.addAll(rule.getUsedVariables());
    }
    i = this.getEquations().iterator();
    while(i.hasNext()) {
        TRSEquation eqn = (TRSEquation)i.next();
        vars.addAll(eqn.getUsedVariables());
    }
    return vars;
    }

    public boolean isSimplifiable() {
    return this.isSimplifiable;
    }

    public void setSimplifiable(boolean b) {
    this.isSimplifiable = b;
    }

    public boolean isFromProlog() {
    return this.isFromProlog;
    }

    public void setFromProlog(boolean b) {
    this.isFromProlog = b;
    }

    /**
     * Checks if this program only contains unary function symbols
     * and constants and checks if the TRS is not equational
     */
    public boolean isMaxUnary() {
        if (this.maxUnarySymbols != MAYBE) {
            return this.maxUnarySymbols.toBool();
        }
        if (this.unarySymbols == YES) {
            this.maxUnarySymbols = YES;
            return true;
        }
        if (this.isEquational()) {
            this.maxUnarySymbols = NO;
            return false;
        }
        if (this.isConditional()) {
            this.maxUnarySymbols = NO;
            return false;
        }
        Iterator i = this.getRules().iterator();
        while (i.hasNext()) {
            Rule r = (Rule)i.next();
            if (!r.isMaxUnary()) {
                this.maxUnarySymbols = NO;
                return false;
            }
        }
        this.maxUnarySymbols = YES;
        return true;
    }

    public boolean isPredefFunctionSymbol(Symbol symbol) {
        if(symbol instanceof DefFunctionSymbol) {
            return this.predefs.contains(symbol);
        }else{
            return false;
        }
    }

    /**
     * Checks if this program only contains unary function symbols
     * and is not equational
     */
    public boolean isUnary() {
        if (this.unarySymbols != MAYBE) {
            return this.unarySymbols.toBool();
        }
        if (this.maxUnarySymbols == NO) {
            this.unarySymbols = NO;
            return false;
        }
        if (this.isEquational()) {
            this.unarySymbols = NO;
            return false;
        }
        Iterator i = this.getRules().iterator();
        while (i.hasNext()) {
            Rule r = (Rule)i.next();
            if (!r.isUnary()) {
                this.unarySymbols = NO;
                return false;
            }
        }
        this.unarySymbols = YES;
        return true;
    }

    /**
     * Reverse all lhs and rhs of this program.
     * @return A new program with lhs and rhs reversed.
     */
    public Program reverse() {

        Set<Rule> newRules = new LinkedHashSet<Rule>();
        Set<Rule> oldRules = this.getRules();
        Set<String> names = new LinkedHashSet<String>();
        for (SyntacticFunctionSymbol f : Rule.getFunctionSymbols(oldRules)) {
            names.add(f.getName());
        }
        FreshNameGenerator fg = new FreshNameGenerator(names, FreshNameGenerator.FRIENDLYNAMES);
        for (Rule r : oldRules) {
            Rule newR = r.reverse(fg);
            newRules.add(newR);
        }
    return Program.create(newRules);

    }

    public static Set<Rule> updateConsDefs(Collection<Rule> rules) {

    Set<SyntacticFunctionSymbol> toDefs = Rule.getLeftRootSymbols(rules);
    Set<SyntacticFunctionSymbol> toCons = Rule.getFunctionSymbols(rules);
    toCons.removeAll(toDefs);
        Set<Rule> newRules = new LinkedHashSet<Rule>();
        Iterator i = rules.iterator();
        while (i.hasNext()) {
            Rule rule = (Rule) i.next();
            newRules.add(rule.updateConsDef(toCons, toDefs));
        }
        return newRules;

    }


    public static Set<Rule> updateConsDefs(Collection<Rule> rules, Set<SyntacticFunctionSymbol> toCons, Set<SyntacticFunctionSymbol> toDefs) {

    Set<Rule> newRules = new LinkedHashSet<Rule>();
    for (Rule rule : rules) {
        AlgebraTerm l = rule.getLeft().updateConsDef(toCons, toDefs);
        AlgebraTerm r = rule.getRight().updateConsDef(toCons, toDefs);
        newRules.add(Rule.create(l, r));
    }

    return newRules;
    }

    public static Set<Rule> updateConsDefs(Collection<Rule> rules, Program reference) {
    // Collect all defined function symbols from the reference and
    // the left sides of rules

    Set<SyntacticFunctionSymbol> toDefs = Rule.getLeftRootSymbols(rules);
    for (SyntacticFunctionSymbol sym : reference.getDefFunctionSymbols()) {
        if (!(sym instanceof TupleSymbol)) {
        toDefs.add(sym);
        }
    }

    // All other symbols will be constructors

    Set<SyntacticFunctionSymbol> toCons = Rule.getFunctionSymbols(rules);
        toCons.removeAll(toDefs);
    for (SyntacticFunctionSymbol sym : reference.getConstructorSymbols()) {
        if (!(sym instanceof TupleSymbol) && !toDefs.contains(sym)) {
        toCons.add(sym);
        }
    }

    return Program.updateConsDefs(rules, toCons, toDefs);

    }


    public static Pair<Set<Rule>, Set<Rule>> updateConsDefs(Collection<Rule> rules, Collection<Rule> dps) {
    // Collect all defined function symbols from
    // the left sides of rules

    Set<SyntacticFunctionSymbol> toDefs = Rule.getLeftRootSymbols(rules);

    // All other symbols will be constructors

    Set<SyntacticFunctionSymbol> toCons = Rule.getFunctionSymbols(rules);
        toCons.removeAll(toDefs);
    Set<Rule> newRules = Program.updateConsDefs(rules, toCons, toDefs);
    Set<Rule> newDps   = Program.updateConsDefs(dps,   toCons, toDefs);

    return new Pair<Set<Rule>, Set<Rule>>(newRules, newDps);

    }

    public void addWaveRule(WaveRule rule) {
        this.waveRules.add(rule);
    }

    public void addAllWaveRules(Collection<WaveRule> waveRules) {
        this.waveRules.addAll(waveRules);
    }

    public void removeWaveRule(Rule rule) {
        this.waveRules.remove(rule);
    }

    public Set<WaveRule> getWaveRules() {
        return this.waveRules;
    }

    public WaveHole getWaveHoleSymbol() {

        if(this.waveHole == null) {
            FreshNameGenerator freshNameGenerator = new FreshNameGenerator(this.getFunctionSymbols(),
                FreshNameGenerator.FRIENDLYNAMES);
            this.waveHole = WaveHole.create(freshNameGenerator.getFreshName("WH",true),1);
        }

        return this.waveHole;
    }

    public WaveFrontIn getWaveFrontInSymbol() {

        if(this.waveFrontIn == null) {
            FreshNameGenerator freshNameGenerator = new FreshNameGenerator(this.getFunctionSymbols(),
                FreshNameGenerator.FRIENDLYNAMES);
            this.waveFrontIn = WaveFrontIn.create(freshNameGenerator.getFreshName("WF_IN",true),1);
        }

        return this.waveFrontIn;
    }

    public WaveFrontOut getWaveFrontOutSymbol() {

        if(this.waveFrontOut == null) {
            FreshNameGenerator freshNameGenerator = new FreshNameGenerator(this.getFunctionSymbols(),
                FreshNameGenerator.FRIENDLYNAMES);
            this.waveFrontOut = WaveFrontOut.create(freshNameGenerator.getFreshName("WF_OUT",true),1);
        }

        return this.waveFrontOut;

    }

    private final static String INDENT_STRING = "  ";

    private int indent(String head, StringBuffer sb, int indent) {
        indent = Program.preindent(head, sb, indent);
        Program.level(sb, indent);
        return indent;
    }

    private static int preindent(String head, StringBuffer sb, int indent) {
        sb.append("(");
        sb.append(head);
        indent++;
        return indent;
    }

    private static int dedent(StringBuffer sb, int indent) {
        indent--;
        Program.level(sb, indent);
        sb.append(")");
        return indent;
    }

    private static void level(StringBuffer sb, int indent) {
        sb.append("\n");
        for (int i = 0; i < indent; i++) {
            sb.append(Program.INDENT_STRING);
        }
    }

    public void toACL2(StringBuffer sb, int indent, FreshNameGenerator fng, boolean fullLists) {
        for (Set<Node<Sort>> rank : this.getSortGraph().getRanks()) {
            for (Node<Sort> sortNode : rank) {
                Sort sort = sortNode.getObject();
                Program.level(sb, indent);
                sort.toACL2(sb, indent, fng, fullLists);
            }
        }
        List<DefFunctionSymbol> defs = new ArrayList<DefFunctionSymbol>();
        Set<Rule> callRules = new LinkedHashSet<Rule>();
        for (Rule rule : this.getAllRules()) {
            callRules.add(Rule.create(rule.left, rule.right));
            for (Rule cond : rule.getConds()) {
                callRules.add(Rule.create(rule.left, cond.left));
            }
        }
        Program callProgram = Program.create(callRules);
        for (Set<Node<Cycle<DefFunctionSymbol>>> rank : new SCCGraph<DefFunctionSymbol,Object>(callProgram.getCallGraph(true),false).getRanks()) {
            for (Node<Cycle<DefFunctionSymbol>> condensedNode : rank) {
                for (Node<DefFunctionSymbol> node : condensedNode.getObject()) {
                    DefFunctionSymbol def = node.getObject();
                    defs.add(def);
                }
            }
        }
//        for (DefFunctionSymbol def : this.getDefFunctionSymbols()) {
        for (DefFunctionSymbol def : defs) {
            Program.level(sb, indent);
            Set<Rule> rules = this.getAllRules(def);
            List<RuleInfo> ruleInfos = new ArrayList<RuleInfo>();
            for (Rule rule : rules) {
                RuleInfo ruleInfo = new RuleInfo(rule.getRight(), rule.getConds());
                AlgebraFunctionApplication lhs = (AlgebraFunctionApplication) rule.getLeft();
                int arity = lhs.getFunctionSymbol().getArity();
                for (int i = 0; i < arity; i++) {
                    List<Integer> argNum = new LinkedList<Integer>();
                    List<Boolean> argLast = new LinkedList<Boolean>();
                    this.findConditions(lhs.getArgument(i),i,ruleInfo,argNum,argLast);
                }
                ruleInfos.add(ruleInfo);
            }
            //sb.append(ruleInfos);
            int arity = def.getArity();
            indent = this.indent("defun "+fng.getFreshName(def.getName(), true)+" ("+Program.varList(arity)+")", sb, indent);
            indent = this.indent("if", sb, indent);
            indent = Program.preindent("and", sb, indent);
            for (int i = 0; i < arity; i++) {
                Program.level(sb, indent);
                indent = this.indent(fng.getFreshName("is"+def.getArgSort(i).getName(), true), sb, indent);
                sb.append("x");
                sb.append(i);
                indent = Program.dedent(sb, indent);
            }
            indent = Program.dedent(sb, indent);
            Program.level(sb, indent);
            for (int i = 0; i < ruleInfos.size(); i++) {
                RuleInfo ruleInfo = ruleInfos.get(i);
                List<SymCondition> conds = i+1 < ruleInfos.size() ? ruleInfo.getConds() : new ArrayList<SymCondition>();
                indent = this.indent("if", sb, indent);
                indent = Program.preindent("and", sb, indent);
                for (SymCondition cond : conds) {
                    Program.level(sb, indent);
                    indent = this.indent("eq", sb, indent);
                    int oldIndent = indent;
                    if (fullLists || cond.toCheck.getArity() > 0) {
                        indent = this.indent("car", sb, indent);
                    }
                    while (!cond.argNum.isEmpty()) {
                        int argNum = cond.argNum.get(0);
                        boolean last = cond.argLast.get(0);
                        cond.argNum.remove(0);
                        cond.argLast.remove(0);
                        if (fullLists || !last) {
                            indent = this.indent("car", sb, indent);
                        }
                        for (int j = 0; j <= argNum; j++) {
                            indent = this.indent("cdr", sb, indent);
                        }
                    }
                    sb.append("x");
                    sb.append(cond.varNum);
                    while (indent > oldIndent) {
                        indent = Program.dedent(sb, indent);
                    }
                    Program.level(sb, indent);
                    sb.append("'");
                    sb.append(fng.getFreshName(cond.toCheck.getName(),true));
                    indent = Program.dedent(sb, indent);
                }
                for (Rule cond : ruleInfo.ruleConds) {
                    Program.level(sb, indent);
                    indent = this.indent("eq", sb, indent);
                    cond.getLeft().toACL2(sb, indent, fng, ruleInfo, fullLists);
                    Program.level(sb, indent);
                    cond.getRight().toACL2(sb, indent, fng, ruleInfo, fullLists);
                    indent = Program.dedent(sb, indent);
                }
                indent = Program.dedent(sb, indent);
                Program.level(sb, indent);
                ruleInfo.rhs.toACL2(sb, indent, fng, ruleInfo, fullLists);
                Program.level(sb, indent);
            }
            AlgebraTerm witness = def.getSort().getWitnessTermCandidate();
            witness.toACL2(sb, indent, fng, null, fullLists);
            for (int i = 0; i < ruleInfos.size(); i++) {
                indent = Program.dedent(sb, indent);
            }
            Program.level(sb, indent);
            witness.toACL2(sb, indent, fng, null, fullLists);
            indent = Program.dedent(sb, indent);
            indent = Program.dedent(sb, indent);
        }
    }

    private SCCGraph<Sort,Object> getSccSortGraph() {
        return new SCCGraph<Sort,Object>(this.getSortGraph());
    }
    public Graph<Sort,Object> getSortGraph() {
        Graph<Sort,Object> sortGraph = new Graph<Sort,Object>();
        for (Sort sort : this.getSorts()) {
            sortGraph.addNode(new Node<Sort>(sort));
        }
        for (Sort sort : this.getSorts()) {
            Node<Sort> sortNode = sortGraph.getNodeFromObject(sort);
            for (ConstructorSymbol cons : sort.getConstructorSymbols()) {
                for (Sort argSort : cons.getArgSorts()) {
                    if (sort.equals(argSort)) {
                        continue;
                    }
                    Node<Sort> argSortNode = sortGraph.getNodeFromObject(argSort);
                    sortGraph.addEdge(sortNode, argSortNode);
                }
            }
        }
        return sortGraph;
    }

    private static String varList(int arity) {
        StringBuffer sb = new StringBuffer();
        boolean first = true;
        for (int i = 0; i < arity; i++) {
            if (first) {
                first = false;
            } else {
                sb.append(" ");
            }
            sb.append("x");
            sb.append(i);
        }
        return sb.toString();
    }

    private void findConditions(AlgebraTerm argument, int varNum, RuleInfo ruleInfo, List<Integer> argNum, List<Boolean> argLast) {
        if (argument.isVariable()) {
            ruleInfo.put((AlgebraVariable) argument, varNum, new ArrayList<Integer>(argNum), new ArrayList<Boolean>(argLast));
        } else {
            AlgebraFunctionApplication app = (AlgebraFunctionApplication) argument;
            SyntacticFunctionSymbol toCheck = app.getFunctionSymbol();
            ruleInfo.add(varNum, new ArrayList<Integer>(argNum), new ArrayList<Boolean>(argLast), toCheck);
            int arity = toCheck.getArity();
            for (int i = 0; i < arity; i++) {
                argNum.add(0,i);
                argLast.add(0,i+1 == arity);
                this.findConditions(app.getArgument(i), varNum, ruleInfo, argNum, argLast);
                argNum.remove(0);//argNum.size()-1);
                argLast.remove(0);//argLast.size()-1);
            }
        }
    }

    public static class RuleInfo {
        List<SymCondition> conds = new ArrayList<SymCondition>();
        Map<AlgebraVariable,Integer> var2varNum;
        Map<AlgebraVariable,List<Integer>> var2argNum;
        Map<AlgebraVariable,List<Boolean>> var2argLast;
        AlgebraTerm rhs;
        List<Rule> ruleConds;
        public RuleInfo(AlgebraTerm rhs, List<Rule> ruleConds) {
            this.rhs = rhs;
            this.ruleConds = ruleConds;
            this.var2varNum = new LinkedHashMap<AlgebraVariable,Integer>();
            this.var2argNum = new LinkedHashMap<AlgebraVariable,List<Integer>>();
            this.var2argLast = new LinkedHashMap<AlgebraVariable,List<Boolean>>();
        }
        public List<SymCondition> getConds() {
            return this.conds;
        }
        public void put(AlgebraVariable var, int varNum, List<Integer> argNum, List<Boolean> argLast) {
            this.var2varNum.put(var, varNum);
            this.var2argNum.put(var, argNum);
            this.var2argLast.put(var, argLast);
        }
        public void add(int varNum, List<Integer> argNum, List<Boolean> argLast, SyntacticFunctionSymbol toCheck) {
            this.conds.add(new SymCondition(varNum, argNum, argLast, toCheck));
        }
        @Override
        public String toString() {
            StringBuffer sb = new StringBuffer();
            for (SymCondition cond : this.conds) {
                sb.append(cond);
                sb.append("\n");
            }
            sb.append(this.var2varNum);
            sb.append("\n");
            sb.append(this.var2argNum);
            sb.append("\n");
            sb.append(this.var2argLast);
            sb.append("\n");
            sb.append(this.rhs);
            sb.append("\n");
            return sb.toString();
        }
        public Integer getVarNum(AlgebraVariable var) {
            return this.var2varNum.get(var);
        }
        public List<Integer> getArgNum(AlgebraVariable var) {
            return this.var2argNum.get(var);
        }
        public List<Boolean> getArgLast(AlgebraVariable var) {
            return this.var2argLast.get(var);
        }
    }

    private static class SymCondition {
        int varNum;
        List<Integer> argNum;
        List<Boolean> argLast;
        SyntacticFunctionSymbol toCheck;
        public SymCondition(int varNum, List<Integer> argNum, List<Boolean> argLast, SyntacticFunctionSymbol toCheck) {
            this.varNum = varNum;
            this.argNum = argNum;
            this.argLast = argLast;
            this.toCheck = toCheck;
        }
        @Override
        public String toString() {
            StringBuffer sb = new StringBuffer();
            sb.append(this.varNum);
            sb.append(this.argNum);
            sb.append(this.argLast);
            sb.append(this.toCheck);
            return sb.toString();
        }
    }

    public boolean hasBinarySort() {
        sortLoop: for (Sort sort : this.getSorts()) {
            boolean binary = false;
            consLoop: for (ConstructorSymbol cons : sort.getConstructorSymbols()) {
                switch (cons.getArity()) {
                case 0:
                    continue consLoop;
                case 2:
                    binary = true;
                    break;
                default:
                    continue sortLoop;
                }
            }
            if (binary) {
                return true;
            }
        }
        return false;
    }

}
