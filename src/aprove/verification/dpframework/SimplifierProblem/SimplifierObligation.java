package aprove.verification.dpframework.SimplifierProblem;
import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Programs.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.Simplifier.*;

public class SimplifierObligation {
    protected static final int RWLABELLIMIT = 3;
    protected static final int RWITERLIMIT = 500;
    protected static final int RWDEPTHLIMIT = 100;
    protected static final int RWSIZELIMIT = 1000;

    public Hashtable critRecCallsTable = null;

    /** Stores the function symbols where an attempt to prove
     *  j-commutativity failed.
     */
    protected Set<DefFunctionSymbol> failedJComFuncs;
    protected Set<DefFunctionSymbol> terminating;
    protected Set<DefFunctionSymbol> forCheck;

    public FreshNameGenerator symbnames;
    /** A counter to ensure a unique name for each projection. */
    private int projcount;
    public Hashtable<Vector<Sort>,DefFunctionSymbol> projections;

    /** Type-based projections */
    public Hashtable<Vector<AlgebraTerm>, DefFunctionSymbol> projectionsTyped;

    /** Types of functions */
    public TypeContext typeContext;

    /** The program that is to be transformed. */
    public Program program;
    /** The rootprogram is the original program. I.e. the program that
     *  has no origin.
     */
    public Program rootprogram;
    /** Maps a defining function-symbol to its set of rules. */
    public Map<DefFunctionSymbol,Set<Rule>> defsrules;
    /** Maps a defining funtion to its original rules if it is
     *  necessarry that this function gets its old rules back.
     *  (E.g. and, or and equal_*.)
     */
    protected Map<DefFunctionSymbol,Set<Rule>> origrules;
    /** list of all defined functions w/o projections */
    public Set<DefFunctionSymbol> defs;

    /** not yet handled Mutual Recursive Blocks (MRBs) of this program
     */
    public List<Set<DefFunctionSymbol>> remainingMRBs;

    /** the terminating MRBs
     */
    public List<Set<DefFunctionSymbol>> terminMRBs;

    /** the MRBs for which termination is unknown
     */
    public List<Set<DefFunctionSymbol>> unknownMRBs;

    /** A hashtable which gives a set of function-symbols that a
     *  given function-symbol directly depends on.
     */
    public Hashtable<DefFunctionSymbol,Set<DefFunctionSymbol>> dependencies;
    /** A set of function symbols that should be ignored when doing
     *  a identity-transformation. (For example because it is a result
     *  of such a transformation.
     */
    public Set<DefFunctionSymbol> ignoreIdentity;
    /** This set of functions have been processed and thus are fix.
     */
    protected Set<DefFunctionSymbol> fixedFunctions;
    protected static Logger log = Logger.getLogger("");
    public Set<DefFunctionSymbol> mainFunctions;
    protected Sort bool;
    public DefFunctionSymbol fAnd;
    public DefFunctionSymbol fOr;
    public DefFunctionSymbol fNot;
    public ConstructorSymbol cTrue;
    public ConstructorSymbol cFalse;
    /** Maps from defined function symbols to a collection of defined
     *  functions symbols that where created during uncond.-translation. */
    protected Hashtable<DefFunctionSymbol,Set<Rule>> uncondfuncs;
    /** Maps a defined function symbol to a set of rules that is suitable
     *  for symbolic evaluation.
     */
    protected Hashtable<DefFunctionSymbol,Set<Rule>> projdefsrules;
    protected boolean isMRB;
    protected boolean isMRBTerminating;
    protected boolean lastMRBsTerminating;

    /* Constructors */

    public SimplifierObligation(SimplifierObligation obl){
       this.failedJComFuncs = new HashSet<DefFunctionSymbol>(obl.failedJComFuncs);
       this.terminating = new HashSet<DefFunctionSymbol>(obl.terminating);
       this.forCheck = new HashSet<DefFunctionSymbol>(obl.forCheck);

       this.symbnames = obl.symbnames.shallowcopy();
       this.projcount = obl.projcount;

       this.projections = new Hashtable<Vector<Sort>,DefFunctionSymbol>(obl.projections);

       // Type based projections
       this.projectionsTyped = new Hashtable<Vector<AlgebraTerm>, DefFunctionSymbol>(obl.projectionsTyped);
       this.typeContext = obl.typeContext.deepcopy();


       this.program = obl.program;
       this.rootprogram = obl.rootprogram;
       this.defsrules = new HashMap<DefFunctionSymbol,Set<Rule>>(obl.defsrules);

       this.remainingMRBs = new Vector<Set<DefFunctionSymbol>>();
       this.terminMRBs = new Vector<Set<DefFunctionSymbol>>();
       this.unknownMRBs = new Vector<Set<DefFunctionSymbol>>();
       for(Set<DefFunctionSymbol> mrb : obl.remainingMRBs) {
           this.remainingMRBs.add(new HashSet<DefFunctionSymbol>(mrb));
       }
       for(Set<DefFunctionSymbol> mrb : obl.terminMRBs) {
           this.terminMRBs.add(new HashSet<DefFunctionSymbol>(mrb));
       }
       for(Set<DefFunctionSymbol> mrb : obl.unknownMRBs) {
           this.unknownMRBs.add(new HashSet<DefFunctionSymbol>(mrb));
       }

       this.origrules = obl.origrules;
       this.defs = new HashSet<DefFunctionSymbol>(obl.defs);
       this.dependencies = new Hashtable<DefFunctionSymbol,Set<DefFunctionSymbol>>(obl.dependencies);
       this.ignoreIdentity = new HashSet<DefFunctionSymbol>(obl.ignoreIdentity);
       this.fixedFunctions = new HashSet<DefFunctionSymbol>(obl.fixedFunctions);
       this.mainFunctions = new HashSet<DefFunctionSymbol>(obl.mainFunctions);
       this.bool = obl.bool;
       this.fAnd = obl.fAnd;
       this.fOr = obl.fOr;
       this.fNot = obl.fNot;
       this.cTrue = obl.cTrue;
       this.cFalse = obl.cFalse;
       this.uncondfuncs = obl.uncondfuncs;
       this.projdefsrules = new Hashtable<DefFunctionSymbol,Set<Rule>>(obl.projdefsrules);
       this.isMRB = obl.isMRB;
       this.isMRBTerminating = obl.isMRBTerminating;
       this.lastMRBsTerminating = obl.lastMRBsTerminating;

    }


    public SimplifierObligation(Program prog) {
        this.isMRB = false;
        this.isMRBTerminating = false;
        this.lastMRBsTerminating = true;
    this.failedJComFuncs = new HashSet<DefFunctionSymbol>();
        this.terminating = new HashSet<DefFunctionSymbol>();
        this.forCheck = new HashSet<DefFunctionSymbol>();
    this.uncondfuncs = new Hashtable<DefFunctionSymbol,Set<Rule>>();
    this.projdefsrules = new Hashtable<DefFunctionSymbol,Set<Rule>>();
    this.projcount = 0;
    this.projections = new Hashtable<Vector<Sort>,DefFunctionSymbol>();

    // copy the types
    this.projectionsTyped = new Hashtable<Vector<AlgebraTerm>,DefFunctionSymbol>();
    this.typeContext = prog.getTypeContext().deepcopy();

    Set<String> used = new HashSet<String>(prog.getSignature());
    Iterator<AlgebraVariable> itv = prog.getVars().iterator();
    while (itv.hasNext()) {
        used.add(itv.next().getSymbol().getName());
    }
    this.symbnames = new FreshNameGenerator(used, FreshNameGenerator.VARIABLES);
    this.program = prog;
    Program tmpprg = prog;
    while (tmpprg != null) {
        this.rootprogram = tmpprg;
        tmpprg = (Program)tmpprg.getOrigin();
    }
    this.defsrules = new LinkedHashMap<DefFunctionSymbol,Set<Rule>>();
    Iterator<DefFunctionSymbol> itd = prog.getDefFunctionSymbols().iterator();
    while (itd.hasNext()) {
        DefFunctionSymbol def = itd.next();
        Set<Rule> rules = prog.getAllRules(def);
        this.defsrules.put(def, rules);
        this.translateFunction(def, rules); // the result is not used and rules is not affected at all... --matraf
    }

    // set the termination of function symbols
    for(DefFunctionSymbol fsym : prog.getDefFunctionSymbols()) {
        if (fsym.getTermination()) {
            this.setTerminating(fsym);
        }
    }

    this.origrules = new LinkedHashMap<DefFunctionSymbol,Set<Rule>>();
    this.defs = new HashSet<DefFunctionSymbol>();
    this.fixedFunctions = new HashSet<DefFunctionSymbol>();
    this.computeDependencies();
    this.ignoreIdentity = new HashSet<DefFunctionSymbol>();
    Predefined predefined = this.rootprogram.getPredefined();
    this.bool = predefined.getBool();
    this.cTrue = predefined.getTrue();
    this.cFalse = predefined.getFalse();
    this.fAnd = predefined.getAnd();
    this.fOr = predefined.getOr();
    this.fNot = predefined.getNot();
    Set<Rule> rules = this.rootprogram.getRules(this.fAnd);
    this.origrules.put(this.fAnd, rules);
    rules = this.rootprogram.getRules(this.fOr);
    this.origrules.put(this.fOr, rules);
    rules = this.rootprogram.getRules(this.fNot);
    this.origrules.put(this.fNot, rules);

    // Make advanced equal-checks.
    // NEW: now based on types. For this to work, the equal symbols must be named "equal_"+stucture-name
    for(TypeDefinition td : this.rootprogram.getTypeContext().getTypeDefs()) {
        String tdName = td.getDefTerm().getSymbol().getName();
        DefFunctionSymbol eq = this.rootprogram.getPredefFunctionSymbol("equal_"+tdName);
        rules = this.rootprogram.getRules(eq);
        this.origrules.put(eq, rules);
        String name = this.symbnames.getFreshName("x", true);
        AlgebraVariable v = AlgebraVariable.create(VariableSymbol.create(name));
        Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
        args.add(v);
        args.add(v.deepcopy());
        AlgebraTerm left = AlgebraFunctionApplication.create(eq, args);
        AlgebraTerm right = AlgebraFunctionApplication.create(this.cTrue);
        rules = this.rootprogram.getRules(eq);
        rules.add(Rule.create(left, right));
        this.defsrules.put(eq, rules);
    }


    // Make advanced and-function.
    rules = new HashSet<Rule>();
    String name = this.symbnames.getFreshName("x", true);
    AlgebraVariable v = AlgebraVariable.create(VariableSymbol.create(name, this.bool));
    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
    args.add(v);
    args.add(AlgebraFunctionApplication.create(this.cTrue));
    AlgebraTerm left = AlgebraFunctionApplication.create(this.fAnd, args);
    rules.add(Rule.create(left, v.deepcopy()));
    args = new Vector<AlgebraTerm>();
    args.add(AlgebraFunctionApplication.create(this.cTrue));
    args.add(v);
    left = AlgebraFunctionApplication.create(this.fAnd, args);
    rules.add(Rule.create(left, v.deepcopy()));
    args = new Vector<AlgebraTerm>();
    args.add(v);
    args.add(AlgebraFunctionApplication.create(this.cFalse));
    left = AlgebraFunctionApplication.create(this.fAnd, args);
    rules.add(Rule.create(left, AlgebraFunctionApplication.create(this.cFalse)));
    args = new Vector<AlgebraTerm>();
    args.add(AlgebraFunctionApplication.create(this.cFalse));
    args.add(v);
    left = AlgebraFunctionApplication.create(this.fAnd, args);
    rules.add(Rule.create(left, AlgebraFunctionApplication.create(this.cFalse)));
    this.defsrules.put(this.fAnd, rules);
    // Make advanced or-function.
    rules = new HashSet<Rule>();
    args = new Vector<AlgebraTerm>();
    args.add(v);
    args.add(AlgebraFunctionApplication.create(this.cFalse));
    left = AlgebraFunctionApplication.create(this.fOr, args);
    rules.add(Rule.create(left, v.deepcopy()));
    args = new Vector<AlgebraTerm>();
    args.add(AlgebraFunctionApplication.create(this.cFalse));
    args.add(v);
    left = AlgebraFunctionApplication.create(this.fOr, args);
    rules.add(Rule.create(left, v.deepcopy()));
    args = new Vector<AlgebraTerm>();
    args.add(v);
    args.add(AlgebraFunctionApplication.create(this.cTrue));
    left = AlgebraFunctionApplication.create(this.fOr, args);
    rules.add(Rule.create(left, AlgebraFunctionApplication.create(this.cTrue)));
    args = new Vector<AlgebraTerm>();
    args.add(AlgebraFunctionApplication.create(this.cTrue));
    args.add(v);
    left = AlgebraFunctionApplication.create(this.fOr, args);
    rules.add(Rule.create(left, AlgebraFunctionApplication.create(this.cTrue)));
    this.defsrules.put(this.fOr, rules);
    this.computeDependencies();
    // Collect main functions.
    this.mainFunctions = new HashSet<DefFunctionSymbol>();
    itd = this.defsrules.keySet().iterator();
    while (itd.hasNext()) {
        DefFunctionSymbol fsym = itd.next();
        if (fsym.getSignatureClass() == Symbol.MAINSIG) {
        this.mainFunctions.add(fsym);
        }
    }


    this.remainingMRBs = this.getAllMRBs();
    this.terminMRBs = new Vector<Set<DefFunctionSymbol>>();
    this.unknownMRBs = new Vector<Set<DefFunctionSymbol>>();

    Map<DefFunctionSymbol,Set<Rule>> defsrulesCopy = new HashMap<DefFunctionSymbol,Set<Rule>>(this.defsrules);


    //for (Map.Entry<DefFunctionSymbol,Set<Rule>> entry : this.defsrules.entrySet()) {
    for (Map.Entry<DefFunctionSymbol,Set<Rule>> entry : defsrulesCopy.entrySet()) {
        DefFunctionSymbol fsym = entry.getKey();
        rules = entry.getValue();
        this.projdefsrules.put(fsym, this.symbEvalRules(rules));
        }
    }

    /** Computes the next function-set that is to be handled. The
     *  current functions get marked fixed.
     */
    public void nextFunctionSet() {
        if (this.isMRB) {
            this.lastMRBsTerminating = this.lastMRBsTerminating && this.isMRBTerminating;
        }
        this.isMRB = true;
        this.isMRBTerminating = false;
    this.fixedFunctions.addAll(this.defs);
    DefFunctionSymbol fsym = this.getMinimalFunction();
    this.defs = new HashSet<DefFunctionSymbol>();
    if (fsym != null) {
        Iterator it = this.getDependencies(fsym).iterator();
        while (it.hasNext()) {
        fsym = (DefFunctionSymbol)it.next();
        int sig = fsym.getSignatureClass();
        if ((sig == Symbol.MAINSIG || sig == Symbol.DEFAULTSIG) && !this.fixedFunctions.contains(fsym)) {
            this.defs.add(fsym);
        }
        }
    }
        this.forCheck.addAll(this.defs);
    }



    /** Switches to next unhandled MRB
     *  and moves the current MRB into the set of unknown termination behavior
     */
    public void switchToNextMRB() {
        this.switchToNextMRB(false);
    }

    /** Switches to next unhandled MRB
     *  and moves current MRB into the set of terminating MRBs, if curMRBisTerminating is true,
     *  otherwise into the set of unknown termination
     * @param curMRBisTerminating whether the current MRB is terminating or not
     */
    public void switchToNextMRB(boolean curMRBisTerminating) {
        if (!this.defs.isEmpty()) {
            if (curMRBisTerminating) {
                this.terminMRBs.add(this.defs);
            } else {
                this.unknownMRBs.add(this.defs);
            }
        }
        this.nextFunctionSet();
    }


    public boolean noMRBsUnknownTermin() {
        return this.unknownMRBs.isEmpty();
    }


    /**  Computes and returns all mutual recursive blocks (MRBs) of
     *   the program
     * @return A list of MRBs, identified by their defined function symbols
     */
    public List<Set<DefFunctionSymbol>> getAllMRBs() {
        Vector<Set<DefFunctionSymbol>> result = new Vector<Set<DefFunctionSymbol>>();

        this.computeDependencies();

        // make backup of old fixedFunctions
        Set<DefFunctionSymbol> oldFixedFunSyms = this.fixedFunctions;
        this.fixedFunctions = new HashSet<DefFunctionSymbol>();

        DefFunctionSymbol fsym = this.getMinimalFunction();
        while (fsym != null) {
            Set<DefFunctionSymbol> mrbDefs = new HashSet<DefFunctionSymbol>();
            for(DefFunctionSymbol gsym : this.getDependencies(fsym)) {
                int sig = gsym.getSignatureClass();
                if ((sig == Symbol.MAINSIG || sig == Symbol.DEFAULTSIG) && !this.fixedFunctions.contains(gsym)) {
                    mrbDefs.add(gsym);
                }
            }
            result.add(mrbDefs);
            this.fixedFunctions.addAll(mrbDefs);
            fsym = this.getMinimalFunction();
        }

        // restore old fixedFunctions
        this.fixedFunctions = oldFixedFunSyms;

        return result;
    }


    public Set<DefFunctionSymbol> getCurrentMRB() {
        Set<DefFunctionSymbol> mrbDefs = new HashSet<DefFunctionSymbol>(this.defs);

        Iterator<DefFunctionSymbol> defs_it = mrbDefs.iterator();
        while(defs_it.hasNext()) {
            DefFunctionSymbol gsym = defs_it.next();
            int sig = gsym.getSignatureClass();
            if ( (sig == Symbol.MAINSIG || sig == Symbol.DEFAULTSIG) && !this.fixedFunctions.contains(gsym) ) {
                continue;
            }
            defs_it.remove();
        }

        return mrbDefs;
    }

    public void setMRBTerminating(){
        this.isMRBTerminating = true;
    }

    public boolean allMRBsTerminating(){
        return this.finished() && this.lastMRBsTerminating;
    }
    /** Gets a main-function f such that there is no main-function g
     *  where f depends on g but g does not depend on f.
     */
    protected DefFunctionSymbol getMinimalFunction() {
    Set functions = this.defsrules.keySet();
    Vector<DefFunctionSymbol> lifo = new Vector<DefFunctionSymbol>();
    Set<DefFunctionSymbol> visited = new HashSet<DefFunctionSymbol>(this.fixedFunctions);
    Iterator it = functions.iterator();
    while (lifo.isEmpty() && it.hasNext()) {
        DefFunctionSymbol gsym = (DefFunctionSymbol)it.next();
        if (gsym.getSignatureClass() == Symbol.MAINSIG && !visited.contains(gsym)) {
        lifo.add(gsym);
        }
    }
    DefFunctionSymbol fsym = null;
    while (!lifo.isEmpty()) {
        DefFunctionSymbol gsym = lifo.remove(lifo.size()-1);//0);
        if (visited.add(gsym)) {
        if (gsym.getSignatureClass() == Symbol.MAINSIG) {
            fsym = gsym;
            lifo.clear();
        }
        Set deps = this.dependencies.get(gsym);
        if (deps != null) {
            lifo.addAll(deps);
        }
        }
    }
    return fsym;
    }

    /** Returns a list of function-symbols in the order of increasing
     *  dependence of other function-symbol. E.g. on the first
     *  function-symbol in the list has the least number of
     *  function-symbols that depend on it. Projections are ignored.
     */
    public Vector<DefFunctionSymbol> getDependenciesOrder() {
        return this.getDependenciesOrder(this.defs);
    }

    public Vector<DefFunctionSymbol> getDependenciesOrder(Set fsyms) {
    Hashtable<DefFunctionSymbol,Integer> deps = new Hashtable<DefFunctionSymbol,Integer>();
    Iterator it = this.defsrules.keySet().iterator();
    while (it.hasNext()) {
        DefFunctionSymbol f = (DefFunctionSymbol)it.next();
        deps.put(f, Integer.valueOf(0));
    }
    it = fsyms.iterator();
    while (it.hasNext()) {
        Iterator it2 = ((Set)this.defsrules.get(it.next())).iterator();
        while (it2.hasNext()) {
        Rule r = (Rule)it2.next();
        DefFunctionSymbol f = (DefFunctionSymbol)r.getLeft().getSymbol();
        //int sig = f.getSignatureClass();
        Set<DefFunctionSymbol> ds1 = r.getRight().getDefFunctionSymbols();
        Iterator it3 = ds1.iterator();
        while (it3.hasNext()) {
            DefFunctionSymbol g = (DefFunctionSymbol)it3.next();
            //sig = g.getSignatureClass();
            if (!f.equals(g)) {
            Integer i = deps.get(g);
                        if (i == null) {
                            i = Integer.valueOf(0);
                        }
            Integer j = Integer.valueOf(i.intValue()+1);
            deps.put(g, j);
            }
        }
        }
    }
    TreeSet<SymbolCount> entrys = new TreeSet<SymbolCount>();
    it = deps.entrySet().iterator();
    while (it.hasNext()) {
        Map.Entry entry = (Map.Entry)it.next();
        DefFunctionSymbol fsym = (DefFunctionSymbol)entry.getKey();
        if (fsyms.contains(fsym)) {
        entrys.add(new SymbolCount(fsym, (Integer)entry.getValue()));
        }
    }
    Vector<DefFunctionSymbol> depsorder = new Vector<DefFunctionSymbol>();
    for (SymbolCount sc : entrys) {
        Object o = sc.f;
        if (!this.projections.contains(o)) {
        depsorder.add((DefFunctionSymbol) o);
        }
    }
    return depsorder;
    }

    public void computeDependencies() {
    this.dependencies = new Hashtable<DefFunctionSymbol,Set<DefFunctionSymbol>>();
    Iterator it = this.defsrules.keySet().iterator();
    while (it.hasNext()) {
        DefFunctionSymbol f = (DefFunctionSymbol)it.next();
        this.dependencies.put(f, this.computeDependencies(f));
    }
    }

    public Set<DefFunctionSymbol> computeDependencies(DefFunctionSymbol fsym) {
    Set<DefFunctionSymbol> ds = new HashSet<DefFunctionSymbol>();
    Iterator r_it = ((Set)this.defsrules.get(fsym)).iterator();
    while (r_it.hasNext()) {
        Rule r = (Rule)r_it.next();
        ds.addAll(r.getRight().getDefFunctionSymbols());
        Iterator c_it = r.getConds().iterator();
        while (c_it.hasNext()) {
        Rule cond = (Rule)c_it.next();
        ds.addAll(cond.getLeft().getDefFunctionSymbols());
        }
    }
    return ds;
    }

    /* Do I realy have to make an own class just to get this list sorted?
     */
    protected class SymbolCount implements Comparable<SymbolCount> {

    public DefFunctionSymbol f;
    public Integer count;

    public SymbolCount(DefFunctionSymbol sym, Integer c) {
        this.f = sym;
        this.count = c;
    }

    @Override
    public int compareTo(SymbolCount o) {
        int c = this.count.compareTo(o.count);
        if (c != 0) {
        return c;
        }
        return this.f.getName().compareTo(o.f.getName());
    }
    }

    /** Returns true iff f is directly recursive. To give a proper answer
     *  this function requires that the dependencies is up to date, e.g.
     *  it is necessary that computeDependencies has been called.
     */
    public boolean isDirectlyRecursive(DefFunctionSymbol f) {
    return (this.dependencies.get(f)).contains(f);
    }

    /** Returns true iff f is mutually recursive. To give a proper answer
     *  this function requires that the dependencies is up to date, e.g.
     *  it is necessary that computeDependencies has been called.
     *  Here a diretly recursive function is mutually recursive.
     */
    public boolean isMutuallyRecursive(DefFunctionSymbol f) {
    Set<SyntacticFunctionSymbol> visited = new HashSet<SyntacticFunctionSymbol>();
    Vector<SyntacticFunctionSymbol> fifo = new Vector<SyntacticFunctionSymbol>();
    fifo.add((SyntacticFunctionSymbol)this.dependencies.get(f));
    while (!fifo.isEmpty()) {
        DefFunctionSymbol g = (DefFunctionSymbol)fifo.remove(0);
        if (g.equals(f)) {
        return true;
        }
        visited.add(g);
        Iterator it = (this.dependencies.get(g)).iterator();
        while (it.hasNext()) {
        DefFunctionSymbol fn = (DefFunctionSymbol)it.next();
        if (!this.projections.contains(fn) && !visited.contains(fn)) {
            fifo.add(fn);
        }
        }
    }
    return false;
    }

    /** Return true iff h directly depends of f.
     */
    public boolean directlyDependsOn(DefFunctionSymbol h, DefFunctionSymbol f) {
    if (this.projections.contains(h)) {
        return false;
    }
    Set deps = this.dependencies.get(h);
    return deps != null && deps.contains(f);
    }

    /** Return true iff h depends of f.
     */
    public boolean dependsOn(DefFunctionSymbol h, DefFunctionSymbol f) {
    if (this.projections.contains(h)) {
        return false;
    }
    Set<SyntacticFunctionSymbol> visited = new HashSet<SyntacticFunctionSymbol>();
    Vector<SyntacticFunctionSymbol> fifo = new Vector<SyntacticFunctionSymbol>();
    fifo.add(h);
    while (!fifo.isEmpty()) {
        DefFunctionSymbol g = (DefFunctionSymbol)fifo.remove(0);
        if (g.equals(f)) {
        return true;
        }
        visited.add(g);
        Iterator it = (this.dependencies.get(g)).iterator();
        while (it.hasNext()) {
        DefFunctionSymbol fn = (DefFunctionSymbol)it.next();
        if (!this.projections.contains(fn) && !visited.contains(fn)) {
            fifo.add(fn);
        }
        }
    }
    return false;
    }

    /** Returns true iff a function symbol in t occurs that is dependent
     *  on fsym.
     */
    public boolean gotDependencies(AlgebraTerm t, DefFunctionSymbol fsym) {
    Iterator g_it = t.getDefFunctionSymbols().iterator();
    while (g_it.hasNext()) {
        DefFunctionSymbol gsym = (DefFunctionSymbol)g_it.next();
        if (this.dependsOn(gsym, fsym)) {
        return true;
        }
    }
    return false;
    }

    public boolean gotDependencies(List<AlgebraTerm> ts, DefFunctionSymbol fsym) {
    Iterator it = ts.iterator();
    while (it.hasNext()) {
        AlgebraTerm t = (AlgebraTerm)it.next();
        Iterator g_it = t.getDefFunctionSymbols().iterator();
        while (g_it.hasNext()) {
        DefFunctionSymbol gsym = (DefFunctionSymbol)g_it.next();
        if (this.dependsOn(gsym, fsym)) {
            return true;
        }
        }
    }
    return false;
    }

    public boolean greater_dep(DefFunctionSymbol h, DefFunctionSymbol f) {
    return this.dependsOn(h,f) && !this.dependsOn(f,h);
    }

    /** returns a set of function-symbols the function f is dependent on.
     */
    public Set<DefFunctionSymbol> getDependencies(DefFunctionSymbol f) {
    HashSet<DefFunctionSymbol> fs = new HashSet<DefFunctionSymbol>();
    fs.add(f);
    return this.getDependencies(fs);
    }

    /** returns a set of function-symbols the functions in fs are dependent on.
     */
    public Set<DefFunctionSymbol> getDependencies(Set<DefFunctionSymbol> fs) {
    Set<DefFunctionSymbol> visited = new HashSet<DefFunctionSymbol>();
    Vector<DefFunctionSymbol> fifo = new Vector<DefFunctionSymbol>(fs);
    while (!fifo.isEmpty()) {
        DefFunctionSymbol g = fifo.remove(0);
        visited.add(g);
        Set deps = this.dependencies.get(g);
        if (deps != null) {
        Iterator it = deps.iterator();
        while (it.hasNext()) {
            DefFunctionSymbol fn = (DefFunctionSymbol)it.next();
            if (!this.projections.contains(fn) && visited.add(fn)) {
            fifo.add(fn);
            }
        }
        }
    }
    return visited;
    }

    /* Accessors */

    public Set<Rule> getRules() {
    return this.getRules(this.defs);
    }

    public Set<Rule> getRules(Set< ? extends SyntacticFunctionSymbol> fsyms) {
    Set<Rule> rules = new HashSet<Rule>();
    Iterator it = fsyms.iterator();
    while (it.hasNext()) {
        rules.addAll(this.defsrules.get(it.next()));
    }
    return rules;
    }

    public Set<Rule> getCurrentRules() {
    return this.getRules(this.getDependencies(this.defs));
    }

    public Set<DefFunctionSymbol> getMainFunctions(){
    Set<DefFunctionSymbol> mainFunctions = new HashSet<DefFunctionSymbol>();
    Iterator it = this.defsrules.keySet().iterator();
    while (it.hasNext()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)it.next();
        if (fsym.getSignatureClass() == Symbol.MAINSIG) {
        mainFunctions.add(fsym);
        }
    }
        return mainFunctions;
    }

    public Set<Rule> getCurrentMRBRules() {
    return this.getRules(this.getDependencies(this.getDefMainFunctions()));
    }

    public Set<DefFunctionSymbol> getDefMainFunctions(){
    Set<DefFunctionSymbol> mainFunctions = new HashSet<DefFunctionSymbol>();
    Iterator it = this.defs.iterator();
    while (it.hasNext()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)it.next();
        if (fsym.getSignatureClass() == Symbol.MAINSIG) {
        mainFunctions.add(fsym);
        }
    }
        return mainFunctions;
    }

    public Set<Rule> getAllRules() {
    Set<DefFunctionSymbol> mainFunctions = this.getMainFunctions();
    Set<Rule> rules = new HashSet<Rule>();
    Set<DefFunctionSymbol> usedFunctions = new HashSet<DefFunctionSymbol>();
    Iterator it = this.getDependencies(mainFunctions).iterator();
    while (it.hasNext()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)it.next();
        Set defrules = this.origrules.get(fsym);
        if (defrules == null) {
        defrules = this.defsrules.get(fsym);
        }
        rules.addAll(defrules);
        Iterator it2 = defrules.iterator();
        while (it2.hasNext()) {
        Rule rule = (Rule)it2.next();
        usedFunctions.addAll(rule.getRight().getDefFunctionSymbols());
        Iterator it3 = rule.getConds().iterator();
        while (it3.hasNext()) {
            Rule cond = (Rule)it3.next();
            usedFunctions.addAll(cond.getLeft().getDefFunctionSymbols());
        }
        }
    }
    it = this.projections.values().iterator();
    while (it.hasNext()) {
        DefFunctionSymbol proj = (DefFunctionSymbol)it.next();
        if (usedFunctions.contains(proj)) {
        rules.addAll(this.defsrules.get(proj));
        }
    }
    return rules;
    }

    public Program makeProgram() {
    Set<Rule> rules = this.getAllRules();
    Program prog = Program.create(rules, this.program,  AbstractProgram.SIMPLIFIED);
        prog.setStrategy(Program.INNERMOST);
    if (prog.isConditional()) {
        return prog.transformConditional();
    }
    return prog;
    }

    public String export(Export_Util o){
    StringBuffer out = new StringBuffer();
        Vector<Rule> allRules = new Vector<Rule>();
        Vector<Rule> currentRules = new Vector<Rule>();
        Vector<DefFunctionSymbol> order = this.getDependenciesOrder(this.getDependencies(this.getMainFunctions()));
        HashSet<DefFunctionSymbol> cdefs = new HashSet<DefFunctionSymbol>(this.defs);
        for (DefFunctionSymbol fsym : order){
            Set<Rule> fRules = this.defsrules.get(fsym);
            if (this.defs.contains(fsym)){
                currentRules.addAll(fRules);
            } else {
                allRules.addAll(fRules);
            }
            cdefs.remove(fsym);
        }
        for (DefFunctionSymbol fsym : cdefs){
            Set<Rule> fRules = this.defsrules.get(fsym);
            allRules.addAll(fRules);
        }
        if (!currentRules.isEmpty()){
           out.append("<BR>");
           out.append("Current Mutual Recursive Block:");
           out.append("<BR>");
           out.append(o.set(currentRules, Export_Util.RULES));
           out.append("<BR>");
           out.append("Rules:");
           out.append("<BR>");
        }
        out.append(o.set(allRules, Export_Util.RULES));
        return out.toString();
    }

    public String toHTML(){
    return this.export(new HTML_Util());
    }

    public String toLaTeX(){
    return this.export(new LaTeX_Util());
    }

    public String toPLAIN() {
        return this.export(new PLAIN_Util());
    }

    public int getSize(){
        return this.defsrules.entrySet().size();
    }

    @Override
    public String toString() {
    StringBuffer out = new StringBuffer();
    Iterator it = (new Vector(this.defs)).iterator();
    while (it.hasNext()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)it.next();
        out.append("  "+fsym.getName()+"\n");
        int sig = fsym.getSignatureClass();
        if (sig == Symbol.MAINSIG || sig == Symbol.DEFAULTSIG) {
        Iterator r_it = ((Set)this.defsrules.get(fsym)).iterator();
        while (r_it.hasNext()) {
            Rule rule = (Rule)r_it.next();
            out.append(rule.toString()+"\n");
        }
        }
    }
    return out.toString();
    }


    /* Helpers */

    /** Returns a bitfield where the nth bit is set iff the the nth argument
     *  of fsym is not changed (in any recursive call).
     */
    public BigInteger getUnchangedPositions(DefFunctionSymbol fsym) {
    BigInteger unchanged = BigInteger.ZERO.setBit(fsym.getArity()).subtract(BigInteger.ONE);
    Iterator it = ((Set)this.defsrules.get(fsym)).iterator();
    while (it.hasNext()) {
        Rule r = (Rule)it.next();
        List<AlgebraTerm> args = r.getLeft().getArguments();
        Iterator t_it = r.getRight().getAllSubterms().iterator();
        while (t_it.hasNext()) {
        AlgebraTerm t = (AlgebraTerm)t_it.next();
        if (fsym.equals(t.getSymbol())) {
            Iterator a_it1 = args.iterator();
            Iterator a_it2 = t.getArguments().iterator();
            int i = 0;
            while (a_it1.hasNext()) {
            AlgebraTerm arg1 = (AlgebraTerm)a_it1.next();
            AlgebraTerm arg2 = (AlgebraTerm)a_it2.next();
            if (!arg1.equals(arg2)) {
                unchanged = unchanged.clearBit(i);
            }
            i++;
            }
        }
        }
    }
    return unchanged;
    }

    /** Returns a bitfield where the nth bit is set iff the the nth argument
     *  of fsym is only matched against variables. */
    public BigInteger getPositionsWithoutMatching(DefFunctionSymbol fsym) {
    BigInteger positions = BigInteger.ZERO.setBit(fsym.getArity()).subtract(BigInteger.ONE);
    Iterator it = ((Set)this.defsrules.get(fsym)).iterator();
    while (it.hasNext()) {
        Rule r = (Rule)it.next();
        int i = 0;
        Iterator a_it = r.getLeft().getArguments().iterator();
        while (a_it.hasNext()) {
        if (!((AlgebraTerm)a_it.next()).isVariable()) {
            positions = positions.clearBit(i);
        }
        i++;
        }
    }
    return positions;
    }

    /** Gets a list of selectors belonging to the constructor csym,
     *  puts them with their rules into this.defsrules and returns
     *  the selectorlist.
     */
    protected List<DefFunctionSymbol> getSelectors(ConstructorSymbol csym) {
    List<DefFunctionSymbol> selectors = csym.getSelectors();
    Iterator it = selectors.iterator();
    while (it.hasNext()) {
        DefFunctionSymbol fsym = (DefFunctionSymbol)it.next();
        if (this.defsrules.get(fsym) == null) {
        Set<Rule> frules = this.rootprogram.getRules(fsym);
        this.defsrules.put(fsym, frules);

        Type selType = this.rootprogram.getTypeContext().getSingleTypeOf(fsym);

        this.typeContext.setSingleTypeOf(fsym, selType);

        this.updateSymbol(fsym, frules);
        }
    }
    return selectors;
    }

    /** Trys to get the defining funcition with name name and puts the
     *  rules into this.defsrules if neccessary.
     *  The types are taken from rootprogram.getTypeContext()
     */
    protected DefFunctionSymbol getDefFunctionSymbol(String name) {
    DefFunctionSymbol fsym = this.rootprogram.getDefFunctionSymbol(name);
    if (fsym == null) {
        fsym = this.rootprogram.getPredefFunctionSymbol(name);
    }
    if (fsym != null) {
        if (this.defsrules.get(fsym) == null) {
        Set<Rule> frules = this.rootprogram.getRules(fsym);
        this.defsrules.put(fsym, frules);
        this.updateSymbol(fsym, frules);
        Type fsymType = this.rootprogram.getTypeContext().getSingleTypeOf(fsym);

        this.typeContext.setSingleTypeOf(fsym, fsymType);
        }
    }
    return fsym;
    }

    protected void activateFunction(DefFunctionSymbol fsym) {
    if (this.defsrules.get(fsym) == null) {
        Set<Rule> rules = this.rootprogram.getRules(fsym);
        this.defsrules.put(fsym, rules);
        this.defs.add(fsym);
        Type fsymType = this.rootprogram.getTypeContext().getSingleTypeOf(fsym);

        this.typeContext.setSingleTypeOf(fsym, fsymType);
        this.updateSymbol(fsym, rules);
    }
    }

    /** Replaces every occurence of fsym with gsym.
     */
    public static AlgebraTerm replace_f_with_g(AlgebraTerm term, SyntacticFunctionSymbol fsym, SyntacticFunctionSymbol gsym) {
    if (term.isVariable()) {
        return term;
    }
    SyntacticFunctionSymbol sym = (SyntacticFunctionSymbol)term.getSymbol();
    if (fsym.equals(sym)) {
        sym = gsym;
    }
    Vector<AlgebraTerm> newargs = new Vector<AlgebraTerm>();
    Iterator it = term.getArguments().iterator();
    while (it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)it.next();
        newargs.add(SimplifierObligation.replace_f_with_g(arg, fsym, gsym));
    }
    return AlgebraFunctionApplication.create(sym, newargs);
    }

    public static Pair<SyntacticFunctionSymbol,Integer> createLiteral(SyntacticFunctionSymbol fsym, int pos) {
        return new Pair<SyntacticFunctionSymbol,Integer>(fsym, Integer.valueOf(pos));
    }

    public static boolean isTotal(Symbol sym) {
    if (sym instanceof VariableSymbol || sym instanceof ConstructorSymbol) {
        return true;
    }
    return ((DefFunctionSymbol)sym).getTermination();
    }

    public String getAVariableName(int i) {
    return this.symbnames.getFreshName("x_"+i, true);
    }

    public static void setArgNeeded(Hashtable afs, SyntacticFunctionSymbol sym, int pos) {
    BigInteger bits = (BigInteger)afs.get(sym);
    if (bits == null) {
        return;
    }
    BigInteger newbits;
    newbits = bits.setBit(pos);
    afs.put(sym, newbits);
    }


    /** @deprecated
     */
    @Deprecated
    public DefFunctionSymbol getEqualFunctionSort(Sort sort) {
    String name = "equal_"+sort.getName();
    DefFunctionSymbol eqsym = this.rootprogram.getDefFunctionSymbol(name);
    if (eqsym == null) {
        eqsym = this.rootprogram.getPredefFunctionSymbol(name);
        if (eqsym == null) {
        return null;
        }
    }
    if (this.defs.add(eqsym)) {
        Set<Rule> defrules = this.rootprogram.getRules(eqsym);

        Type eqsymType = this.rootprogram.getTypeContext().getSingleTypeOf(eqsym);

        this.typeContext.setSingleTypeOf(eqsym,eqsymType);

        this.defsrules.put(eqsym, defrules);
        this.updateSymbol(eqsym, defrules);
    }
    return eqsym;
    }


    public DefFunctionSymbol getEqualFunction(AlgebraTerm type) {
        String name ="equal_" + type.getSymbol().getName();
        DefFunctionSymbol eqsym = this.rootprogram.getDefFunctionSymbol(name);
        if (eqsym == null) {
            eqsym = this.rootprogram.getPredefFunctionSymbol(name);
            if (eqsym == null) {
                return null;
            }
        }
        if (this.defs.add(eqsym)) {
            Set<Rule> defrules = this.rootprogram.getRules(eqsym);

            Type eqsymType = this.rootprogram.getTypeContext().getSingleTypeOf(eqsym);
            this.typeContext.setSingleTypeOf(eqsym,eqsymType);

            this.defsrules.put(eqsym, defrules);
            this.updateSymbol(eqsym, defrules);
        }
        return eqsym;
    }

    /** Checks whether a variable v occurs in term in an argument of a
     *  function that is dependent on fsym.
     */
    public boolean occursInDependentFunctions(AlgebraVariable v, DefFunctionSymbol fsym, AlgebraTerm term) {
    Vector fifo = new Vector();
    fifo.add(term);
    while (!fifo.isEmpty()) {
        AlgebraTerm t = (AlgebraTerm)fifo.remove(0);
        if (t.isVariable()) {
        continue;
        }
        SyntacticFunctionSymbol sym = (SyntacticFunctionSymbol)term.getSymbol();
        if (sym instanceof DefFunctionSymbol && this.dependsOn((DefFunctionSymbol)sym, fsym)) {
        if (t.getVars().contains(v)) {
            return true;
        }
        }
        fifo.addAll(t.getArguments());
    }
    return false;
    }

    /** Transforms the given rules into a set of rules where the
     *  lhs is a function-application where all arguments are
     *  variables. Matchings are moved to conditons.
     */
    public Set<Rule> moveMatchingToCondition(Set<Rule> rules) {
    Vector<Rule> defrules = new Vector<Rule>(rules);
    Set<Rule> newdefrules = new HashSet<Rule>();
    while (!defrules.isEmpty()) {
        Rule r1 = defrules.remove(0);
        Vector<Rule> rulesubset = new Vector<Rule>();
        rulesubset.add(r1);
        Iterator<Rule> it = defrules.iterator();
        while (it.hasNext()) {
        Rule r2 = it.next();
        if (r2.getLeft().equals(r1.getLeft())) {
            it.remove();
            rulesubset.add(r2);
        }
        }
        this.moveMatchingToCondition(rulesubset, newdefrules);
    }
    return newdefrules;
    }

    protected void moveMatchingToCondition(Vector<Rule> rulesubset, Set<Rule> newdefrules) {
    Iterator it = rulesubset.iterator();
    Rule rule = (Rule)it.next();
    AlgebraTerm left = rule.getLeft();
    DefFunctionSymbol fsym = (DefFunctionSymbol)left.getSymbol();
    List<Rule> newconds = new Vector<Rule>();
    List<AlgebraTerm> newargs = new Vector<AlgebraTerm>();
    int i = 0;
    Iterator arg_it = left.getArguments().iterator();
    while (arg_it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)arg_it.next();
        if (!arg.isVariable()) {
        String name = this.symbnames.getFreshName("m_"+(++i), false);
        AlgebraVariable v = AlgebraVariable.create(VariableSymbol.create(name, arg.getSymbol().getSort()));
        newconds.add(Rule.create(v,  arg));
        newargs.add(v.deepcopy());
        }
        else {
        newargs.add(arg);
        }
    }
    if (newconds.isEmpty()) {
        newdefrules.addAll(rulesubset);
    }
    else {
        left = AlgebraFunctionApplication.create(fsym, newargs);
        it = rulesubset.iterator();
        while (it.hasNext()) {
        rule = (Rule)it.next();
        List<Rule> conds = new Vector<Rule>(newconds);
        conds.addAll(rule.getConds());
        newdefrules.add(Rule.create(conds, left.deepcopy(), rule.getRight()));
        }
    }
    }

    public boolean finished() {
    return this.defs.isEmpty();
    }

    public Set<DefFunctionSymbol> getCurrentDefs() {
    //return this.getDependencies(this.mainFunctions); // Haselbach potential bug thesis 113
    return this.getDependencies(this.defs); // my idea
    }

    /** Deletes a function and cleans up. */
    public void deleteFunction(DefFunctionSymbol fsym) {
    this.defsrules.remove(fsym);
    this.symbnames.freeName(fsym.getName());
    this.defs.remove(fsym);
    this.projdefsrules.remove(fsym);
    if (this.typeContext.getSingleTypeOf(fsym) != null) {
        this.typeContext.removeTypesOf(fsym);
    }
    }

    public Hashtable translateFunction(DefFunctionSymbol fsym, Set<Rule> rules) {
    Vector<Rule> defrules = new Vector<Rule>(rules);
    Hashtable transrules = new Hashtable();
    String name = "if_"+fsym.getName();
    Set<Rule> trules = new HashSet<Rule>();
    while (!defrules.isEmpty()) {
        Rule r1 = defrules.remove(0);
        AlgebraTerm left = r1.getLeft();
        Vector<Rule> rulesubset = new Vector<Rule>();
        rulesubset.add(r1);
        Iterator<Rule> it = defrules.iterator();
        while (it.hasNext()) {
        Rule r2 = it.next();
        if (r2.getLeft().equals(r1.getLeft())) {
            it.remove();
            rulesubset.add(r2);
        }
        }
        Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
        Vector<AlgebraTerm> argsTypes = new Vector<AlgebraTerm>();

        // TODO removal of sorts
        Vector<Sort> sorts = new Vector<Sort>();

        Iterator arg_it = left.getArguments().iterator();
        AlgebraTerm leftTypeM = this.typeContext.getSingleTypeOf(left.getSymbol()).getTypeMatrix();
        Iterator<AlgebraTerm> it_argType = TypeTools.getFunctionArgs(leftTypeM).iterator();
        while (arg_it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)arg_it.next();
        AlgebraTerm argType = it_argType.next();
        Iterator v_it = arg.getVars().iterator();
        while (v_it.hasNext()) {
            AlgebraVariable v = (AlgebraVariable)v_it.next();
            args.add(v);
            argsTypes.add(SimplifierTools.getTypeOfVariableInTerm((VariableSymbol)v.getSymbol(),left,this.typeContext));

            // TODO removal of sorts
            sorts.add(v.getSort());

        }
        }
        AlgebraTerm resultType = TypeTools.getResultTerm(this.typeContext.getSingleTypeOf(fsym).getTypeMatrix());
        AlgebraTerm right = this.translateFunction(name, rulesubset, args, argsTypes, resultType, sorts, fsym.getSort(), transrules, 0);
        trules.add(Rule.create(left,right));
    }
    transrules.put(fsym, trules);
    return transrules;
    }

    protected AlgebraTerm translateFunction(String name, Vector<Rule> rulesubset, Vector<AlgebraTerm> args, Vector<AlgebraTerm> argsTypes, AlgebraTerm ifResultType, Vector<Sort> sorts, Sort sort, Hashtable transrules, int n) {
    Rule r = rulesubset.get(0);
    if (r.getConds().size() <= n) {
        Iterator it = rulesubset.iterator();
        return ((Rule)it.next()).getRight();
    }
    else {
        r = rulesubset.get(0);
        Vector<AlgebraTerm> ifargs = new Vector<AlgebraTerm>(args);
        ifargs.add(r.getConds().get(n).getLeft());

        // TODO removal of sorts
        Vector<Sort> ifsorts = new Vector<Sort>(sorts);
        ifsorts.add(r.getLeft().getSort()); // potential bug: shouldn't this be r.getConds().get(n).getLeft().getSort()? --matraf

        Vector<AlgebraTerm> ifargsTypes = new Vector<AlgebraTerm>(argsTypes);
        AlgebraTerm rLeftType = TypeTools.getResultTerm(this.typeContext.getSingleTypeOf(r.getLeft().getSymbol()).getTypeMatrix());
        ifargsTypes.add(rLeftType);  // same potential bug here, is even more of a problem since getLeft() of a condition might be a variable --matraf

        String ifname = this.symbnames.getFreshName(name, false);
        DefFunctionSymbol ifsym = DefFunctionSymbol.create(ifname, ifsorts, sort);
        this.typeContext.setSingleTypeOf(ifsym, new Type(TypeTools.function(ifargsTypes, ifResultType)));
        AlgebraTerm result = AlgebraFunctionApplication.create(ifsym, ifargs);
        Set<Rule> ifrules = new HashSet<Rule>();
        while (!rulesubset.isEmpty()) {
            Rule r1 = rulesubset.remove(0);
            Rule cond1 = r1.getConds().get(n);
            Vector<Rule> equivCondsRules = new Vector<Rule>();
            equivCondsRules.add(r1);
            Iterator<Rule> it = rulesubset.iterator();
            while (it.hasNext()) {
                Rule r2 = it.next();
                Rule cond2 = r2.getConds().get(n);
                if (cond1.equals(cond2)) {
                    it.remove();
                    equivCondsRules.add(r2);
                }
            }
            ifargs = new Vector<AlgebraTerm>(args);
            ifargs.add(cond1.getRight());
            AlgebraTerm left = AlgebraFunctionApplication.create(ifsym, ifargs);
            ifargs = new Vector<AlgebraTerm>(args);
            ifargsTypes = new Vector<AlgebraTerm>(argsTypes);

            // TODO removal of sorts
            ifsorts = new Vector<Sort>(sorts);

            Iterator v_it = cond1.getRight().getVars().iterator();
            while (v_it.hasNext()) {
                AlgebraVariable v = (AlgebraVariable)v_it.next();
                ifargs.add(v);

                // PROBLEM: The right side of a Condition might be a variable itself
                Set<VariableSymbol> vars = new LinkedHashSet<VariableSymbol>();
                vars.add((VariableSymbol)v.getSymbol());
                AlgebraTerm vType = SimplifierTools.getTypeOfVariables(vars, r1, this.typeContext);
                ifargsTypes.add(vType);

                // TODO removal of sorts
                ifsorts.add(v.getSort());

            }
            AlgebraTerm right = this.translateFunction(name, equivCondsRules, ifargs, ifargsTypes, ifResultType, ifsorts, sort, transrules, n+1);
            ifrules.add(Rule.create(left, right));
        }
        transrules.put(ifsym, ifrules);
        return result;
    }
    }

    protected Set<Rule> symbEvalRules(Set<Rule> rules) {
        Set<Rule> serules = new HashSet<Rule>();
        Iterator r_it = rules.iterator();
        while (r_it.hasNext()) {
            Rule r = (Rule)r_it.next();
            Vector<AlgebraTerm> projections = new Vector<AlgebraTerm>(r.getLeft().getArguments());

            SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol) r.getLeft().getSymbol();
            AlgebraTerm fsymTypeM = this.typeContext.getSingleTypeOf(fsym).getTypeMatrix();
            AlgebraTerm resultType = TypeTools.getResultTerm(fsymTypeM);
            List<AlgebraTerm> projArgsTypes = new Vector<AlgebraTerm>(TypeTools.getFunctionArgs(fsymTypeM));

            Vector<Rule> newconds = new Vector<Rule>();
            Iterator c_it = r.getConds().iterator();
            while (c_it.hasNext()) {
                Rule cond = (Rule)c_it.next();
                Rule newcond = Rule.create(cond.getLeft(), cond.getRight());
                newconds.add(newcond);
                projections.add(cond.getRight());

                AlgebraTerm condRightTypeM = null;
                if (cond.getRight().isVariable()) {
                    if (!cond.getLeft().isVariable()) {
                        condRightTypeM = this.typeContext.getSingleTypeOf(cond.getLeft().getSymbol()).getTypeMatrix();
                    }
                    else {
                        Set<VariableSymbol> vars = new HashSet<VariableSymbol>();
                        vars.add((VariableSymbol)cond.getLeft().getSymbol());
                        vars.add((VariableSymbol)cond.getRight().getSymbol());
                        condRightTypeM = SimplifierTools.getTypeOfVariables(vars, r, this.typeContext);
                    }
                }
                else {
                    condRightTypeM = this.typeContext.getSingleTypeOf(cond.getRight().getSymbol()).getTypeMatrix();
                }

                projArgsTypes.add(TypeTools.getResultTerm(condRightTypeM));
            }

            AlgebraTerm newrightTyped = this.makeProjectionTyped(r.getRight(),resultType, projections, projArgsTypes);

            serules.add(Rule.create(newconds, r.getLeft(), newrightTyped));
        }
        return serules;
    }

    /** Creates the projection-arguments.
     *  @param ft The term that is the first argument (and thus the result)
     *    of the projection.
     *  @param args The remaining arguments.
     *  @return The projection-term.
     *  @deprecated
     */
    @Deprecated
    public AlgebraTerm makeProjectionSort(AlgebraTerm ft, List<AlgebraTerm> args) {
    if (args.isEmpty()) {
        return ft;
    }
    Vector<Sort> sorts = new Vector<Sort>();
    Vector<AlgebraTerm> terms = new Vector<AlgebraTerm>();
    // A (hash)set of subterms would be more efficient.
    List<AlgebraTerm> subterms = ft.getAllSubterms();

    sorts.add(ft.getSymbol().getSort());

    terms.add(ft);
    Iterator it = args.iterator();
    while (it.hasNext()) {
        AlgebraTerm t = (AlgebraTerm)it.next();
        if (!subterms.contains(t)) {
        sorts.add(t.getSymbol().getSort());
        terms.add(t);
        }
    }
    try {
        DefFunctionSymbol proj = this.getProjectionSorts(sorts);
        return AlgebraFunctionApplication.create(proj, terms);
    }
    catch (Exception e) { }
    return null;
    }


    /** Creates a projection <code>proj(ft, args)</code>
     *
     * @param ft First argument (and result) of the projection
     * @param ftType Return type of <b>ft</b>
     * @param args Arguments of the projection
     * @param argTypes Types of the arguments
     * @return The projection-term
     */
    public AlgebraTerm makeProjectionTyped(AlgebraTerm ft, AlgebraTerm ftType, List<AlgebraTerm> args, List<AlgebraTerm> argTypes) {
        if (args.isEmpty()) {
            return ft;
        }

        if (args.size() != argTypes.size()) {
            throw new RuntimeException("Number of arguments and number of types of arguments must be equal.");
        }

        Vector<AlgebraTerm> projArgs = new Vector<AlgebraTerm>();

        Vector<AlgebraTerm> projArgTypes = new Vector<AlgebraTerm>();

        HashSet<AlgebraTerm> subterms = new HashSet<AlgebraTerm>();
        for (AlgebraTerm subterm : ft.getAllSubterms()) {
            subterms.add(subterm);
        }

        projArgs.add(ft);
        projArgTypes.add(ftType);

        Iterator<AlgebraTerm> it_argType = argTypes.iterator();
        for(Iterator<AlgebraTerm> it_arg=args.iterator(); it_arg.hasNext(); ) {
            AlgebraTerm arg = it_arg.next();
            AlgebraTerm argType = it_argType.next();
            if (!subterms.contains(arg)) {
                projArgs.add(arg);
                projArgTypes.add(argType);
            }
        }

        try {
            DefFunctionSymbol projTyped = this.getProjectionTyped(projArgTypes);
            return AlgebraFunctionApplication.create(projTyped,projArgs);
        }
        catch (Exception e) {
            return null;
        }
    }



    /** Returns the function-symbol of a function that maps to the
     *  first argument. If necessary this function will be created.
     *  @deprecated
     */
    @Deprecated
    public DefFunctionSymbol getProjectionSorts(Vector<Sort> sorts) throws ProgramException {
    if (sorts.size() == 0) {
        throw new ProgramException("projections must have at least one argument");
    }
    DefFunctionSymbol proj = this.projections.get(sorts);
    if (proj == null) {
        this.projcount++;
        String name = this.symbnames.getFreshName("proj_"+this.projcount, true);
        proj = DefFunctionSymbol.create(name, sorts, sorts.get(0));
        proj.setTermination(true);
        this.setTerminating(proj);
        Vector<AlgebraTerm> tl = new Vector<AlgebraTerm>();
        for (int i=0; i<sorts.size(); i++) {
        VariableSymbol sym = VariableSymbol.create(this.getAVariableName(i), sorts.get(i));
        tl.add(AlgebraVariable.create(sym));
        }
        AlgebraTerm left = AlgebraFunctionApplication.create(proj, tl);
        AlgebraTerm right = AlgebraVariable.create(VariableSymbol.create(this.getAVariableName(0), sorts.get(0)));
        Set<Rule> projrules = new HashSet<Rule>();
        projrules.add(Rule.create(left, right));
        this.projections.put(sorts, proj);
        this.defsrules.put(proj, projrules);
    }
    return proj;
    }


    /** Returns the function-symbol of a function that maps to the first argument.
     *  Creates such a function if necessary.
     *
     * @param types The types of the arguments of the projection
     * @return A (possibly new) function symbol for the projection
     * @throws ProgramException If there are no types supplied
     */
    public DefFunctionSymbol getProjectionTyped(Vector<AlgebraTerm> types) throws ProgramException {
        if (types.size() == 0) {
            throw new ProgramException("Projections must have at least one typed argument!");
        }

        DefFunctionSymbol proj = this.projectionsTyped.get(types);
        if (proj == null) {
            this.projcount++;
            String name = this.symbnames.getFreshName("proj_"+this.projcount,true);

            // TODO removal of sorts
            // below here it gets dirty
            // Sorts are needed to create the projection
            Vector<Sort> sorts = new Vector<Sort>();

            Iterator<AlgebraTerm> it_type = types.iterator();
            while(it_type.hasNext()) {
                AlgebraTerm type = it_type.next();

                Sort sort = this.program.getSort(type.toString());
                if (aprove.Globals.useAssertions) {
                    assert sort != null : "no sort with name "+type.toString()+" was found!";
                }
                sorts.add(sort);
            }

            // creating the new type (be sure to not do a copy of the Terms in types, otherwise this.projectionsTyped.get() won't work anymore)
            Type type = new Type(TypeTools.function(types,types.get(0)));

            proj = DefFunctionSymbol.create(name, sorts, sorts.get(0));
            proj.setTermination(true);
            this.setTerminating(proj);

            Vector<AlgebraTerm> tl = new Vector<AlgebraTerm>();
            for (int i=0; i<types.size(); i++) {
                VariableSymbol sym = VariableSymbol.create(this.getAVariableName(i), sorts.get(i));
                tl.add(AlgebraVariable.create(sym));
            }

            AlgebraTerm left = AlgebraFunctionApplication.create(proj, tl);
            AlgebraTerm right = AlgebraVariable.create(VariableSymbol.create(this.getAVariableName(0), sorts.get(0)));
            Set<Rule> projrules = new HashSet<Rule>();
            projrules.add(Rule.create(left, right));

            this.projections.put(sorts, proj);

            this.typeContext.setSingleTypeOf(proj, type);

            this.projectionsTyped.put(types, proj);
            this.defsrules.put(proj, projrules);
        }

        return proj;
    }


    public boolean isProjection(Symbol fsym) {
        return this.projectionsTyped.containsValue(fsym);
    }


/*    protected void updateSymbol(DefFunctionSymbol fsym, Set<Rule> newdefrules) {
    this.dependencies.put(fsym, this.computeDependencies(fsym));
        this.projdefsrules.put(fsym, this.symbEvalRules(newdefrules));
    }*/

    public void updateSymbol(DefFunctionSymbol fsym, Set<Rule> newdefrules) {
    this.dependencies.put(fsym, this.computeDependencies(fsym));
    this.projdefsrules.put(fsym, this.symbEvalRules(newdefrules));
    Iterator f_it = this.defsrules.keySet().iterator();
    while (f_it.hasNext()) {
        DefFunctionSymbol gsym = (DefFunctionSymbol)f_it.next();
        if (this.failedJComFuncs.contains(gsym) && this.directlyDependsOn(gsym, fsym)) {
        gsym.resetUnknownJCommutativity();
        this.failedJComFuncs.remove(gsym);
        }
    }
    }


    /** Lifts the given rules. After lifting the lhs has no
     *  constructor-symbols.
     */
    public Set<Rule> liftRules(Set<Rule> rules) {
    Set<Rule> lifted = new HashSet<Rule>();
    Iterator it = rules.iterator();
    while (it.hasNext()) {
        Rule rule = (Rule)it.next();
        Rule lr = this.liftRule(rule);
        lifted.add(lr);
    }
    return lifted;
    }

    /** Lifts the given rule. After lifting the lhs has no
     *  constructor-symbols.
     */
    public Rule liftRule(Rule rule) {
    AlgebraTerm left = rule.getLeft();
    AlgebraTerm right = rule.getRight();
    Hashtable replacements = new Hashtable();
    Vector<AlgebraTerm> newargs = new Vector<AlgebraTerm>();
    int i = 0;
    List<AlgebraTerm> args = left.getArguments();
    Iterator it = args.iterator();
    while (it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)it.next();
        i++;
        if (!arg.isVariable()) {
        String name = this.symbnames.getFreshName("x_"+i, true);
        VariableSymbol vsym = VariableSymbol.create(name, arg.getSymbol().getSort());
        newargs.add(AlgebraVariable.create(vsym));
        AlgebraTerm replacement = AlgebraVariable.create(vsym);
        this.getLiftReplacements(arg, replacements, replacement);
        }
        else {
        newargs.add(arg);
        }
    }
    it = rule.getConds().iterator();
    while (it.hasNext()) {
        Rule cond = (Rule)it.next();
        AlgebraTerm t = cond.getLeft().termReplace(replacements);
        this.getLiftReplacements(cond.getRight(), replacements, t);
    }
    AlgebraTerm newleft = AlgebraFunctionApplication.create((SyntacticFunctionSymbol)left.getSymbol(), newargs);
    AlgebraTerm newright = rule.getRight().termReplace(replacements);
    return Rule.create(newleft, newright);
    }

    /** Lifts the rules and makes sure that all lhs are equal.
     *  I.e. all rules are using the same set of variables.
     *  The order of lifted and conditions of course correspond to each
     *  other. Additionaly it corresponds to the order of rules (if
     *  any, i.e. if rules is a for example a linked hash set).
     */
    public void liftRules(Set<Rule> rules, Vector<Rule> lifted, Vector<AlgebraTerm> conditions) {
    if (rules.isEmpty()) {
        return;
    }
    AlgebraTerm gleft = null;
    Iterator it = rules.iterator();
    while (it.hasNext()) {
        Rule rule = (Rule)it.next();
        Object o[] = this.getLiftedRuleWithCondition(rule);
        Rule lr = (Rule)o[0];
        AlgebraTerm condition = (AlgebraTerm)o[1];
        if (gleft == null) {
        gleft = lr.getLeft();
        conditions.add(condition);
        lifted.add(lr);
        }
        else {
        try {
            AlgebraTerm lleft = lr.getLeft();
            AlgebraTerm lright = lr.getRight();
            AlgebraSubstitution sub = lleft.matches(gleft);
            conditions.add(condition.apply(sub));
            lifted.add(Rule.create(lleft.apply(sub), lright.apply(sub)));
        }
        catch (UnificationException e) { }
        }
    }
    }

    public Object[] getLiftedRuleWithCondition(Rule rule) {
    Vector<AlgebraTerm> rconditions = new Vector<AlgebraTerm>();
    Rule lr = this.liftRule(rule, rconditions);
    AlgebraTerm condition = null;
    if (rconditions.isEmpty()) {
        condition = AlgebraFunctionApplication.create(this.cTrue);
    }
    else {
        Iterator c_it = rconditions.iterator();
        condition = (AlgebraTerm)c_it.next();
        while (c_it.hasNext()) {
        Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
        args.add(condition);
        args.add((AlgebraTerm) c_it.next());
        condition = AlgebraFunctionApplication.create(this.fAnd, args);
        }
    }
    Object o[] = new Object[2];
    o[0] = lr;
    o[1] = condition;
    return o;
    }

    protected Rule liftRule(Rule rule, Vector<AlgebraTerm> conditions) {
    AlgebraTerm left = rule.getLeft();
    AlgebraTerm right = rule.getRight();
    Hashtable replacements = new Hashtable();
    Vector<AlgebraTerm> newargs = new Vector<AlgebraTerm>();
    int i = 0;
    List<AlgebraTerm> args = left.getArguments();
    Iterator it = args.iterator();
    while (it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)it.next();
        i++;
        if (!arg.isVariable()) {
        String name = this.symbnames.getFreshName("x_"+i, true);
        VariableSymbol vsym = VariableSymbol.create(name, arg.getSymbol().getSort());
        newargs.add(AlgebraVariable.create(vsym));
        AlgebraTerm replacement = AlgebraVariable.create(vsym);
        if (!arg.getVars().isEmpty()) {
            this.getLiftReplacements(arg, replacements, replacement, conditions);
        }
        else {
            this.getLiftConditions(arg, replacement, conditions);
        }
        }
        else {
        newargs.add(arg);
        }
    }
    it = rule.getConds().iterator();
    while (it.hasNext()) {
        Rule cond = (Rule)it.next();
        AlgebraTerm t = cond.getLeft().termReplace(replacements);
        this.getLiftReplacements(cond.getRight(), replacements, t, conditions);
    }
    AlgebraTerm newleft = AlgebraFunctionApplication.create((SyntacticFunctionSymbol)left.getSymbol(), newargs);
    AlgebraTerm newright = rule.getRight().termReplace(replacements);
    return Rule.create(newleft, newright);
    }

    /** Computes the replacements that have to be made for term.
     */
    public void getLiftReplacements(AlgebraTerm term, Hashtable replacements, AlgebraTerm replacement) {
    replacements.put(term, replacement);
    if (!term.isVariable()) {
        ConstructorSymbol csym = (ConstructorSymbol)term.getSymbol();
        List<DefFunctionSymbol> selectors = this.getSelectors(csym);
        Iterator a_it = term.getArguments().iterator();
        Iterator s_it = selectors.iterator();
        while (a_it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)a_it.next();
        DefFunctionSymbol sel = (DefFunctionSymbol)s_it.next();
        Vector<AlgebraTerm> selarg = new Vector<AlgebraTerm>();
        selarg.add(replacement.deepcopy());
        AlgebraTerm newreplacement = AlgebraFunctionApplication.create(sel, selarg);
        this.getLiftReplacements(arg, replacements, newreplacement);
        }
    }
    }

    /**
     *  @param term The term that has to be matched.
     *  @param replacement The replacement for this term.
     *  @param conditions This vector collects the conditons.
     *  @param replacements A hashtable that maps constructor terms
     *  to replacement terms.
     */
    public void getLiftReplacements(AlgebraTerm term, Hashtable replacements, AlgebraTerm replacement, Vector<AlgebraTerm> conditions) {
    replacements.put(term, replacement);
    if (!term.isVariable()) {
        ConstructorSymbol csym = (ConstructorSymbol)term.getSymbol();
        DefFunctionSymbol isa = this.getDefFunctionSymbol("isa_"+csym.getName());
        List<AlgebraTerm> args = new Vector<AlgebraTerm>();
        args.add(replacement.deepcopy());
        conditions.add(AlgebraFunctionApplication.create(isa, args));
        List<DefFunctionSymbol> selectors = this.getSelectors(csym);
        Iterator a_it = term.getArguments().iterator();
        Iterator s_it = selectors.iterator();
        while (a_it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)a_it.next();
        DefFunctionSymbol sel = (DefFunctionSymbol)s_it.next();
        Vector<AlgebraTerm> selarg = new Vector<AlgebraTerm>();
        selarg.add(replacement.deepcopy());
        AlgebraTerm newreplacement = AlgebraFunctionApplication.create(sel, selarg);
        this.getLiftReplacements(arg, replacements, newreplacement, conditions);
        }
    }
    }


    /** Creates conditions a term has to fullfill to match a given term.
     *  @param term The term that has to be matched.
     *  @param replacement The replacement for this term.
     *  @param conditions This vector collects the conditons.
     */
    public void getLiftConditions(AlgebraTerm term, AlgebraTerm replacement, Vector<AlgebraTerm> conditions) {
    if (!term.isVariable()) {
        ConstructorSymbol csym = (ConstructorSymbol)term.getSymbol();
        DefFunctionSymbol isa = this.getDefFunctionSymbol("isa_"+csym.getName());
        List<AlgebraTerm> args = new Vector<AlgebraTerm>();
        args.add(replacement.deepcopy());
        conditions.add(AlgebraFunctionApplication.create(isa, args));
        List<DefFunctionSymbol> selectors = this.getSelectors(csym);
        Iterator a_it = term.getArguments().iterator();
        Iterator s_it = selectors.iterator();
        while (a_it.hasNext()) {
        AlgebraTerm arg = (AlgebraTerm)a_it.next();
        DefFunctionSymbol sel = (DefFunctionSymbol)s_it.next();
        Vector<AlgebraTerm> selarg = new Vector<AlgebraTerm>();
        selarg.add(replacement.deepcopy());
        AlgebraTerm newreplacement = AlgebraFunctionApplication.create(sel, selarg);
        this.getLiftConditions(arg, newreplacement, conditions);
        }
    }
    }

    /** Performes a symbolic evaluation of a given term with respect to
     *  a given set of rewrite-rules.
     */
    public AlgebraTerm symbolicEvaluation(AlgebraTerm term, Map rwrules) {
    term.labelTerm(new Hashtable());
    AlgebraTerm rewrite = term;

    AlgebraTerm rwType = null;

    boolean changed = true;
    for (int i=0; changed && (i<SimplifierObligation.RWITERLIMIT); i++) {
        changed = false;

        if (!(rewrite.getSymbol() instanceof VariableSymbol)) {
                rwType = TypeTools.getResultTerm(this.typeContext.getSingleTypeOf(rewrite.getSymbol()).getTypeMatrix());
                rewrite = this.advProjectionTransform(rewrite,rwType);
        }

        AlgebraTerm t = rewrite.limitRewriteStep(SimplifierObligation.RWLABELLIMIT, SimplifierObligation.RWITERLIMIT, SimplifierObligation.RWDEPTHLIMIT, rwrules);
        if (t != null && t.size() < SimplifierObligation.RWSIZELIMIT) {
        rewrite = t;
        changed = true;
        }
    }

    AlgebraTerm t = null;

    if (!(rewrite.getSymbol() instanceof VariableSymbol)) {
        t = this.deleteArguments(this.advProjectionTransform(rewrite,rwType));
    }

    if (t != null) {
        rewrite = t;
            changed = true;
    }
    rewrite.unlabelTerm();
        if (rewrite.equals(term)) {
            return null;
        }
    return rewrite;
    }

    /** Return the rule that one would get by keeping a minimal set
     *  of arguments in the projection. E.g. the first argument is
     *  kept, and the list of removed arguments is the maximal list
     *  such that for every argument in this list its defindeness
     *  follows from the kept arguments.
     *  The check, whether definedness can be concluded is very
     *  simple and can be improved.
     */
    public AlgebraTerm deleteArguments(AlgebraTerm term) {
    boolean changed = false;

    if (!this.isProjection(term.getSymbol())) {
        return null;
    }
    Set<AlgebraTerm> concludeterms = new HashSet<AlgebraTerm>();
    SyntacticFunctionSymbol ps = (SyntacticFunctionSymbol)term.getSymbol();
    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
    Vector<AlgebraTerm> argTypes = new Vector<AlgebraTerm>();
    List<AlgebraTerm> termArgTypes = TypeTools.getFunctionArgs(this.typeContext.getSingleTypeOf(ps).getTypeMatrix());

    Iterator it = term.getArguments().iterator();
    Iterator<AlgebraTerm> it_termArgType = termArgTypes.iterator();
    AlgebraTerm t = (AlgebraTerm)it.next();
    AlgebraTerm tType = it_termArgType.next();
    args.add(t);
    argTypes.add(tType);

    concludeterms.addAll(t.getAllSubterms());
    while (it.hasNext()) {
        t = (AlgebraTerm)it.next();
        tType = it_termArgType.next();

        if (!concludeterms.contains(t)) {
        Symbol fsym = t.getSymbol();
        if (fsym instanceof DefFunctionSymbol) {
            DefFunctionSymbol fdsym = (DefFunctionSymbol)fsym;
            boolean canConclude = false;
            Iterator s_it = concludeterms.iterator();
            while (!canConclude && s_it.hasNext()) {
            AlgebraTerm s = (AlgebraTerm)s_it.next();
            Symbol gsym = s.getSymbol();
            if ((gsym instanceof DefFunctionSymbol) && t.getArguments().equals(s.getArguments())) {
                canConclude = this.sameTerminationBehaviour(fdsym, (DefFunctionSymbol)gsym);
            }
            }
            if (canConclude) {
            changed = true;
            }
            else {
                args.add(t);
                argTypes.add(tType);
                concludeterms.addAll(t.getAllSubterms());
            }
        }
        }
        else {
        changed = true;
        }
    }
    if (changed) {
        t = args.remove(0);
        tType = argTypes.remove(0);

        return this.makeProjectionTyped(t, tType, args, argTypes);
    }
    return null;
    }

    /* Projections (Transformation) */

    public AlgebraTerm advProjectionTransform(AlgebraTerm term, AlgebraTerm resultType) {
    Set<AlgebraTerm> projs = new HashSet<AlgebraTerm>();
    AlgebraTerm p = this.advProjectionTransform(term, projs);
    if (projs.isEmpty()) {
        return p;
    }
    Set<AlgebraTerm> contained = new HashSet<AlgebraTerm>(p.getAllSubterms());
    Vector<AlgebraTerm> newprojs = new Vector<AlgebraTerm>();

    Vector<AlgebraTerm> newprojsTypes = new Vector<AlgebraTerm>();

    Vector<Pair<AlgebraTerm,AlgebraTerm>> fifoTyped = new Vector<Pair<AlgebraTerm,AlgebraTerm>>();
    for(AlgebraTerm proj : projs) {
        Type projType = this.typeContext.getSingleTypeOf(proj.getSymbol());
        AlgebraTerm projResType = null;
        if (projType != null) {
            projResType = TypeTools.getResultTerm(this.typeContext.getSingleTypeOf(proj.getSymbol()).getTypeMatrix());
        }
        fifoTyped.add(new Pair<AlgebraTerm,AlgebraTerm>(proj,projResType));
    }

    while(!fifoTyped.isEmpty()) {
        Pair<AlgebraTerm,AlgebraTerm> pairTermType = fifoTyped.remove(0);
        AlgebraTerm t = pairTermType.x;
        AlgebraTerm tType = pairTermType.y;

        if (!t.isVariable() && !contained.contains(t)) {
            if(SimplifierObligation.isTotal(t.getSymbol())) {
                Iterator<AlgebraTerm> it_arg = t.getArguments().iterator();

                List<AlgebraTerm> argTypes = TypeTools.getFunctionArgs(this.typeContext.getSingleTypeOf(t.getSymbol()).getTypeMatrix());

                Iterator<AlgebraTerm> it_argType = argTypes.iterator();

                while(it_arg.hasNext()) {
                    AlgebraTerm arg = it_arg.next();
                    AlgebraTerm argType = it_argType.next();
                    fifoTyped.add(new Pair<AlgebraTerm,AlgebraTerm>(arg,argType));
                }
            }
            else {
                newprojs.add(t);
                newprojsTypes.add(tType);
                contained.add(t);
            }
        }
    }
    AlgebraTerm pType = resultType;
    return this.makeProjectionTyped(p,pType, newprojs, newprojsTypes);
    }

    public AlgebraTerm advProjectionTransform(AlgebraTerm term, Set<AlgebraTerm> projs) {
    if (term.isVariable()) {
        return term;
    }
    if (this.isProjection(term.getSymbol())) {
        Iterator<AlgebraTerm> it_arg = term.getArguments().iterator();

        AlgebraTerm p = this.advProjectionTransform(it_arg.next(), projs);
        while (it_arg.hasNext()) {
        AlgebraTerm t = this.advProjectionTransform(it_arg.next(), projs);
        projs.add(t);
        }
        return p;
    }
    Hashtable attr = term.getAttributes();
    SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol)term.getSymbol();
    Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
    Iterator<AlgebraTerm> it_arg = term.getArguments().iterator();

    while (it_arg.hasNext()) {
        AlgebraTerm t = this.advProjectionTransform(it_arg.next(), projs);
        args.add(t);
    }
    AlgebraTerm p = AlgebraFunctionApplication.create(fsym, args);
    p.setAttributes(attr);
    return p;
    }


    protected boolean sameTerminationBehaviour(DefFunctionSymbol fsym, DefFunctionSymbol gsym) {
    Set<Rule> frules = this.defsrules.get(fsym);
    Set<Rule> grules = this.defsrules.get(gsym);
    if ( (frules == null) || (grules == null) ) {
        return false; // in this case, nothing can be said, so stay on the safe side and return false
    }
    Iterator it = frules.iterator();
    while (it.hasNext()) {
        Rule frule = (Rule)it.next();
        Rule grule = SimplifierTools.getCorrespondentRule(this.defsrules.get(gsym), frule.getLeft().getArguments(), frule.getConds());
        if (grule == null) {
            return false;
        }
        Rule lfrule = this.liftRule(frule);
        Rule lgrule = this.liftRule(grule);

        // assert that the information stored in this class is correct
        if (Globals.useAssertions) {
            assert !(frule.getRight().isTerminating() ^ this.isTerminating(frule.getRight())) : "different termination information for "+frule.getRight();
            assert !(grule.getRight().isTerminating() ^ this.isTerminating(grule.getRight())) : "different termination information for "+grule.getRight();
        }

        if (frule.getRight().isTerminating()) {
            if (grule.getRight().isTerminating()) {
                continue;
            }
            return false;
        }
        if (grule.getRight().isTerminating()) {
            return false;
        }
        try {
            AlgebraSubstitution sigma = lfrule.getLeft().matches(lgrule.getLeft());
            if (!lfrule.getRight().apply(sigma).equals(lgrule.getRight())) {
                return false;
            }
        }
        catch (UnificationException e) { }
    }
    return true;
    }

    public boolean symbolicEvaluation(DefFunctionSymbol fsym) {
        boolean changed = false;
    Vector<Rule> defrules = new Vector<Rule>(this.defsrules.get(fsym));
    Set<Rule> newdefrules = new HashSet<Rule>();
    while (!defrules.isEmpty()) {
        Rule r1 = defrules.remove(0);
        Vector<Rule> rulesubset = new Vector<Rule>();
        rulesubset.add(r1);
        Iterator<Rule> it = defrules.iterator();
        while (it.hasNext()) {
        Rule r2 = it.next();
        if (r2.getLeft().equals(r1.getLeft())) {
            it.remove();
            rulesubset.add(r2);
        }
        }
        boolean c = this.symbolicEvaluation(rulesubset, newdefrules, 0);
            changed = changed || c; // lazy ||
    }
    this.defsrules.put(fsym, newdefrules);
    this.updateSymbol(fsym, newdefrules);
        return changed;
    }

    /** Perform symbolic evaluation on the rules in rulesubset. The
     *  results are added to newdefrules.
     */
    public boolean symbolicEvaluation(Vector<Rule> rulesubset, Set<Rule> newdefrules, int n) {
        boolean changed = false;
    Rule r = rulesubset.get(0);
    if (r.getConds().size() <= n) {
        // If we are here then all rules in rulesubset have to evaluate
        // the same conditions. So just perform symbolic-evaluation
        // on the rhs. Rulesubset should have size 1.
        Iterator it = rulesubset.iterator();
        while (it.hasNext()) {
        r = (Rule)it.next();
        AlgebraTerm right = r.getRight();
        List<Rule> conds = r.getConds();
        AlgebraTerm newright = this.symbolicEvaluation(right, this.projdefsrules);
        if (newright != null) {
            AlgebraTerm left = r.getLeft();
            r = Rule.create(conds, left, newright);
                    changed = true;
        }
        newdefrules.add(r);
        }
    } else {
        // Here we have to form further subsets of rulesubset by taking one
        // more condition into account.
        while (!rulesubset.isEmpty()) {
        Rule r1 = rulesubset.remove(0);
        Rule cond1 = r1.getConds().get(n);
        Vector<Rule> equivCondsRules = new Vector<Rule>();
        equivCondsRules.add(r1);
        Iterator<Rule> it = rulesubset.iterator();
        while (it.hasNext()) {
            Rule r2 = it.next();
            Rule cond2 = r2.getConds().get(n);
            if (cond1.equals(cond2)) {
            it.remove();
            equivCondsRules.add(r2);
            }
        }
        Vector<Rule> equivCondRules2 = new Vector<Rule>();
        AlgebraTerm condNewLeft = this.symbolicEvaluation(cond1.getLeft(), this.projdefsrules);
                if (condNewLeft == null) {
                    condNewLeft = cond1.getLeft();
                } else {
                    changed = true;
                }
        AlgebraTerm condRight = cond1.getRight();
        if (this.isProjection(condNewLeft.getSymbol())) {
            List<AlgebraTerm> projections = condNewLeft.getArguments();

            // since condNewLeft.getSymbol() is a projection, there is a type for it
            List<AlgebraTerm> projArgsTypes = TypeTools.getFunctionArgs(this.typeContext.getSingleTypeOf(condNewLeft.getSymbol()).getTypeMatrix());
            AlgebraTerm condNewLeftType = projArgsTypes.remove(0);

            condNewLeft = projections.remove(0);
            it = equivCondsRules.iterator();
            while (it.hasNext()) {
            r = it.next();
            List<Rule> newconds = new Vector<Rule>(r.getConds());
            Rule cond = Rule.create(condNewLeft.deepcopy(), condRight.deepcopy());
            newconds.set(n, cond);

            AlgebraTerm newrightTyped = this.makeProjectionTyped(r.getRight(),condNewLeftType, projections,projArgsTypes);

            changed = changed || !projections.isEmpty();
            equivCondRules2.add(Rule.create(newconds, r.getLeft(), newrightTyped));
            }
        }
        else {
            it = equivCondsRules.iterator();
            while (it.hasNext()) {
            r = it.next();
            List<Rule> newconds = new Vector<Rule>(r.getConds());
            Rule cond = Rule.create(condNewLeft.deepcopy(), condRight.deepcopy());
            newconds.set(n, cond);
            equivCondRules2.add(Rule.create(newconds, r.getLeft(), r.getRight()));
            }
        }
        boolean c = this.symbolicEvaluation(equivCondRules2, newdefrules, n+1);
                changed = changed || c;  // lazy ||
        }
    }
        return changed;
    }

   /** lifts the matching of the first condition into the lhs of the rule.
     *  @return true iff transformation was possible.
     */
    public boolean liftMatching(DefFunctionSymbol fsym) {
    boolean changed = false;
    Set<Rule> newrules = new HashSet<Rule>();
    Iterator it = ((Set) this.defsrules.get(fsym)).iterator();
    while (it.hasNext()) {
        Rule rule = (Rule)it.next();
        Rule newrule = SimplifierTools.liftMatching(rule);
        if (newrule == null) {
        newrules.add(rule);
        }
        else {
        changed = true;
        newrules.add(newrule);
        }
    }
    if (changed) {
        this.defsrules.put(fsym, newrules);
        this.updateSymbol(fsym, newrules);
        return true;
    }
    return false;
    }

    /* Condition-Match-Transformation */

    public void conditionMatchTransformation() {
    Iterator it = this.defs.iterator();
    while (it.hasNext()) {
        this.conditionMatchTransformation((DefFunctionSymbol)it.next());
    }
    }

    /** This transformation delets rules where constructors have to match
     *  different constructors in a condition and splits conditions, where
     *  constructors have to match the same constructor. Also, if the rhs
     *  of a condition matches its lhs, then it is eliminated.
     */
    public boolean conditionMatchTransformation(DefFunctionSymbol fsym) {
    //log.log(Level.FINEST, "Simplifier: Performing condition-match-transformation on "+fsym.getName()+".\n");
    Set<Rule> rules = this.defsrules.get(fsym);
    Set<Rule> newrules = new HashSet<Rule>();
    boolean changed = false;
    Iterator r_it = rules.iterator();
    while (r_it.hasNext()) {
        Rule r = (Rule)r_it.next();
        boolean deleteRule = false;
        List<Rule> newconds = new Vector<Rule>();
        AlgebraSubstitution sigma = AlgebraSubstitution.create();
        Vector<AlgebraTerm> projs = new Vector<AlgebraTerm>();

        Vector<AlgebraTerm> projsTypes = new Vector<AlgebraTerm>();

        Iterator c_it = r.getConds().iterator();
        while (c_it.hasNext()) {
        Rule cond = (Rule)c_it.next();
        AlgebraTerm left = cond.getLeft().apply(sigma);
        AlgebraTerm right = cond.getRight();
        try {
            sigma = right.matches(left, sigma);
            projs.add(left);
            if (!left.isVariable()) {
                projsTypes.add(TypeTools.getResultTerm(this.typeContext.getSingleTypeOf(left.getSymbol()).getTypeMatrix()));
            }
            else {
                if (!right.isVariable()) {
                    projsTypes.add(TypeTools.getResultTerm(this.typeContext.getSingleTypeOf(right.getSymbol()).getTypeMatrix()));
                }
                else {
                    Set<VariableSymbol> vars = new LinkedHashSet<VariableSymbol>();
                    vars.add((VariableSymbol)left.getSymbol());
                    vars.add((VariableSymbol)right.getSymbol());
                    AlgebraTerm leftType = SimplifierTools.getTypeOfVariables(vars, r, this.typeContext);

                    projsTypes.add(leftType);
                }
            }
            changed = true;
        }
        catch (UnificationException e) {
            if (!left.isVariable() && !right.isVariable()) {
            SyntacticFunctionSymbol csym = (SyntacticFunctionSymbol)left.getSymbol();
            SyntacticFunctionSymbol dsym = (SyntacticFunctionSymbol)right.getSymbol();
            if ((csym instanceof ConstructorSymbol) && (dsym instanceof ConstructorSymbol)) {
                changed = true;
                if (csym.equals(dsym)) {
                Iterator larg_it = left.getArguments().iterator();
                Iterator rarg_it = right.getArguments().iterator();
                while (larg_it.hasNext()) {
                    AlgebraTerm larg = (AlgebraTerm)larg_it.next();
                    AlgebraTerm rarg = (AlgebraTerm)rarg_it.next();
                    newconds.add(Rule.create(larg, rarg));
                }
                continue;
                } else {
                // This rule is obviously never applicable. Thus, delete it.
                deleteRule = true;
                break;
                }
            }
            }
            newconds.add(Rule.create(left, right));
        }
        }
        if (!deleteRule) {

            // the type of the rhs of r must be the same as for the lhs
            AlgebraTerm rGetLeftTypeM = this.typeContext.getSingleTypeOf(r.getLeft().getSymbol()).getTypeMatrix();
            AlgebraTerm rGetLeftType = TypeTools.getResultTerm(rGetLeftTypeM);

            AlgebraTerm newrightTyped = this.makeProjectionTyped(r.getRight().apply(sigma), rGetLeftType, projs, projsTypes);

            if (aprove.Globals.useAssertions) {
                AlgebraTerm newright = this.makeProjectionSort(r.getRight().apply(sigma), projs);
                assert(newright.equals(newrightTyped)) : "sorted= "+newright+" \n!=\ntyped= "+newrightTyped+"\nsorts: "+((SyntacticFunctionSymbol)newright.getSymbol()).getArgSorts()+" -> "+newright.getSymbol().getSort()+"\ntypes: "+this.typeContext.getSingleTypeOf(newrightTyped.getSymbol());
            }

            newrules.add(Rule.create(newconds, r.getLeft(), newrightTyped));
        }
    }
    if (changed) {
        this.defsrules.put(fsym, newrules);
        this.updateSymbol(fsym, newrules);
        return true;
    }
    return false;
    }

   /** Checks whether the definedness is the same under some condition.
     *  @return True iff definedness is the same.
     *  @param cond The condition under which the definedness is the same.
     *  @param t One term.
     *  @param r Other term.
     */
    public boolean proveDefEquivalenceUnderCondition(AlgebraTerm cond, AlgebraTerm t, AlgebraTerm r) {
    //TODO Use condition.
    if (t == null || r == null) {
        return false;
    }
    Vector<AlgebraTerm> ts = new Vector<AlgebraTerm>();
    ts.add(t);
    Vector<AlgebraTerm> rs = new Vector<AlgebraTerm>();
    rs.add(r);
    return this.defindnessFollows(ts, rs) && this.defindnessFollows(rs, ts);
    }

    /** Checks whether the definedness follows.
     * @return True iff the termination follows.
     * @param rs If these terms terminate, the ts-terms have to terminate, too.
     * @param ts These terms have to terminate when the rs-term terminate.
     */
    public boolean defindnessFollows(List<AlgebraTerm> rs, List<AlgebraTerm> ts) {
    Set<AlgebraTerm> concludeterms = new HashSet<AlgebraTerm>();
    Iterator r_it = rs.iterator();
    while (r_it.hasNext()) {
        AlgebraTerm r = (AlgebraTerm)r_it.next();
        concludeterms.addAll(r.getAllSubterms());
    }
    Vector<AlgebraTerm> fifo = new Vector<AlgebraTerm>(ts);
    while (!fifo.isEmpty()) {
        AlgebraTerm t = fifo.remove(0);
        if (!(concludeterms.contains(t) || t.isVariable())) {
        SyntacticFunctionSymbol fsym = (SyntacticFunctionSymbol)t.getSymbol();
        switch (fsym.getSignatureClass()) {
            case Symbol.CONSSIG:
            case Symbol.BOOLSIG:
            case Symbol.SELECTORSIG:
            fifo.addAll(t.getArguments());
            break;
            default:
            DefFunctionSymbol fdsym = (DefFunctionSymbol)fsym;
            boolean canConclude = false;
            r_it = concludeterms.iterator();
            while (!canConclude && r_it.hasNext()) {
                AlgebraTerm r = (AlgebraTerm)r_it.next();
                Symbol gsym = r.getSymbol();
                if ((gsym instanceof DefFunctionSymbol) && r.getArguments().equals(t.getArguments())) {
                canConclude = this.sameTerminationBehaviour(fdsym, (DefFunctionSymbol)gsym);
                }
            }
        }
        }
    }
    return true;
    }


    public boolean isTerminating(DefFunctionSymbol fsym){
        return this.terminating.contains(fsym);
    }

    public boolean isTerminating(){
        return this.terminating.containsAll(this.forCheck);
    }


    public boolean isTerminating(AlgebraTerm t) {
        if (t.isVariable()) {
            return true;
        } else if ( (t.getSymbol() instanceof ConstructorSymbol) || this.isTerminating((DefFunctionSymbol)t.getSymbol())) {
            for(AlgebraTerm arg : t.getArguments()) {
                if (!this.isTerminating(arg)) {
                    return false;
                }
            }
            return true;
        } else {
            return false;
        }
    }


    public void setTerminating(DefFunctionSymbol fsym){
        this.terminating.add(fsym);
    }

    public String getName(){
        return "SIMPOBL";
    }

    public SimplifierObligation shallowcopy(){
        SimplifierObligation obl = new SimplifierObligation(this);
        return obl;
    }

    public SimplifierObligation deepcopy(){
        return (SimplifierObligation) Copy.copyObject(this);
    }

}
