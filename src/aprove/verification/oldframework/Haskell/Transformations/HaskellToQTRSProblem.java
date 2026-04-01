package aprove.verification.oldframework.Haskell.Transformations;

import java.util.*;
import java.util.logging.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Collectors.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Literals.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Stephan Swiderski
 */
public class HaskellToQTRSProblem extends BasicReduction {
    public static final String arrowName = "@";
    Stack<TRSTerm> terms;
    List<Rule> rules;
    Set<HaskellEntity> notUnique;
    NameGenerator tyVarNames;

    List<TRSTerm> curPats;
    HaskellEntity curFunctionEntity;
    HaskellEntity errorEntity;
    HaskellEntity arrowEntity;
    boolean curFunctionIsMember;
    boolean needAndEntity;
    boolean addTypes;

    FunctionSymbol trsApply;
    FunctionSymbol trsTypeApply;

    /**
     * stores the name of the unknown type constructor, which is used for fresh type variables on right hand sides of rules
     */
    private final String unknownTypeConstructorName;

    private HaskellEntity getEntity(final String name, final HaskellEntity.Sort sort) {
        return this.prelude.getEntity(this, "Prelude", name, sort);
    }

    public HaskellToQTRSProblem(final Modules modules, final boolean addTypes) {
        this.notUnique = modules.buildNotUniqueGroup();
        this.tyVarNames = new NoUsedTyVarNameGenerator(modules.getPrelude());
        this.rules = new ArrayList<Rule>();
        this.terms = new Stack<TRSTerm>();
        this.trsApply = FunctionSymbol.create("app", 2);
        this.trsTypeApply = FunctionSymbol.create("#", 2);
        this.prelude = modules.getPrelude();
        //this.andEntity = this.getEntity("&&",HaskellEntity.Sort.VAR);
        this.arrowEntity = this.prelude.getTypeArrow();
        this.errorEntity = this.getEntity("error", HaskellEntity.Sort.VAR);
        this.addTypes = addTypes;

        this.unknownTypeConstructorName = this.prelude.getFreshNameFor("tyUnknown");
    }

    public void push(final TRSTerm a) {
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("Term:"+a);
        }

        this.terms.push(a);
    }

    public TRSTerm pop() {
        return this.terms.pop();
    }

    public List<TRSTerm> popAll() {
        final List<TRSTerm> buf = this.terms;
        this.terms = new Stack<TRSTerm>();
        return buf;
    }

    public TRSTerm createTWrap(final TRSTerm a, final HaskellObject ho) {
        if (this.addTypes) {
            return this.createTWrapDirect(a, ho.getTypeTerm());
        }
        return a;
        //
    }

    public TRSTerm createTWrapDirect(final TRSTerm a, final HaskellType tt) {
        final Atom atom = (Atom) HaskellTools.getLeftMost(tt);
        if (atom == null) {
            HaskellSym.showee(this.curFunctionEntity);
        }
        assert (atom != null);
        if (atom instanceof Cons) {
            final HaskellEntity e = atom.getSymbol().getEntity();
            String name = null;
            if (this.arrowEntity == e) {
                name = HaskellToQTRSProblem.arrowName;
            } else {
                name = this.makeName(e);
            }
            return this.createTRSTypeApply(a, this.createTRSConstr(name));
        } else {
            return this.createTRSTypeApply(a, this.createTRSVar(this.tyVarNames.getNameFor(atom.getSymbol())));
        }
    }

    public TRSTerm createFuncTWrap(final TRSTerm a) {
        return this.createTRSTypeApply(a, this.createTRSConstr(HaskellToQTRSProblem.arrowName));
    }

    public TRSTerm createTRSApply(final TRSTerm a, final TRSTerm b) {
        final ArrayList<TRSTerm> pars = new ArrayList<TRSTerm>();
        pars.add(a);
        pars.add(b);
        return TRSTerm.createFunctionApplication(this.trsApply, ImmutableCreator.create(pars));
    }

    public TRSTerm createTRSTypeApply(final TRSTerm a, final TRSTerm b) {
        final ArrayList<TRSTerm> pars = new ArrayList<TRSTerm>();
        pars.add(a);
        pars.add(b);
        return TRSTerm.createFunctionApplication(this.trsTypeApply, ImmutableCreator.create(pars));
    }

    public String makeName(final HaskellEntity e) {
        String name = null;
        if (this.notUnique.contains(e)) {
            name = e.getModule().getName() + "." + e.getName();
        } else {
            name = e.getName();
        }
        return name;
    }

    public TRSTerm createTRSConstr(final HaskellEntity e, final boolean member) {
        String name = this.makeName(e);
        if (member) {
            name = "@" + name;
        }
        return this.createTRSConstr(name);
    }

    public TRSTerm createTRSConstr(final HaskellEntity e) {
        return this.createTRSConstr(this.makeName(e));
    }

    public TRSTerm createTRSConstr(final String name) {
        return TRSTerm.createFunctionApplication(FunctionSymbol.create(name, 0), TRSTerm.EMPTY_ARGS);
    }

    public TRSTerm createTRSVar(final HaskellEntity e) {
        return this.createTRSVar(e.getName());
    }

    public TRSTerm createTRSVar(final String name) {
        return TRSTerm.createVariable(name);
    }

    @Override
    public HaskellObject caseCons(final Cons ho) {
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println(ho.getSymbol());
            System.out.println(ho.getSymbol().getEntity());
        }

        this.push(this.createTWrap(this.createTRSConstr(ho.getSymbol().getEntity()), ho));
        return ho;
    }

    @Override
    public HaskellObject caseIntegerLit(final IntegerLit ho) {
        TRSTerm num = this.createTWrap(this.createTRSConstr("Zero"), ho);
        for (int i = 0; i < ho.getIntValue(); i++) {
            num = this.createTWrap(this.createTRSApply(this.createFuncTWrap(this.createTRSConstr("Succ")), num), ho);
        }
        this.push(num);
        return ho;
    }

    @Override
    public HaskellObject caseCharLit(final CharLit ho) {
        TRSTerm num = this.createTWrap(this.createTRSConstr("Zero"), ho);
        for (int i = 0; i < ho.getCharValue(); i++) {
            num = this.createTWrap(this.createTRSApply(this.createFuncTWrap(this.createTRSConstr("Succ")), num), ho);
        }
        this.push(this.createTWrap(this.createTRSApply(this.createFuncTWrap(this.createTRSConstr("Char")), num), ho));
        return ho;
    }

    @Override
    public HaskellObject caseVar(final Var ho) {
        final HaskellEntity e = ho.getSymbol().getEntity();
        if (((VarEntity) e).getLocal()) {
            this.push(this.createTWrap(this.createTRSVar(e), ho));
        } else {
            //if (e == this.andEntity) needAndEntity = true;
            this.push(this.createTWrap(this.createTRSConstr(e), ho));
        }
        return ho;
    }

    @Override
    public HaskellObject caseApply(final Apply ho) {
        final TRSTerm b = this.pop();
        final TRSTerm a = this.pop();
        this.push(this.createTWrap(this.createTRSApply(a, b), ho));
        return ho;
    }

    @Override
    public void icaseHaskellRule(final HaskellRule ho) {
        this.curPats = this.popAll();
    }

    @Override
    public HaskellObject caseHaskellRule(final HaskellRule ho) {
        TRSTerm left = this.createTRSConstr(this.curFunctionEntity, this.curFunctionIsMember);
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("RRA:"+left);
        }

        for (final TRSTerm pat : this.curPats) {
            left = this.createTRSApply(this.createFuncTWrap(left), pat);

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //  System.out.println("RRB:"+left);
            }
        }
        left = this.createTWrap(left, ho.getExpression());

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("RRC:" + left);
        }

        final TRSTerm right = this.pop();

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("RRD:" + right);
        }

        this.rules.add(Rule.create((TRSFunctionApplication) left, right));
        return ho;
    }

    @Override
    public void fcaseFunction(final Function ho) {
        super.fcaseFunction(ho);
        this.curFunctionEntity = ho.getSymbol().getEntity();
    }

    public static QTRSProblem applyTo(final Modules modules, final boolean addTypes) {
        //HaskellSym.showee(modules);
        final HaskellToQTRSProblem httt = new HaskellToQTRSProblem(modules, addTypes);
        httt.forModules(modules);
        final Set<Rule> trules = new HashSet<Rule>(httt.rules);
        final Set<TRSFunctionApplication> lefts = HaskellToQTRSProblem.createLeftSet(trules);
        final QTRSProblem prog = QTRSProblem.create(ImmutableCreator.create(trules), lefts);
        return prog;
    }

    public static QTRSProblem applyTo(final Modules modules,
        final List<Pair<HaskellExp, HaskellExp>> rules,
        final boolean addTypes,
        final Abortion aborter) {
        //HaskellSym.showee(modules);
        final HaskellToQTRSProblem httt = new HaskellToQTRSProblem(modules, addTypes);
        final Set<Rule> trsRules = httt.createRuleSet(modules, rules,/*null,*/aborter);
        final Set<TRSFunctionApplication> lefts = HaskellToQTRSProblem.createLeftSet(trsRules);
        final QTRSProblem prog = QTRSProblem.create(ImmutableCreator.create(new HashSet<Rule>(trsRules)), lefts);
        return prog;
    }

    /**
     * Builds a QDPProblem, where it has to be specified whether this is to be used for
     * NonTermination (then Q={} and f=a) or for Termination (then Q=R and f=m)
     * @param modules The Haskell modules representing the analysis
     * @param hPR Dependency Pairs and Rules to build the QDPProblem for
     * @param addTypes Whether to add type annotation to every symbol (unused)
     * @param aborter An aborter
     * @param nonTermination Whether the resulting QDPProblem is to be used for NonTermination (true) or for Termination (false)
     * @return A QDPProblem containing the given Dependency Pairs and Rules, with Q and f set as specified above
     */
    private static QDPProblem buildQDPProblem(final Modules modules,
        final HaskellPR hPR,
        final boolean addTypes,
        final Abortion aborter,
        final boolean nonTermination,
        final VarEntity ccCheckEntity) {
        final HaskellToQTRSProblem httt = new HaskellToQTRSProblem(modules, addTypes);
        final List<Pair<HaskellExp, HaskellExp>> hP = hPR.getP();

        // XXX DEBUG
        if (aprove.Globals.DEBUG_MATRAF) {
            System.err.println("hP: " + hP);
        }

        Logger logger = null;
        long now = 0;
        // XXX DEBUG
        if (aprove.Globals.DEBUG_MATRAF) {
            logger = Logger.getLogger("aprove.verification.oldframework.Haskell.Transformations.HaskellToQTRSProcessor");
            now = System.nanoTime();
        }

        final Set<Rule> ptrules = httt.createDPSet(modules, hP,/*httt.collectFreeVars(hP),*/aborter);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_MATRAF) {
            now = System.nanoTime() - now;
            logger.log(Level.FINE, "Creation of P ruleset took " + now / 1.e9 + " seconds\n");
            now = System.nanoTime();
        }

        final Set<Rule> rtrules = httt.createRuleSet(modules, hPR.getR(),/*null,*/aborter);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_MATRAF) {
            now = System.nanoTime() - now;
            logger.log(Level.FINE, "Creation of R ruleset took " + now / 1.e9 + " seconds\n");
            now = System.nanoTime();
        }

        final FunctionSymbol errorSym = FunctionSymbol.create(httt.errorEntity.getName(), 1);

        Set<TRSFunctionApplication> rtlefts;
        if (nonTermination) {
            rtlefts = new HashSet<TRSFunctionApplication>(); // Q = {}

            if (ccCheckEntity != null) {
                final Set<FunctionSymbol> funcSyms = new HashSet<FunctionSymbol>();
                for (final Rule rule : rtrules) {
                    funcSyms.add(rule.getRootSymbol());
                }
                final FreshNameGenerator fng = new FreshNameGenerator(funcSyms, FreshNameGenerator.VARIABLES);

                // add the class constraint check to Q
                final FunctionSymbol ccCheckSym = FunctionSymbol.create(ccCheckEntity.getName(), 1);
                final TRSVariable ccs = TRSTerm.createVariable(fng.getFreshName("ccs", false));
                rtlefts.add(TRSTerm.createFunctionApplication(ccCheckSym, new TRSTerm[] {ccs }));
            }
        } else {
            rtlefts = HaskellToQTRSProblem.createLeftSet(rtrules); // Q = R
        }
        //Set<FunctionApplication> rtlefts = createLeftSet(rtrules); // Q = R
        //Set<FunctionApplication> rtlefts = createLeftDefinedSymsAndAddErrorRule(rtrules, errorSym); // Q = {f(x_1,...,x_n) | f \in defined(R)}, R += {f(x1,...,error(x_i),...,x_n) -> error(x_i)}
        //Set<FunctionApplication> rtlefts = new HashSet<FunctionApplication>(); // Q = {}

        // XXX DEBUG
        if (aprove.Globals.DEBUG_MATRAF) {
            now = System.nanoTime() - now;
            logger.log(Level.FINE, "Creation of Q took " + now / 1.e9 + " seconds\n");
            now = System.nanoTime();
        }

        final QTRSProblem qtrs = QTRSProblem.create(ImmutableCreator.create(new HashSet<Rule>(rtrules)), rtlefts);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_MATRAF) {
            now = System.nanoTime() - now;
            logger.log(Level.FINE, "Creation of QTRS took " + now / 1.e9 + " seconds\n");
            now = System.nanoTime();
        }

        boolean minimal = true;
        // this is now set to minimal (last true)

        if (nonTermination) {
            minimal = false;
        }

        final QDPProblem qdp = QDPProblem.create(ImmutableCreator.create(ptrules), qtrs, minimal);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_MATRAF) {
            now = System.nanoTime() - now;
            logger.log(Level.FINE, "Creation of QDP took " + now / 1.e9 + " seconds\n");
        }

        return qdp;
    }

    /**
     * creates a QDPProblem from a set of Dependency Pairs and a set of rules that may be used to show termination
     * @param modules The Haskell modules to show termination for
     * @param hPR The Dendency Pairs and rules
     * @param addTypes Whether to add types (unused)
     * @param aborter An Aborter
     * @return A QDPProblem with the supplied Dependency Pairs and rules, where Q=R and f=m
     */
    public static QDPProblem buildQDPProblemForTermination(final Modules modules,
        final HaskellPR hPR,
        final boolean addTypes,
        final Abortion aborter) {
        return HaskellToQTRSProblem.buildQDPProblem(modules, hPR, addTypes, aborter, false, null);
    }

    /**
     * creates a QDPProblem from a set of Dependency Pairs and a set of rules that may be used to show non-termination
     * @param modules The Haskell modules to show termination for
     * @param hPR The Dendency Pairs and rules
     * @param addTypes Whether to add types (unused)
     * @param aborter An Aborter
     * @param ccCheckEntity The VarEntity of the ClassConstraint check function, may be null if no such function is needed
     * @return A QDPProblem with the supplied Dependency Pairs and rules, where Q={} and f=a
     */
    public static QDPProblem buildQDPProblemForNonTermination(final Modules modules,
        final HaskellPR hPR,
        final boolean addTypes,
        final Abortion aborter,
        final VarEntity ccCheckEntity) {
        return HaskellToQTRSProblem.buildQDPProblem(modules, hPR, addTypes, aborter, true, ccCheckEntity);
    }

    public Set<TRSTerm> collectFreeVars(final List<Pair<HaskellExp, HaskellExp>> rules) {
        final Set<Var> vars = new HashSet<Var>();
        for (final Pair<HaskellExp, HaskellExp> rule : rules) {
            final Set<Var> rvars = new HashSet<Var>();
            final FreeLocalVarCollector flvc = new FreeLocalVarCollector(rvars);
            rule.getKey().visit(flvc);

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("A" + rvars);
            }

            rvars.clear();
            rule.getValue().visit(flvc);

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println("B" + rvars);
            }

            vars.addAll(rvars);
        }
        final Set<TRSTerm> exts = new HashSet<TRSTerm>();
        for (final Var v : vars) {
            final HaskellEntity e = v.getSymbol().getEntity();
            exts.add(this.createTWrap(this.createTRSVar(e), v));
        }
        return exts;
    }

    /* data structures for the creation of nice type names */
    private HashMap<HaskellSym, String> typeVarSym2Name = null;
    private HashMap<HaskellEntity, String> tyConsEnt2Name = null;

    /**
     * creates a nice name for a type variable
     */
    private String createNiceTypeVarName(final HaskellSym typeVarSym) {
        if (this.typeVarSym2Name == null) {
            this.typeVarSym2Name = new HashMap<HaskellSym, String>();
        }

        String niceName = this.typeVarSym2Name.get(typeVarSym);
        if (niceName == null) {
            niceName = this.tyVarNames.createNewNameFor(typeVarSym);
            this.typeVarSym2Name.put(typeVarSym, niceName);
        }

        return niceName;
    }

    /**
     * creates an unused name for a type constructor
     * (e.g. otherwise [] as empty list and as list type constructor would overlap)
     */
    private String createUniqTyConsName(final HaskellEntity he) {
        if (this.tyConsEnt2Name == null) {
            this.tyConsEnt2Name = new HashMap<HaskellEntity, String>();
        }

        String niceName = this.tyConsEnt2Name.get(he);
        if (niceName == null) {
            final String niceBaseName = "ty_" + this.makeName(he);
            niceName = niceBaseName;
            int suffix = 0;
            while (this.prelude.nameIsUsed(niceName)) {
                niceName = niceBaseName + Integer.toString(suffix);
                ++suffix;
            }
        }

        return niceName;
    }

    public TRSTerm typeConvert(final HaskellObject ho, final Set<TRSVariable> allowedVars) {
        if (ho instanceof Apply) {
            final Apply app = (Apply) ho;
            final TRSTerm funcTerm = this.typeConvert(app.getFunction(), allowedVars);
            final TRSTerm argTerm = this.typeConvert(app.getArgument(), allowedVars);
            return this.createTRSApply(funcTerm, argTerm);
        } else {
            if (ho instanceof Cons) {
                final Cons cons = (Cons) ho;
                final String newTyConsName = this.createUniqTyConsName(cons.getSymbol().getEntity());
                return this.createTRSConstr(newTyConsName/*cons.getSymbol().getEntity()*/);
            } else /* if (ho instanceof Var) */{
                final Var var = (Var) ho;
                final String newTyVarName = this.createNiceTypeVarName(var.getSymbol());
                final TRSTerm vTerm = this.createTRSVar(newTyVarName);
                return ((allowedVars != null) && (!allowedVars.contains(vTerm)))
                    ? this.createTRSConstr(this.unknownTypeConstructorName) : vTerm;
            }
        }
    }

    /**
     * Converts a Haskell expression to a term that can be used in a QTRS or QDP problem
     * @param exp Haskell expression to convert
     * @param filter argument filtering
     * @param allowedVars type variables allowed to occur, if set to null then all are allowed
     * @return the constructed term
     */
    public TRSTerm convertToTRSTerm(final HaskellObject exp,
        final Map<HaskellEntity, List<Boolean>> filter,
        final Set<TRSVariable> allowedVars) {
        final List<HaskellObject> exps = HaskellTools.applyFlatten(exp);
        final Atom atm = (Atom) exps.remove(0);
        final HaskellEntity e = atm.getSymbol().getEntity();
        if ((e == null) || (e instanceof TyConsEntity)) {
            return this.typeConvert(exp, allowedVars);
        }
        if (atm instanceof Var) {
            final Var var = (Var) atm;
            if (((VarEntity) e).getLocal()) {
                final TRSVariable trsVar = (TRSVariable) this.createTRSVar(e);
                if ((allowedVars != null) && (!allowedVars.contains(trsVar))) {
                    // this should never happen
                    throw new RuntimeException("violated Variable-Condition!");
                }
                return trsVar;
            }
        }
        final ArrayList<TRSTerm> paras = new ArrayList<TRSTerm>();
        final List<Boolean> args = filter.get(e);
        int i = 0;
        for (final HaskellObject ho : exps) {
            boolean argfilter = false;
            if (args != null) {
                argfilter = args.get(i);
            }
            if (!argfilter) {
                paras.add(this.convertToTRSTerm(ho, filter, allowedVars));
            }
            i++;
        }
        final String name = this.makeName(e);
        return TRSTerm.createFunctionApplication(FunctionSymbol.create(name, paras.size()), ImmutableCreator.create(paras));
    }

    public Set<Rule> createDPSet(final Modules modules, final List<Pair<HaskellExp, HaskellExp>> rules,/*Set<Term> exts,*/
        final Abortion aborter) {
        final Map<HaskellEntity, List<Boolean>> filter = new HashMap<HaskellEntity, List<Boolean>>();

        boolean changed = true;
        while (changed) {
            changed = false;

            for (final Pair<HaskellExp, HaskellExp> rule : rules) {
                final Set<HaskellSym> freeSymsLeft = new HashSet<HaskellSym>();
                final FreeLocalVarSymCollector fvscL = new FreeLocalVarSymCollector(freeSymsLeft);
                final List<HaskellObject> left_objs = HaskellTools.applyFlatten(rule.getKey());

                final HaskellEntity left_he = ((Atom) left_objs.remove(0)).getSymbol().getEntity();
                final List<Boolean> left_argFilter = filter.get(left_he);
                int i = 0;
                for (final HaskellObject ho : left_objs) {
                    if ((left_argFilter == null) || (!left_argFilter.get(i))) {
                        ho.visit(fvscL);
                    }
                    i++;
                }
                final List<HaskellObject> right_objs = HaskellTools.applyFlatten(rule.getValue());
                final HaskellEntity he = ((Atom) right_objs.remove(0)).getSymbol().getEntity();
                List<Boolean> argFilter = filter.get(he);
                if (argFilter == null) {
                    argFilter = new ArrayList<Boolean>(right_objs.size());
                    for (i = 0; i < right_objs.size(); i++) {
                        argFilter.add(false);
                    }
                    filter.put(he, argFilter);
                }
                i = 0;
                for (final HaskellObject ho : right_objs) {
                    final Set<HaskellSym> freeSymsRight = new HashSet<HaskellSym>();
                    final FreeLocalVarSymCollector fvscR = new FreeLocalVarSymCollector(freeSymsRight);
                    ho.visit(fvscR);
                    freeSymsRight.removeAll(freeSymsLeft);
                    boolean filterArg = !freeSymsRight.isEmpty();

                    if (filterArg) {
                        boolean onlyTyVars = true;
                        for (final HaskellSym vsym : freeSymsRight) {
                            final HaskellEntity e = vsym.getEntity();
                            if (!((e == null) || (e instanceof TyConsEntity))) {
                                onlyTyVars = false;
                                break;
                            }
                        }
                        filterArg = !onlyTyVars;
                    }

                    if (!argFilter.get(i) && filterArg) {
                        changed = true;
                        argFilter.set(i, filterArg);

                        // XXX DEBUG
                        if (aprove.Globals.DEBUG_MATRAF) {
                            System.err.println("adding filtering for " + he + " arg num " + i + " (rule = "
                                + rule.getKey() + " -> " + rule.getValue());
                        }
                    }
                    i++;
                }
            }

        }

        return this.createRuleSet(modules, rules, filter, aborter);
    }

    public Set<Rule> createRuleSet(final Modules modules, final List<Pair<HaskellExp, HaskellExp>> rules,/*Set<Term> exts,*/
        final Abortion aborter) {
        final Map<HaskellEntity, List<Boolean>> filter = new HashMap<HaskellEntity, List<Boolean>>();
        return this.createRuleSet(modules, rules, filter, aborter);
    }

    public Set<Rule> createRuleSet(final Modules modules,
        final List<Pair<HaskellExp, HaskellExp>> rules,
        final Map<HaskellEntity, List<Boolean>> filter,/*Set<Term> exts,*/
        final Abortion aborter) {
        //HaskellSym.showee(modules);
        this.forModules(modules);
        final Set<Rule> trules = new HashSet<Rule>();

        for (final Pair<HaskellExp, HaskellExp> rule : rules) {

            final TRSTerm left = this.convertToTRSTerm(rule.getKey(), filter, null);
            final TRSTerm right = this.convertToTRSTerm(rule.getValue(), filter, left.getVariables());

            trules.add(Rule.create((TRSFunctionApplication) left, right));
        }
        return trules;
    }

    public Rule correctRuleForVarCond(TRSTerm left, TRSTerm right, final Set<TRSTerm> exts) {
        if (exts != null) {
            for (final TRSTerm t : exts) {
                left = this.createTRSApply(left, t);
                right = this.createTRSApply(right, t);
            }
        }
        return Rule.create((TRSFunctionApplication) left, right);
    }

    public static Set<TRSFunctionApplication> createLeftSet(final Set<Rule> rules) {
        final Set<TRSFunctionApplication> lefts = new HashSet<TRSFunctionApplication>();
        for (final Rule rule : rules) {
            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                System.out.println(rule);
            }

            lefts.add(rule.getLeft());
        }
        return lefts;
    }

    /**
     * creates Q from a set of rules
     * This will contain every defined symbol in the rules,
     * where the arguments are filled with variables
     * and adds a rule f(error(x)) -> error(x) to the rules
     * @param rules a set of rules
     * @param errorSym the error constructor symbol
     * @return a set of function applications for every defined function
     */
    public static Set<TRSFunctionApplication> createLeftDefinedSymsAndAddErrorRule(final Set<Rule> rules, final FunctionSymbol errorSym) {
        final Set<TRSFunctionApplication> lefts = new HashSet<TRSFunctionApplication>();
        final Set<FunctionSymbol> funcSyms = new HashSet<FunctionSymbol>();
        for (final Rule rule : rules) {
            funcSyms.add(rule.getRootSymbol());
        }
        final FreshNameGenerator fng = new FreshNameGenerator(funcSyms, FreshNameGenerator.VARIABLES);
        for (final FunctionSymbol fsym : funcSyms) {
            final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
            for (int i = 0; i < fsym.getArity(); ++i) {
                args.add(TRSTerm.createVariable(fng.getFreshName("x_" + i, true)));
            }
            lefts.add(TRSTerm.createFunctionApplication(fsym, ImmutableCreator.create(args)));

            // adding the error rule for every position
            for (int i = 0; i < fsym.getArity(); ++i) {
                final ArrayList<TRSTerm> errorArgs = new ArrayList<TRSTerm>(args);
                final TRSTerm errorTerm =
                    TRSTerm.createFunctionApplication(errorSym, new TRSTerm[] {args.get(i) });
                errorArgs.set(i, errorTerm);
                rules.add(Rule.create(
                    TRSTerm.createFunctionApplication(fsym, ImmutableCreator.create(errorArgs)), errorTerm));
            }
        }
        return lefts;
    }

    @Override
    public boolean guardEntity(final HaskellEntity ho) {
        /*        if (this.andEntity == ho) return false;
                if (ho instanceof TyClassEntity) {
                    return true;
                }
                if (ho instanceof InstEntity) {
                    InstEntity ie = (InstEntity) ho;
                    TyClassEntity tce = (TyClassEntity)ie.getTyClassEntity();
                    Set<HaskellEntity> members = new HashSet<HaskellEntity>(tce.getSubEntities());
                    for (HaskellEntity ive : ie.getSubEntities()){
                        HaskellEntity cve = ((InstFunction)ive.getValue()).getMemberForInst();
                        members.remove(cve);
                    }
                    //this.buildCalls((TyConsEntity)ie.getTyConsEntity(),members);
                    return true;
                }
                return (ho instanceof VarEntity);*/
        return false;
    }

    @Override
    public boolean guardValue(final HaskellEntity ho) {
        /*if (ho instanceof VarEntity){
            this.curFunctionIsMember = (ho instanceof CVarEntity);
            return true;
        }*/
        return false;
    }

    /*private void buildCalls(TyConsEntity tce,Set<HaskellEntity> members){
        for (HaskellEntity member : members){
            if (member.getValue() != null) {
                MemberTypeSchema mts = Copy.deep((MemberTypeSchema)member.getType());
                HaskellType typeTerm = mts.getMatrix();
                ClassConstraint cc = mts.getClassConstraint();
                Var var = (Var)cc.getType();
                aprove.verification.oldframework.Haskell.Substitution subs = new aprove.verification.oldframework.Haskell.Substitution(var,new Cons(new HaskellNamedSym(tce)));
                typeTerm = (HaskellType) subs.applyToDestructive(typeTerm);
                List<HaskellType> typeTerms = this.prelude.deArrow(typeTerm);
                HaskellType lastTypeTerm = typeTerms.remove(typeTerms.size()-1);

                Term left = createTRSConstr(member,false);
                Term right = createTRSConstr(member,true);
                int i=0;
                for (HaskellType tt : typeTerms){
                    i++;
                    Term trsvar = this.createTRSVar("x"+i);
                    Term trsvarw = this.createTWrapDirect(trsvar,tt);
                    left = this.createTRSApply(this.createFuncTWrap(left),trsvarw);
                    right = this.createTRSApply(this.createFuncTWrap(right),trsvarw.deepcopy());
                }
                left = this.createTWrapDirect(left,lastTypeTerm);
                right = this.createTWrapDirect(right,lastTypeTerm);

                this.rules.add(Rule.create(left,right));
            }
        }
    }*/

    @Override
    public boolean guardStartTerms(final Modules ho) {
        return false;
    }

    public static class NoUsedTyVarNameGenerator extends TyVarNameGenerator {

        Prelude prelude;

        public NoUsedTyVarNameGenerator(final Prelude prelude) {
            super();
            this.prelude = prelude;
        }

        @Override
        public String createNewNameFor(final Object o) {
            String nname = null;
            do {
                nname = super.createNewNameFor(o);
            } while (this.prelude.nameIsUsed(nname));
            return nname;
        }

    }
}
