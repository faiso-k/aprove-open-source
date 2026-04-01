package aprove.verification.oldframework.Haskell.Transformations;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Literals.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Stephan Swiderski
 */
public class HaskellToTRSTransformation extends BasicReduction {
    public static final String arrowName = "@";
    Stack<AlgebraTerm> terms;
    List<Rule> rules;
    Sort sort;
    Set<HaskellEntity> notUnique;
    NameGenerator tyVarNames;

    List<AlgebraTerm> curPats;
    HaskellEntity curFunctionEntity;
    HaskellEntity arrowEntity;
    boolean curFunctionIsMember;
    boolean addTypes;

    SyntacticFunctionSymbol trsApply;
    SyntacticFunctionSymbol trsTypeApply;

    private HaskellEntity getEntity(final String name, final HaskellEntity.Sort sort) {
        return this.prelude.getEntity(this, "Prelude", name, sort);
    }

    public HaskellToTRSTransformation(final Modules modules, final boolean addTypes) {
        this.sort = Sort.create(Sort.standardName);
        this.addTypes = addTypes;
        this.notUnique = modules.buildNotUniqueGroup();
        this.tyVarNames = new NoUsedTyVarNameGenerator(modules.getPrelude());
        this.rules = new Vector<Rule>();
        this.terms = new Stack<AlgebraTerm>();
        this.trsApply = DefFunctionSymbol.create("app", 2, this.sort);
        //this.trsApply.setFixity(FunctionSymbol.INFIXL);
        //this.trsApply.setFixityLevel(1);
        this.trsTypeApply = DefFunctionSymbol.create("#", 2, this.sort);
        this.trsTypeApply.setFixity(SyntacticFunctionSymbol.INFIXL);
        this.trsTypeApply.setFixityLevel(2);
        this.prelude = modules.getPrelude();
        this.arrowEntity = this.prelude.getTypeArrow();
    }

    public void push(final AlgebraTerm a) {
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("Term:"+a);
        }

        this.terms.push(a);
    }

    public AlgebraTerm pop() {
        return this.terms.pop();
    }

    public List<AlgebraTerm> popAll() {
        final List<AlgebraTerm> buf = this.terms;
        this.terms = new Stack<AlgebraTerm>();
        return buf;
    }

    public AlgebraTerm createTWrap(final AlgebraTerm a, final HaskellObject ho) {
        return this.addTypes ? this.createTWrapDirect(a, ho.getTypeTerm()) : a;
    }

    public AlgebraTerm createTWrapDirect(final AlgebraTerm a, final HaskellType tt) {
        final Atom atom = (Atom) HaskellTools.getLeftMost(tt);
        if (atom == null) {
            HaskellSym.showee(this.curFunctionEntity);
        }
        assert (atom != null);
        if (atom instanceof Cons) {
            final HaskellEntity e = atom.getSymbol().getEntity();
            String name = null;
            if (this.arrowEntity == e) {
                name = HaskellToTRSTransformation.arrowName;
            } else {
                name = this.makeName(e);
            }
            return this.createTRSTypeApply(a, this.createTRSConstr(name));
        } else {
            return this.createTRSTypeApply(a, this.createTRSVar(this.tyVarNames.getNameFor(atom.getSymbol())));
        }
    }

    public AlgebraTerm createFuncTWrap(final AlgebraTerm a) {
        return this.createTRSTypeApply(a, this.createTRSConstr(HaskellToTRSTransformation.arrowName));
    }

    public AlgebraTerm createTRSApply(final AlgebraTerm a, final AlgebraTerm b) {
        final List<AlgebraTerm> pars = new Vector<AlgebraTerm>();
        pars.add(a);
        pars.add(b);
        return AlgebraFunctionApplication.create(this.trsApply, pars);
    }

    public AlgebraTerm createTRSTypeApply(final AlgebraTerm a, final AlgebraTerm b) {
        final List<AlgebraTerm> pars = new Vector<AlgebraTerm>();
        pars.add(a);
        pars.add(b);
        return AlgebraFunctionApplication.create(this.trsTypeApply, pars);
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

    public AlgebraTerm createTRSConstr(final HaskellEntity e, final boolean member) {
        String name = this.makeName(e);
        if (member) {
            name = "@" + name;
        }
        return this.createTRSConstr(name);
    }

    public AlgebraTerm createTRSConstr(final HaskellEntity e) {
        return this.createTRSConstr(this.makeName(e));
    }

    public AlgebraTerm createTRSConstr(final String name) {
        return AlgebraFunctionApplication.create(ConstructorSymbol.create(name, 0, this.sort));
    }

    public AlgebraTerm createTRSVar(final HaskellEntity e) {
        return AlgebraVariable.create(VariableSymbol.create(e.getName(), this.sort));
    }

    public AlgebraTerm createTRSVar(final String name) {
        return AlgebraVariable.create(VariableSymbol.create(name, this.sort));
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
        AlgebraTerm num = this.createTWrap(this.createTRSConstr("Zero"), ho);
        for (int i = 0; i < ho.getIntValue(); i++) {
            num = this.createTWrap(this.createTRSApply(this.createFuncTWrap(this.createTRSConstr("Succ")), num), ho);
        }
        this.push(num);
        return ho;
    }

    @Override
    public HaskellObject caseCharLit(final CharLit ho) {
        AlgebraTerm num = this.createTWrap(this.createTRSConstr("Zero"), ho);
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
            this.push(this.createTWrap(this.createTRSConstr(e), ho));
        }
        return ho;
    }

    @Override
    public HaskellObject caseApply(final Apply ho) {
        final AlgebraTerm b = this.pop();
        final AlgebraTerm a = this.pop();
        this.push(this.createTWrap(this.createTRSApply(a, b), ho));
        return ho;
    }

    @Override
    public void icaseHaskellRule(final HaskellRule ho) {
        this.curPats = this.popAll();
    }

    @Override
    public HaskellObject caseHaskellRule(final HaskellRule ho) {
        AlgebraTerm left = this.createTRSConstr(this.curFunctionEntity, this.curFunctionIsMember);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            //System.out.println("RRA:"+left);
        }

        for (final AlgebraTerm pat : this.curPats) {
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

        final AlgebraTerm right = this.pop();

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            System.out.println("RRD:" + right);
        }

        this.rules.add(Rule.create(left, right));
        return ho;
    }

    @Override
    public void fcaseFunction(final Function ho) {
        super.fcaseFunction(ho);
        this.curFunctionEntity = ho.getSymbol().getEntity();
    }

    public static Program applyTo(final Modules modules, final Abortion aborter) {
        //HaskellSym.showee(modules);
        final HaskellToTRSTransformation httt = new HaskellToTRSTransformation(modules, false);
        httt.forModules(modules);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            for (final Rule rule : httt.rules) {
                System.out.println(rule);
            }
        }

        final Program prog = Program.create(new HashSet<Rule>(httt.rules));
        try {
            prog.addSort(Sort.create(Sort.standardName));
        } catch (final ProgramException e) {
        }
        return prog;
    }

    public static Program applyTo(final Modules modules,
        final List<Pair<HaskellExp, HaskellExp>> rules,
        final boolean addTypes,
        final Abortion aborter) {
        //HaskellSym.showee(modules);
        final HaskellToTRSTransformation httt = new HaskellToTRSTransformation(modules, addTypes);

        final Set<Rule> trsRules = new HashSet<Rule>();
        for (final Pair<HaskellExp, HaskellExp> rule : rules) {
            rule.getKey().visit(httt);
            final AlgebraTerm left = httt.pop();
            rule.getValue().visit(httt);
            final AlgebraTerm right = httt.pop();
            trsRules.add(Rule.create(left, right));
        }
        // XXX DEBUG
        if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
            for (final Rule rule : trsRules) {
                System.out.println(rule);
            }
        }

        final Program prog = Program.create(trsRules);
        try {
            prog.addSort(Sort.create(Sort.standardName));
        } catch (final ProgramException e) {
        }
        return prog;
    }

    @Override
    public boolean guardEntity(final HaskellEntity ho) {
        if (ho instanceof TyClassEntity) {
            return true;
        }
        if (ho instanceof InstEntity) {
            final InstEntity ie = (InstEntity) ho;
            final TyClassEntity tce = (TyClassEntity) ie.getTyClassEntity();
            final Set<HaskellEntity> members = new HashSet<HaskellEntity>(tce.getSubEntities());
            for (final HaskellEntity ive : ie.getSubEntities()) {
                final HaskellEntity cve = ((InstFunction) ive.getValue()).getMemberForInst();
                members.remove(cve);
            }
            this.buildCalls((TyConsEntity) ie.getTyConsEntity(), members);
            return true;
        }
        return (ho instanceof VarEntity);
    }

    @Override
    public boolean guardValue(final HaskellEntity ho) {
        if (ho instanceof VarEntity) {
            this.curFunctionIsMember = (ho instanceof CVarEntity);
            return true;
        }
        return false;
    }

    private void buildCalls(final TyConsEntity tce, final Set<HaskellEntity> members) {
        for (final HaskellEntity member : members) {
            if (member.getValue() != null) {
                final MemberTypeSchema mts = Copy.deep((MemberTypeSchema) member.getType());
                HaskellType typeTerm = mts.getMatrix();
                final ClassConstraint cc = mts.getClassConstraint();
                final Var var = (Var) cc.getType();
                final aprove.verification.oldframework.Haskell.HaskellSubstitution subs =
                    new aprove.verification.oldframework.Haskell.HaskellSubstitution(var, new Cons(new HaskellNamedSym(tce)));
                typeTerm = (HaskellType) subs.applyToDestructive(typeTerm);
                final List<HaskellType> typeTerms = this.prelude.deArrow(typeTerm);
                final HaskellType lastTypeTerm = typeTerms.remove(typeTerms.size() - 1);

                AlgebraTerm left = this.createTRSConstr(member, false);
                AlgebraTerm right = this.createTRSConstr(member, true);
                int i = 0;
                for (final HaskellType tt : typeTerms) {
                    i++;
                    final AlgebraTerm trsvar = this.createTRSVar("x" + i);
                    final AlgebraTerm trsvarw = this.createTWrapDirect(trsvar, tt);
                    left = this.createTRSApply(this.createFuncTWrap(left), trsvarw);
                    right = this.createTRSApply(this.createFuncTWrap(right), trsvarw.deepcopy());
                }
                left = this.createTWrapDirect(left, lastTypeTerm);
                right = this.createTWrapDirect(right, lastTypeTerm);

                this.rules.add(Rule.create(left, right));
            }
        }
    }

    @Override
    public boolean guardStartTerms(final Modules ho) {
        return false;
    }

}

class NoUsedTyVarNameGenerator extends TyVarNameGenerator {

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
