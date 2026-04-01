package aprove.verification.oldframework.Haskell.Visitors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Literals.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
* @author Stephan Swiderski
* @version $Id$
*/
public class ExportVisitor extends HaskellVisitor {
    StringBuffer target;
    Export_Util export_Util;

    Set<HaskellEntity> notUnique;
    Prelude prelude;
    Module module;
    Modules modules;
    Stack<Integer> prioStack;
    Stack<StringBuffer> targets;
    Stack<String> arrows;
    Stack<Integer> positions;

    public ExportVisitor(final Modules modules, final Module module, final Export_Util export_Util,
            final StringBuffer target) {
        this.notUnique = new HashSet<HaskellEntity>();
        this.export_Util = export_Util;
        this.targets = new Stack<StringBuffer>();
        this.modules = modules;
        this.module = module;
        this.prelude = modules.getPrelude();
        this.prioStack = new Stack<Integer>();
        this.prioStack.push(0);
        this.targets.push(target);
        this.target = target;
        this.arrows = new Stack<String>();
        this.positions = new Stack<Integer>();
        this.positions.add(0);
    }

    public Set<HaskellEntity> sortByName(final Set<? extends HaskellEntity> es) {
        final Set<HaskellEntity> res = new TreeSet<HaskellEntity>(new EntityComparator());
        res.addAll(es);
        return res;
    }

    public List<StringBuffer> popTargets(final int i) {
        final int l = this.targets.size();
        final List<StringBuffer> sbs = new Vector<StringBuffer>(this.targets.subList(l - i, l));
        this.targets.setSize(l - i);
        return sbs;
    }

    public void append(final String s) {
        this.targets.peek().append(s);
    }

    public void space() {
        this.append(this.export_Util.appSpace());
    }

    public void joker() {
        this.append(this.export_Util.jokerSign());
    }

    public void irrSign() {
        this.append(this.export_Util.irrSign());
    }

    public void atSign() {
        this.append(this.export_Util.atSign());
    }

    public String getName(final HaskellSym sym, final boolean def) {
        if (sym.getEntity().getTuple() >= 0) {
            String name = "(";
            for (int i = 0; i < sym.getTuple(); i++) {
                name = name + ",";
            }
            name = name + ")";
            return name;
        }
        return this.getName(sym.getEntity(), def);
    }

    private boolean isOperator(final String name) {
        final int i = name.indexOf('.');
        char c;
        if (i >= 0) {
            if (name.length() > 1) {
                c = name.charAt(i + 1);
            } else {
                return true;
            }
        } else {
            c = name.charAt(0);
        }
        return !(Character.isLetter(c) || c == '_' || c == '[' || c == '(');
    }

    private String wantOp(final String name, final boolean op) {
        final boolean isOp = this.isOperator(name);
        if (op && !isOp) {
            return "`" + name + "`";
        }
        if (!op && isOp) {
            return "(" + name + ")";
        }
        return name;
    }

    public String createName(final HaskellSym sym) {
        return this.wantOp(this.getName(sym, false), sym.getOperator()
            && sym.getEntity().getFixity() != InfixDecl.FIXITY_DEFAULT);
    }

    public String createName(final HaskellSym sym, final boolean def, final boolean op) {
        return this.wantOp(this.getName(sym, def), op);
    }

    public String getName(final HaskellEntity entity, final boolean def) {
        assert (entity != null);
        final boolean local = (entity instanceof VarEntity) && (((VarEntity) entity).getLocal());
        String name = null;
        final boolean mm =
            this.notUnique.contains(entity)
                || ((entity.getModule() != this.module) && (entity.getModule() != this.prelude));
        final String wop = "";
        if (!def && mm && !local) {
            //boolean upCase = HaskellEntity.Sort.UPCASE.contains(entity.getSort());
            //    name = this.highLow(entity.getModule().getName(),upCase)+"_"+this.prelude.correctName(entity.getName());
            name = entity.getModule().getName() + "." + entity.getName() + wop;
        } else {
            name = entity.getName() + wop;
        }
        return name;
    }

    @Override
    public boolean outerGuardApply(final Apply ho) {
        return !this.tupleInfixCheck(ho);
    }

    public boolean tupleInfixCheck(final Apply apply) {
        final List<HaskellObject> tups = HaskellTools.applyFlatten(apply);
        final HaskellObject ho = tups.get(0);
        if (ho instanceof Cons) {
            final int j = ((Cons) ho).getSymbol().getEntity().getTuple();
            if (j == (tups.size() - 1)) {
                tups.remove(0);
                this.prioStack.push(0);
                this.append("(");
                boolean first = true;
                for (final HaskellObject te : tups) {
                    if (!first) {
                        this.append(",");
                    }
                    te.visit(this);
                    first = false;
                }
                this.append(")");
                this.prioStack.pop();
                return true;
            }
        }
        final Atom atom = (Atom) ho;
        final HaskellSym sym = atom.getSymbol();
        final HaskellEntity e = sym.getEntity();
        final int p = e.getPriority();
        int pr = p;
        int pl = p;
        if (p <= this.prioStack.peek()) {
            this.append("(");
        }
        final String name = this.createName(sym);
        final boolean b = this.isOperator(name);
        switch (b ? e.getFixity() : InfixDecl.FIXITY_DEFAULT) {
        case InfixDecl.FIXITY_LEFT:
            pl--;
            pr++;
        case InfixDecl.FIXITY_RIGHT:
            pr--;
        case InfixDecl.FIXITY_NON:
            this.prioStack.push(pl);
            this.positions.push(-1);
            tups.get(1).visit(this);
            this.space();
            this.positions.pop();
            this.prioStack.pop();
            this.positions.push(0);
            tups.get(0).visit(this);
            this.positions.pop();
            this.prioStack.push(pr);
            this.positions.push(1);
            if (tups.size() > 2) {
                this.space();
                tups.get(2).visit(this);
            }
            this.positions.pop();
            this.prioStack.pop();
            break;
        case InfixDecl.FIXITY_DEFAULT:
        case InfixDecl.FIXITY_MONO:
        default:
            this.positions.push(-2);
            this.prioStack.push(p);
            boolean first = true;
            for (final HaskellObject par : tups) {
                if (!first) {
                    this.space();
                }
                par.visit(this);
                first = false;
            }
            this.prioStack.pop();
            this.positions.pop();
            break;
        }
        if (p <= this.prioStack.peek()) {
            this.append(")");
        }
        return true;
    }

    @Override
    public void fcaseApply(final Apply apply) {

    }

    @Override
    public HaskellObject caseApply(final Apply apply) {
        return apply;
    }

    @Override
    public HaskellObject caseCons(final Cons cons) {
        if (cons.getSymbol().getName(false).equals("[]")) {
            this.append(this.export_Util.haskellCons(this.export_Util.escape("[]")));
        } else if (cons.getSymbol().getTuple() == 0) {
            this.append(this.export_Util.haskellCons(this.export_Util.escape("()")));
        } else if (cons.getSymbol().getEntity() == this.prelude.getTypeArrow()) {
            this.append(this.export_Util.haskellCons(this.export_Util.rightarrow()));
        } else {
            this.append(this.export_Util.haskellCons(this.export_Util.escape(this.createName(cons.getSymbol()))));
        }
        return cons;
    }

    @Override
    public HaskellObject caseVar(final Var var) {
        this.append(this.export_Util.haskellVar(this.export_Util.escape(this.createName(var.getSymbol()))));
        return var;
    }

    @Override
    public HaskellObject caseBindPat(final BindPat ho) {
        ho.getVariable().visit(this);
        this.atSign();
        this.prioStack.push(9);
        ho.getSubPattern().visit(this);
        this.prioStack.pop();
        return ho;
    }

    @Override
    public void fcaseIrrPat(final IrrPat ho) {
        this.irrSign();
        this.prioStack.push(9);
    }

    @Override
    public HaskellObject caseIrrPat(final IrrPat ho) {
        this.prioStack.pop();
        return ho;
    }

    @Override
    public HaskellObject caseJokerPat(final JokerPat ho) {
        this.joker();
        return ho;
    }

    @Override
    public HaskellObject casePlusPat(final PlusPat ho) {
        this.append("(");
        ho.getVariable().visit(this);
        this.append("+");
        ho.getInteger().visit(this);
        this.append(")");
        return ho;
    }

    @Override
    public void fcaseIfExp(final IfExp ho) {
        this.positions.push(0);
        this.prioStack.push(0);
        this.targets.push(new StringBuffer());
    }

    @Override
    public void icaseIfExp(final IfExp ho) {
        this.targets.push(new StringBuffer());
    }

    @Override
    public void iicaseIfExp(final IfExp ho) {
        this.targets.push(new StringBuffer());
    }

    @Override
    public HaskellObject caseIfExp(final IfExp ho) {
        this.positions.pop();
        this.prioStack.pop();
        this.buildIf(this.positions.peek() < 0, this.popTargets(3));
        return ho;
    }

    @Override
    public HaskellObject caseCharLit(final CharLit ho) {
        String text = ho.getCharValue() + "";
        if ((ho.getCharValue() <= ' ') || (ho.getCharValue() > '~')) {
            text = "\\" + ((int) ho.getCharValue());
        }
        this.append("'" + text + "'");
        return ho;
    }

    @Override
    public HaskellObject caseFloatLit(final FloatLit ho) {
        String val = ho.getFloatValue().toString();
        if (val.indexOf(".") < 0) {
            val += ".0";
        }
        this.append(val);
        return ho;
    }

    @Override
    public HaskellObject caseIntegerLit(final IntegerLit ho) {
        this.append("" + ho.getIntValue());
        return ho;
    }

    @Override
    public void fcaseLambdaExp(final LambdaExp ho) {
        if (this.positions.peek() < 0) {
            this.append("(");
        }
        this.positions.push(-2);
        this.prioStack.push(9);
        this.append(this.export_Util.backslash());
    }

    @Override
    public void icaseLambdaExp(final LambdaExp ho) {
        this.positions.pop();
        this.prioStack.pop();
        this.positions.push(0);
        this.prioStack.push(0);
        this.append(this.export_Util.rightarrow());
    }

    @Override
    public HaskellObject caseLambdaExp(final LambdaExp ho) {
        this.positions.pop();
        this.prioStack.pop();
        if (this.positions.peek() < 0) {
            this.append(")");
        }
        return ho;
    }

    @Override
    public void fcaseLetExp(final LetExp ho) {
        for (final HaskellEntity e : this.sortByName(ho.getEntityFrame().getCollectedEntities())) {
            this.targets.push(new StringBuffer());
            e.visit(this);
        }
        this.targets.push(new StringBuffer());
        this.positions.push(0);
        this.prioStack.push(0);
    }

    @Override
    public HaskellObject caseLetExp(final LetExp ho) {
        final StringBuffer res = this.targets.pop();
        this.positions.pop();
        this.prioStack.pop();
        if (ho.getMode() == 0) {
            this.buildLet(this.positions.peek() < 0,
                this.popTargets(ho.getEntityFrame().getCollectedEntities().size()), res);
        }
        if (ho.getMode() == 1) {
            this.buildWhere(this.popTargets(ho.getEntityFrame().getCollectedEntities().size()), res);
        }
        return ho;
    }

    public void buildLet(final boolean left, final List<StringBuffer> locals, final StringBuffer res) {
        if (left) {
            this.append("(");
        }
        this.append(this.export_Util.haskellLet(locals, res));
        if (left) {
            this.append(")");
        }
    }

    public void buildWhere(final List<StringBuffer> locals, final StringBuffer res) {
        this.append(this.export_Util.haskellWhere(locals, res));
    }

    public void buildIf(final boolean left, final List<StringBuffer> ts) {
        if (left) {
            this.append("(");
        }
        this.append(this.export_Util.haskellIf(ts.get(0), ts.get(1), ts.get(2)));
        if (left) {
            this.append(")");
        }
    }

    @Override
    public void fcaseAltExp(final AltExp ho) {
        this.targets.push(new StringBuffer());
    }

    @Override
    public void icaseAltExp(final AltExp ho) {
        this.targets.push(new StringBuffer());
    }

    @Override
    public HaskellObject caseAltExp(final AltExp ho) {
        if (ho.getExpression() instanceof CondStackExp) {
            return ho;
        } else {
            if (ho.getExpression() instanceof LetExp) {
                final LetExp le = (LetExp) ho.getExpression();
                if (le.getExpression() instanceof CondStackExp) {
                    return ho;
                }
            }
        }
        this.targets.push(new StringBuffer(this.export_Util.haskellNoCond(this.targets.pop(),
            this.export_Util.rightarrow())));
        return ho;
    }

    @Override
    public void fcaseCaseExp(final CaseExp ho) {
        this.arrows.push(this.export_Util.rightarrow());
        this.targets.push(new StringBuffer());
    }

    @Override
    public HaskellObject caseCaseExp(final CaseExp ho) {
        final List<Pair<StringBuffer, StringBuffer>> alts = new Vector<Pair<StringBuffer, StringBuffer>>();
        for (int i = 0; i < ho.getCases().size(); i++) {
            final StringBuffer r = this.targets.pop();
            final StringBuffer c = this.targets.pop();
            alts.add(0, new Pair<StringBuffer, StringBuffer>(c, r));
        }
        final StringBuffer arg = this.targets.pop();
        this.append(this.export_Util.haskellCase(arg, alts));
        this.arrows.pop();
        return ho;
    }

    @Override
    public void fcaseCondStackExp(final CondStackExp ho) {
        final List<Pair<StringBuffer, StringBuffer>> crs = new Vector<Pair<StringBuffer, StringBuffer>>();
        for (final CondExp ce : ho.getConditions()) {
            this.targets.push(new StringBuffer());
            ce.getCondition().visit(this);
            final StringBuffer c = this.targets.pop();
            this.targets.push(new StringBuffer());
            ce.getResult().visit(this);
            final StringBuffer r = this.targets.pop();
            crs.add(new Pair<StringBuffer, StringBuffer>(c, r));
        }
        this.append(this.export_Util.haskellCond(crs, this.arrows.peek()));
    }

    @Override
    public void fcaseEntity(final HaskellEntity ho) {
        if (ho instanceof VarEntity) {
            ho.getValue().visit(this);
        }
    }

    @Override
    public void fcaseFunction(final Function ho) {
        this.arrows.push("=");
        this.targets.push(new StringBuffer());
    }

    @Override
    public HaskellObject caseFunction(final Function ho) {
        final List<Pair<StringBuffer, StringBuffer>> rules = new Vector<Pair<StringBuffer, StringBuffer>>();
        for (int i = 0; i < ho.getRules().size(); i++) {
            final StringBuffer r = this.targets.pop();
            final StringBuffer c = this.targets.pop();
            rules.add(0, new Pair<StringBuffer, StringBuffer>(c, r));
        }
        final StringBuffer arg = this.targets.pop();
        this.append(this.export_Util.haskellRules(
            new StringBuffer(this.export_Util.haskellVar(this.createName(ho.getSymbol()))), rules));
        this.arrows.pop();
        return ho;
    }

    @Override
    public void fcaseHaskellRule(final HaskellRule ho) {
        this.targets.push(new StringBuffer());
        boolean first = true;
        this.prioStack.push(9);
        this.positions.push(-2);
        for (final HaskellObject pat : ho.getPatterns()) {
            if (!first) {
                this.append(this.export_Util.appSpace());
            }
            pat.visit(this);
            first = false;
        }
        this.positions.pop();
        this.prioStack.pop();
    }

    @Override
    public void icaseHaskellRule(final HaskellRule ho) {
        this.targets.push(new StringBuffer());
    }

    @Override
    public HaskellObject caseHaskellRule(final HaskellRule ho) {
        if (ho.getExpression() instanceof CondStackExp) {
            return ho;
        } else {
            if (ho.getExpression() instanceof LetExp) {
                final LetExp le = (LetExp) ho.getExpression();
                if (le.getExpression() instanceof CondStackExp) {
                    return ho;
                }
            }
        }
        this.targets.push(new StringBuffer(this.export_Util.haskellNoCond(this.targets.pop(), "=")));
        return ho;
    }

    @Override
    public boolean guardHaskellRulePatterns(final HaskellRule ho) {
        return false;
    }

    @Override
    public boolean guardPlusPat(final PlusPat ho) {
        return false;
    }

    @Override
    public boolean guardBindPat(final BindPat ho) {
        return false;
    }

    @Override
    public boolean guardTypeSchemaTypeExp(final TypeExp ho) {
        return false;
    }

    @Override
    public boolean guardTypeTypeExp(final TypeExp ho) {
        return false;
    }

    @Override
    public boolean guardLetFrame(final LetExp ho) {
        return false;
    }

    @Override
    public boolean guardCondStackConditions(final CondStackExp ho) {
        return false;
    }

    @Override
    public boolean guardEntities(final Module ho) {
        return false;
    }

    @Override
    public boolean guardValue(final HaskellEntity ho) {
        return false;
    }

    @Override
    public boolean guardType(final HaskellEntity ho) {
        return false;
    }

    public boolean guardFunctionRules(final Function ho) {
        return false;
    }

    public String applyTo(final HaskellObject ho) {
        ho.visit(this);
        return this.export_Util.math(this.target.toString());
    }
}
