package aprove.input.Programs.ipad;

import java.util.*;

import aprove.input.Generated.ipad.node.*;
import aprove.input.Programs.Predef.*;
import aprove.input.Programs.Predef.IntegerPredef.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

/** Treewalker that implements the statements-pass.
 *  <p>
 *  This pass picks up all procedure-declarations and transforms the
 *  statement-sequences into rules.
 *  </p>
 * @version $Id$
 * @author Christian Haselbach
 */

class StatementPass extends Pass {

    private Token curfuntoken;
    private String fname;
    private int stmtcount;
    private Stack<AlgebraTerm> terms;
    private ProcHead curProcHead;
    private Stack<Sort> sorts;
    private ConstructorSymbol curconstr;
    private int selectorindex;
    private Vector<DefFunctionSymbol> curselectors;
    private Hashtable callReferences;

    private Stack<AlgebraTerm> expectedTypes;

    private String getAVariableName(final int i) {
        String s = null;
        switch (i % 6) {
        case 0:
            s = "x";
            break;
        case 1:
            s = "y";
            break;
        case 2:
            s = "z";
            break;
        case 3:
            s = "u";
            break;
        case 4:
            s = "v";
            break;
        case 5:
            s = "w";
            break;
        }
        return (i < 6) ? s : s + (i / 6);
    }

    @Override
    public void inStart(final Start node) {
        this.terms = new Stack<AlgebraTerm>();
        this.sorts = new Stack<Sort>();
        this.callReferences = new Hashtable();

        this.expectedTypes = new Stack<AlgebraTerm>();
    }

    @Override
    public void caseAStruct(final AStruct node) {
        final Iterator it = node.getConstr().iterator();
        while (it.hasNext()) {
            ((PConstr) it.next()).apply(this);
        }
    }

    @Override
    public void inAConstr(final AConstr node) {
        this.curconstr = this.prog.getConstructorSymbol(this.chop(node.getCons()));
        this.curselectors = new Vector<DefFunctionSymbol>();
        this.selectorindex = 0;
    }

    @Override
    public void outAConstr(final AConstr node) {
        this.curconstr.setSelectors(this.curselectors);
    }

    @Override
    public void caseAIdcomma(final AIdcomma node) {
        this.makeSelector(node.getSelector());
    }

    @Override
    public void caseAIdlist(final AIdlist node) {
        if (node.getIdcomma() != null) {
            final Iterator it = node.getIdcomma().iterator();
            while (it.hasNext()) {
                ((AIdcomma) it.next()).apply(this);
            }
        }
        this.makeSelector(node.getSelector());
    }

    private void makeSelector(final Token t) {
        final String name = this.chop(t);
        final DefFunctionSymbol def =
            DefFunctionSymbol.create(name, new Vector<Sort>(), this.curconstr.getArgSort(this.selectorindex));
        def.addArgSort(this.curconstr.getSort());
        // selectors are terminating by construction
        def.setTermination(true);
        try {
            this.prog.addPredefFunctionSymbol(def);
            this.prog.setFunctionSignature(def, Symbol.SELECTORSIG);
            this.curselectors.add(def);
            final Type ct = this.typeContext.getSingleTypeOf(this.curconstr);
            this.typeContext.setSingleTypeOf(def, ct.createSelType(this.selectorindex));
        } catch (final Exception e) {
        }
        final AlgebraTerm witness = (AlgebraTerm) this.witnessTerms.get(this.curconstr.getArgSort(this.selectorindex).getName());
        final Iterator it = this.curconstr.getSort().getConstructorSymbols().iterator();
        while (it.hasNext()) {
            final ConstructorSymbol conssym = (ConstructorSymbol) it.next();
            final List<AlgebraTerm> tl = new Vector<AlgebraTerm>();
            final Iterator s_it = conssym.getArgSorts().iterator();
            int i = 0;
            while (s_it.hasNext()) {
                final Sort s = (Sort) s_it.next();
                tl.add(AlgebraVariable.create(VariableSymbol.create(this.getAVariableName(i++), s)));
            }
            final List<AlgebraTerm> f = new Vector<AlgebraTerm>();
            f.add(ConstructorApp.create(conssym, tl));
            AlgebraTerm tr;
            if (conssym.equals(this.curconstr)) {
                tr = tl.get(this.selectorindex);
            } else {
                tr = witness;
            }
            this.prog.addRule(Rule.create(AlgebraFunctionApplication.create(def, f), tr));
        }
        this.selectorindex++;
    }

    @Override
    public void caseAFunct(final AFunct node) {
        this.stmtcount = 0;
        this.curfuntoken = node.getFunctname();
        this.fname = this.chop(this.curfuntoken);
        this.curProcHead = (ProcHead) this.procHeads.get(this.fname);
        final ProcHead ph = this.curProcHead;
        this.curProcHead = ph.copy();
        List<AlgebraTerm> args;
        if (ph.getSort() != null) {
            this.curProcHead.addVar("#_v", ph.getRetTy(), ph.getSort(), ProcHead.INTERNALVAR);
            args = new Vector<AlgebraTerm>(ph.getArgs());
            args.add((AlgebraTerm) this.witnessTerms.get(ph.getSort().getName()));
        } else {
            args = this.curProcHead.getArgs();
        }
        node.getStatementlist().apply(this);
        // for every cbr-variable add a corresponding function
        final Iterator it = ph.getRefVars().iterator();
        while (it.hasNext()) {
            final VariableSymbol sym = (VariableSymbol) it.next();
            final DefFunctionSymbol def1 = this.prog.getDefFunctionSymbol(this.fname + "_" + sym.getName());
            final AlgebraFunctionApplication f1 = AlgebraFunctionApplication.create(def1, ph.getArgs());
            final DefFunctionSymbol def2 =
                this.prog.getDefFunctionSymbol(this.fname + "^" + this.stmtcount + "_" + sym.getName());
            final AlgebraFunctionApplication f2 = AlgebraFunctionApplication.create(def2, args);
            this.prog.addRule(Rule.create(f1, f2));
        }
        // if this function has a result-type (non-void) add a corresponding function
        final Sort returnSort = this.curProcHead.getSort();
        if (returnSort != null) {
            final DefFunctionSymbol def1 = this.prog.getDefFunctionSymbol(this.fname);
            final AlgebraFunctionApplication f1 = AlgebraFunctionApplication.create(def1, ph.getArgs());
            final DefFunctionSymbol def2 = this.prog.getDefFunctionSymbol(this.fname + "^" + this.stmtcount + "_#_v");
            final AlgebraFunctionApplication f2 = AlgebraFunctionApplication.create(def2, args);
            this.prog.addRule(Rule.create(f1, f2));
        }
    }

    // Statements

    @Override
    public void caseAAssignSimpleStatement(final AAssignSimpleStatement node) {
        final String var = this.chop(node.getId());
        final AType type = (AType) node.getType();
        final ProcHead ph = this.curProcHead;
        VariableSymbol sym;
        AlgebraTerm symType = null;
        if (type != null) {
            final String name = this.chop(type.getId());
            final AlgebraTerm cty = this.getDeclaredType(name, type.getId());
            final Sort s = this.prog.getSort(name);

            // check type definition based on Type Context
            if (cty == null) {
                this.addParseError(node.getId(), "Unknown type ''" + this.chop(type.getId()) + "''");
                return;
            }

            // TODO remove me
            if (s == null) {
                this.addParseError(node.getId(), "Unknown sort ''" + this.chop(type.getId()) + "''");
                return;
            }

            this.curProcHead = ph.copy();
            sym = this.curProcHead.addVar(var, cty, s, ProcHead.INTERNALVAR);
            if (sym == null) {
                this.addParseError(node.getId(), "variable ''" + var + "'' is multiple defined");
            }

            symType = cty;
        } else {
            sym = this.curProcHead.getVariableSymbol(var);
            symType = this.curProcHead.getVariableSymbolType(var);
        }
        if (sym == null) {
            this.addParseError(node.getId(), "Undeclared variable ''" + var + "''");
            final Sort s = this.prog.getSort("bool");
            final AlgebraTerm cty = this.getDeclaredType("bool", null);
            this.curProcHead = ph.copy();
            sym = this.curProcHead.addVar(var, cty, s, ProcHead.INTERNALVAR);
        }

        this.expectedTypes.clear();
        this.expectedTypes.push(symType);

        // TODO remove me
        this.sorts.clear();
        this.sorts.push(sym.getSort());

        this.terms.clear();
        this.callReferences.clear();
        node.getTerm().apply(this);
        final AlgebraTerm assignterm = this.terms.pop();
        if (this.allFunctionsAreTerminating(assignterm)) {
            this.stmtcount++;
            final Iterator it = this.curProcHead.getVars().iterator();
            final Iterator jt = this.curProcHead.getFunArgTys().iterator();
            while (it.hasNext()) {
                final VariableSymbol argsym = (VariableSymbol) it.next();
                final AlgebraTerm cRetTy = (AlgebraTerm) jt.next();
                final DefFunctionSymbol def =
                    DefFunctionSymbol.create(this.fname + "^" + this.stmtcount + "_" + argsym.getName(),
                        new Vector<Sort>(ph.getFunArgSorts()), argsym.getSort());

                final AlgebraFunctionApplication f = AlgebraFunctionApplication.create(def, ph.getArgs());
                try {
                    this.prog.addDefFunctionSymbol(def);
                    final AlgebraTerm ct = TypeTools.function(ph.getFunArgTys(), cRetTy);
                    this.typeContext.setSingleTypeOf(def, TypeTools.autoQuan(ct));
                } catch (final Exception e) {
                }
                Rule r;
                if (sym.equals(argsym)) {
                    r = Rule.create(f, assignterm);
                } else {
                    final AlgebraTerm t = (AlgebraTerm) this.callReferences.get(argsym);
                    if (t != null) {
                        r = Rule.create(f, t);
                    } else {
                        r = Rule.create(f, AlgebraVariable.create(argsym));
                    }
                }
                this.prog.addRule(def, r);
            }
        } else {
            this.makeSkip();
            final int skipstmtnr = this.stmtcount++;
            final Iterator it = this.curProcHead.getVars().iterator();
            final Iterator jt = this.curProcHead.getFunArgTys().iterator();
            while (it.hasNext()) {
                final VariableSymbol argsym = (VariableSymbol) it.next();
                final AlgebraTerm cRetTy = (AlgebraTerm) jt.next();
                final DefFunctionSymbol defl =
                    DefFunctionSymbol.create(this.fname + "^" + this.stmtcount + "_" + argsym.getName(),
                        new Vector<Sort>(ph.getFunArgSorts()), argsym.getSort());
                try {
                    this.prog.addDefFunctionSymbol(defl);
                    final AlgebraTerm ct = TypeTools.function(ph.getFunArgTys(), cRetTy);
                    this.typeContext.setSingleTypeOf(defl, TypeTools.autoQuan(ct));
                } catch (final Exception e) {
                }
                final AlgebraTerm left = AlgebraFunctionApplication.create(defl, ph.getArgs());
                final DefFunctionSymbol defr =
                    this.prog.getDefFunctionSymbol(this.fname + "^" + skipstmtnr + "_" + argsym.getName());
                final Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
                final Iterator a_it = this.curProcHead.getArgs().iterator();
                while (a_it.hasNext()) {
                    final AlgebraTerm arg = (AlgebraTerm) a_it.next();
                    if (arg.getSymbol().equals(sym)) {
                        args.add(assignterm.shallowcopy());
                    } else {
                        final AlgebraTerm t = (AlgebraTerm) this.callReferences.get(argsym);
                        if (t != null) {
                            args.add(t.shallowcopy());
                        } else {
                            args.add(arg.shallowcopy());
                        }
                    }
                }
                final AlgebraTerm right = AlgebraFunctionApplication.create(defr, args);
                this.prog.addRule(defl, Rule.create(left, right));
            }
        }
    }

    @Override
    public void caseAIfthenelseStatement(final AIfthenelseStatement node) {
        this.terms.clear();

        this.expectedTypes.clear();
        this.expectedTypes.push(this.typeContext.getTypeDef("bool").getDefTerm());

        // TODO remove me
        this.sorts.clear();
        this.sorts.push(this.prog.getSort("bool"));

        node.getCondstmt().apply(this);
        final AlgebraTerm cond = this.terms.pop();
        final int condnr = this.stmtcount;
        node.getThenstmt().apply(this);
        final int thennr = this.stmtcount;
        node.getElsestmt().apply(this);
        final int elsenr = this.stmtcount;
        this.stmtcount++;
        final Iterator it = this.curProcHead.getVars().iterator();
        final Iterator jt = this.curProcHead.getFunArgTys().iterator();
        while (it.hasNext()) {
            final VariableSymbol argsym = (VariableSymbol) it.next();
            final AlgebraTerm cRetTy = (AlgebraTerm) jt.next();
            final DefFunctionSymbol def =
                DefFunctionSymbol.create(this.fname + "^" + this.stmtcount + "_" + argsym.getName(), new Vector<Sort>(
                    this.curProcHead.getFunArgSorts()), argsym.getSort());
            final AlgebraFunctionApplication f = AlgebraFunctionApplication.create(def, this.curProcHead.getArgs());
            try {
                this.prog.addDefFunctionSymbol(def);
                final AlgebraTerm ct = TypeTools.function(this.curProcHead.getFunArgTys(), cRetTy);
                this.typeContext.setSingleTypeOf(def, TypeTools.autoQuan(ct));
            } catch (final Exception e) {
            }
            final DefFunctionSymbol defthen =
                this.prog.getDefFunctionSymbol(this.fname + "^" + thennr + "_" + argsym.getName());
            final DefFunctionSymbol defelse =
                this.prog.getDefFunctionSymbol(this.fname + "^" + elsenr + "_" + argsym.getName());
            final Vector<Rule> cotrue = new Vector<Rule>();
            cotrue.add(Rule.create(cond, AlgebraFunctionApplication.create((SyntacticFunctionSymbol) this.prog.getSymbol("true"))));
            final Vector<Rule> cofalse = new Vector<Rule>();
            cofalse.add(Rule.create(cond, AlgebraFunctionApplication.create((SyntacticFunctionSymbol) this.prog.getSymbol("false"))));
            this.prog.addRule(def,
                Rule.create(cotrue, f, AlgebraFunctionApplication.create(defthen, this.curProcHead.getArgs())));
            this.prog.addRule(def,
                Rule.create(cofalse, f, AlgebraFunctionApplication.create(defelse, this.curProcHead.getArgs())));
        }
    }

    @Override
    public void caseAIfthenStatement(final AIfthenStatement node) {
        this.terms.clear();

        this.expectedTypes.clear();
        this.expectedTypes.push(this.typeContext.getTypeDef("bool").getDefTerm());

        // TODO remove me
        this.sorts.clear();
        this.sorts.push(this.prog.getSort("bool"));

        node.getCondstmt().apply(this);
        final AlgebraTerm cond = this.terms.pop();
        final int condnr = this.stmtcount;
        node.getThenstmt().apply(this);
        final int thennr = this.stmtcount;
        this.stmtcount++;
        final Iterator it = this.curProcHead.getVars().iterator();
        final Iterator jt = this.curProcHead.getFunArgTys().iterator();
        while (it.hasNext()) {
            final VariableSymbol argsym = (VariableSymbol) it.next();
            final AlgebraTerm cRetTy = (AlgebraTerm) jt.next();
            final DefFunctionSymbol def =
                DefFunctionSymbol.create(this.fname + "^" + this.stmtcount + "_" + argsym.getName(), new Vector<Sort>(
                    this.curProcHead.getFunArgSorts()), argsym.getSort());
            final AlgebraFunctionApplication f = AlgebraFunctionApplication.create(def, this.curProcHead.getArgs());
            try {
                this.prog.addDefFunctionSymbol(def);
                final AlgebraTerm ct = TypeTools.function(this.curProcHead.getFunArgTys(), cRetTy);
                this.typeContext.setSingleTypeOf(def, TypeTools.autoQuan(ct));
            } catch (final Exception e) {
            }
            final DefFunctionSymbol defthen =
                this.prog.getDefFunctionSymbol(this.fname + "^" + thennr + "_" + argsym.getName());
            final Vector<Rule> cotrue = new Vector<Rule>();
            cotrue.add(Rule.create(cond, AlgebraFunctionApplication.create((SyntacticFunctionSymbol) this.prog.getSymbol("true"))));
            final Vector<Rule> cofalse = new Vector<Rule>();
            cofalse.add(Rule.create(cond, AlgebraFunctionApplication.create((SyntacticFunctionSymbol) this.prog.getSymbol("false"))));
            this.prog.addRule(def,
                Rule.create(cotrue, f, AlgebraFunctionApplication.create(defthen, this.curProcHead.getArgs())));
            this.prog.addRule(def, Rule.create(cofalse, f, AlgebraVariable.create(argsym)));
        }
    }

    @Override
    public void caseACallSimpleStatement(final ACallSimpleStatement node) {
        final TId id = node.getId();
        final String name = this.chop(id);
        final ProcHead callProcHead = (ProcHead) this.procHeads.get(name);
        final PTermlist termlist = node.getTermlist();
        final int size = ((ATermlist) termlist).getCommaterm().size() + 1;
        if (callProcHead.getArity() != size) {
            this.addParseError(id, "expected " + Integer.valueOf(callProcHead.getArity()).toString() + " parameters, not "
                + Integer.valueOf(size).toString());
            return;
        }
        this.callReferences.clear();

        this.expectedTypes.clear();
        for (int i = size - 1; i >= 0; --i) {
            this.expectedTypes.push(callProcHead.getFunArgTys().get(i));
        }

        // TODO remove me
        this.sorts.clear();
        for (int i = size - 1; i >= 0; i--) {
            this.sorts.push(callProcHead.getArgSort(i));
        }

        this.callReferences.clear();
        this.terms.clear();
        termlist.apply(this);
        this.addArguments(id, null, name, size);
        final ProcHead ph = this.curProcHead;
        this.makeSkip();
        final int skipstmtnr = this.stmtcount++;
        final Iterator it = this.curProcHead.getVars().iterator();
        final Iterator jt = this.curProcHead.getFunArgTys().iterator();
        while (it.hasNext()) {
            final VariableSymbol argsym = (VariableSymbol) it.next();
            final AlgebraTerm cRetTy = (AlgebraTerm) jt.next();
            final DefFunctionSymbol defl =
                DefFunctionSymbol.create(this.fname + "^" + this.stmtcount + "_" + argsym.getName(), new Vector<Sort>(
                    ph.getFunArgSorts()), argsym.getSort());
            try {
                this.prog.addDefFunctionSymbol(defl);
                final AlgebraTerm ct = TypeTools.function(ph.getFunArgTys(), cRetTy);
                this.typeContext.setSingleTypeOf(defl, TypeTools.autoQuan(ct));
            } catch (final Exception e) {
            }
            final AlgebraTerm left = AlgebraFunctionApplication.create(defl, ph.getArgs());
            final DefFunctionSymbol defr =
                this.prog.getDefFunctionSymbol(this.fname + "^" + skipstmtnr + "_" + argsym.getName());
            final Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
            final Iterator a_it = this.curProcHead.getArgs().iterator();
            while (a_it.hasNext()) {
                final AlgebraTerm arg = (AlgebraTerm) a_it.next();
                final AlgebraTerm t = (AlgebraTerm) this.callReferences.get(arg.getSymbol());
                if (t != null) {
                    args.add(t.shallowcopy());
                } else {
                    args.add(arg.shallowcopy());
                }
            }
            final AlgebraTerm right = AlgebraFunctionApplication.create(defr, args);
            this.prog.addRule(defl, Rule.create(left, right));
        }
    }

    @Override
    public void caseASkipSimpleStatement(final ASkipSimpleStatement node) {
        this.makeSkip();
    }

    @Override
    public void caseAWhileStatement(final AWhileStatement node) {
        this.terms.clear();

        this.expectedTypes.clear();
        this.expectedTypes.push(this.typeContext.getTypeDef("bool").getDefTerm());

        // TODO remove me
        this.sorts.clear();
        this.sorts.push(this.prog.getSort("bool"));

        this.callReferences.clear();
        node.getTerm().apply(this);
        final Hashtable myReferences = new Hashtable(this.callReferences);
        final int condnr = this.stmtcount;
        final AlgebraTerm cond = this.terms.pop();
        node.getStatementlist().apply(this);
        // Create the argument-list for f^while b do S od
        final List<AlgebraTerm> tl = new Vector<AlgebraTerm>();
        Iterator it = this.curProcHead.getVars().iterator();
        while (it.hasNext()) {
            final VariableSymbol sym = (VariableSymbol) it.next();
            final DefFunctionSymbol defS =
                this.prog.getDefFunctionSymbol(this.fname + "^" + this.stmtcount + "_" + sym.getName());
            final Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
            final Iterator a_it = this.curProcHead.getArgs().iterator();
            while (a_it.hasNext()) {
                final AlgebraTerm arg = (AlgebraTerm) a_it.next();
                final AlgebraTerm t = (AlgebraTerm) myReferences.get(arg.getSymbol());
                if (t != null) {
                    args.add(t.shallowcopy());
                } else {
                    args.add(arg.shallowcopy());
                }
            }
            tl.add(AlgebraFunctionApplication.create(defS, args));
        }
        final Vector<Rule> cotrue = new Vector<Rule>();
        cotrue.add(Rule.create(cond, AlgebraFunctionApplication.create((SyntacticFunctionSymbol) this.prog.getSymbol("true"))));
        final Vector<Rule> cofalse = new Vector<Rule>();
        cofalse.add(Rule.create(cond, AlgebraFunctionApplication.create((SyntacticFunctionSymbol) this.prog.getSymbol("false"))));
        // Add the new defining funtion-symbols to the program.
        this.stmtcount++;
        it = this.curProcHead.getVars().iterator();
        final Iterator jt = this.curProcHead.getFunArgTys().iterator();
        while (it.hasNext()) {
            final VariableSymbol sym = (VariableSymbol) it.next();
            final AlgebraTerm cRetTy = (AlgebraTerm) jt.next();
            final DefFunctionSymbol def =
                DefFunctionSymbol.create(this.fname + "^" + this.stmtcount + "_" + sym.getName(), new Vector<Sort>(
                    this.curProcHead.getFunArgSorts()), sym.getSort());
            try {
                this.prog.addDefFunctionSymbol(def);
                final AlgebraTerm ct = TypeTools.function(this.curProcHead.getFunArgTys(), cRetTy);
                this.typeContext.setSingleTypeOf(def, TypeTools.autoQuan(ct));
            } catch (final Exception e) {
            }
            final AlgebraFunctionApplication f1 = AlgebraFunctionApplication.create(def, this.curProcHead.getArgs());
            final AlgebraFunctionApplication f2 = AlgebraFunctionApplication.create(def, tl);
            this.prog.addRule(Rule.create(cotrue, f1, f2));
            this.prog.addRule(Rule.create(cofalse, f1, AlgebraVariable.create(sym)));
        }
    }

    @Override
    public void caseANeStatementlist(final ANeStatementlist node) {
        final ProcHead ph = this.curProcHead;
        this.curProcHead = ph.copy();
        // Handle current statement.
        node.getStatement().apply(this);
        final int stmtnr = this.stmtcount;
        if (node.getNeStatementlist() == null) {
            this.curProcHead = ph;
            return;
        }
        // Handle remaining statementlist.
        node.getNeStatementlist().apply(this);
        final List<AlgebraTerm> arguments = new Vector<AlgebraTerm>();
        Iterator var_it = this.curProcHead.getVars().iterator();
        while (var_it.hasNext()) {
            final VariableSymbol argsym = (VariableSymbol) var_it.next();
            final DefFunctionSymbol def1 =
                this.prog.getDefFunctionSymbol(this.fname + "^" + stmtnr + "_" + argsym.getName());
            arguments.add(AlgebraFunctionApplication.create(def1, ph.getArgs()));
        }
        final int stmtlistnr = this.stmtcount;
        this.stmtcount++;
        // Merge statement and satementlist.
        var_it = ph.getVars().iterator();
        final Iterator jt = this.curProcHead.getFunArgTys().iterator();
        while (var_it.hasNext()) {
            final VariableSymbol argsym = (VariableSymbol) var_it.next();
            final AlgebraTerm cRetTy = (AlgebraTerm) jt.next();
            final DefFunctionSymbol def2 =
                this.prog.getDefFunctionSymbol(this.fname + "^" + stmtlistnr + "_" + argsym.getName());
            final AlgebraTerm fr = AlgebraFunctionApplication.create(def2, arguments).shallowcopy();
            final DefFunctionSymbol def =
                DefFunctionSymbol.create(this.fname + "^" + this.stmtcount + "_" + argsym.getName(), new Vector<Sort>(
                    ph.getFunArgSorts()), argsym.getSort());
            try {
                this.prog.addDefFunctionSymbol(def);
                final AlgebraTerm ct = TypeTools.function(ph.getFunArgTys(), cRetTy);
                this.typeContext.setSingleTypeOf(def, TypeTools.autoQuan(ct));
            } catch (final Exception e) {
            }
            final AlgebraFunctionApplication fl = AlgebraFunctionApplication.create(def, ph.getArgs());
            this.prog.addRule(Rule.create(fl, fr));
        }
        this.curProcHead = ph;
    }

    // Statement-helpers

    private void makeSkip() {
        this.stmtcount++;
        final Iterator it = this.curProcHead.getVars().iterator();
        final Iterator jt = this.curProcHead.getFunArgTys().iterator();
        while (it.hasNext()) {
            final VariableSymbol sym = (VariableSymbol) it.next();
            final AlgebraTerm cRetTy = (AlgebraTerm) jt.next();
            final DefFunctionSymbol def =
                DefFunctionSymbol.create(this.fname + "^" + this.stmtcount + "_" + sym.getName(), new Vector<Sort>(
                    this.curProcHead.getFunArgSorts()), sym.getSort());
            final AlgebraFunctionApplication f = AlgebraFunctionApplication.create(def, this.curProcHead.getArgs());
            try {
                this.prog.addDefFunctionSymbol(def);
                final AlgebraTerm ct = TypeTools.function(this.curProcHead.getFunArgTys(), cRetTy);
                this.typeContext.setSingleTypeOf(def, TypeTools.autoQuan(ct));
            } catch (final Exception e) {
            }
            this.prog.addRule(Rule.create(f, AlgebraVariable.create(sym)));
        }
    }

    // Terms

    @Override
    public void caseAOperatorAppTerm(final AOperatorAppTerm node) {
        final Token id = node.getInfixid();
        final PSterm left = node.getLeft();
        final PTerm right = node.getRight();
        if (this.chop(id).equals("==")) {
            this.caseADequalTerm(id, left, right);
        } else if (this.chop(id).equals("~")) {
            this.caseAIsATerm(id, left, right);
        } else {
            this.caseAGeneralOperatorTerm(id, left, right);
        }
    }

    public void caseADequalTerm(final Token id, final PSterm left, final PTerm right) {

        AlgebraTerm expectedType = this.expectedTypes.pop();
        final AlgebraTerm boolType = this.typeContext.getTypeDef("bool").getDefTerm();
        if (!this.checkTypes(boolType, expectedType, id)) {
            this.pushdummyterm(Sort.create(expectedType.getSymbol().getName()));
            return;
        }

        // TODO remove me
        Sort s = this.sorts.pop();
        final Sort bool = this.prog.getSort("bool");
        //    if (!checksorts(bool, s, id)) {
        //        this.pushdummyterm(s);
        //        return;
        //    }

        // processing the lhs of equal will determine the type/sort of the rhs
        this.expectedTypes.push(Pass.ANY_TYPE);
        this.sorts.push(Pass.ANY_SORT);

        left.apply(this);

        final Symbol sym = this.terms.peek().getSymbol();
        s = sym.getSort();
        expectedType = null;
        if (sym instanceof VariableSymbol) {
            expectedType = this.curProcHead.getVariableSymbolType(sym.getName());
        } else {
            expectedType = this.typeContext.getSingleTypeOf(sym).getTypeMatrix();
            expectedType = TypeTools.getResultTerm(expectedType);
        }

        this.expectedTypes.push(expectedType);

        // TODO remove me
        this.sorts.push(s);

        right.apply(this);

        //        FunctionSymbol f = prog.getPredefFunctionSymbol("equal_"+s.getName());
        final String typeName = expectedType.getSymbol().getName();
        final SyntacticFunctionSymbol f = this.prog.getPredefFunctionSymbol("equal_" + typeName);
        if (f == null) {
            this.addParseError(id, "internal error: ''equal_" + typeName + "'' not found!");
        } else {
            try {
                this.prog.activatePredefFunctionSymbol(f.getName());
            } catch (final ProgramException e) {
                this.addParseError(id, e.getMessage());
            }
            this.addArguments(id, f, 2);
        }
    }

    public void caseAIsATerm(final Token id, final PSterm left, final PTerm right) {

        final AlgebraTerm expectedType = this.expectedTypes.pop();
        final AlgebraTerm boolType = this.typeContext.getTypeDef("bool").getDefTerm();
        if (!this.checkTypes(boolType, expectedType, id)) {
            this.pushdummyterm(Sort.create(expectedType.getSymbol().getName()));
            return;
        }

        // TODO remove me
        final Sort s = this.sorts.pop();
        final Sort bool = this.prog.getSort("bool");
        //    if (!checksorts(bool, s, id)) {
        //        this.pushdummyterm(s);
        //        return;
        //    }

        TId cid = null;
        try {
            final PSterm sterm = ((AStermTerm) right).getSterm();
            cid = ((AConstVarSterm) sterm).getId();
        } catch (final Exception e) {
            this.addParseError(id, "expected a constructor");
            this.pushdummyterm(bool);
            return;
        }
        final ConstructorSymbol csym = this.prog.getConstructorSymbol(this.chop(cid));
        if (csym == null) {
            this.addParseError(cid, "unknown constructor");
            this.pushdummyterm(bool);
            return;
        }
        this.expectedTypes.push(TypeTools.getResultTerm(this.typeContext.getSingleTypeOf(csym).getTypeMatrix()));

        // TODO remove me
        this.sorts.push(csym.getSort());

        left.apply(this);
        final DefFunctionSymbol f = this.prog.getPredefFunctionSymbol("isa_" + csym.getName());
        if (f == null) {
            this.addParseError(id, "internal error: ''isa_" + csym.getName() + "'' not found!");
        } else {
            try {
                this.prog.activatePredefFunctionSymbol(f.getName());
            } catch (final ProgramException e) {
                this.addParseError(id, e.getMessage());
            }
            this.addArguments(id, f, 1);
        }
    }

    public void caseAGeneralOperatorTerm(final Token id, final PSterm left, final PTerm right) {
        String name = this.chop(id);

        final AlgebraTerm expectedType = this.expectedTypes.pop();

        final Sort s = this.sorts.pop();

        final List<String> intPredefs = Arrays.asList("+", "-", "*", "/", "<", "<=", ">", ">=", "%");

        final int predefIndex = intPredefs.indexOf(name);

        if (predefIndex >= 0) {

            final Sort intSort = this.prog.getSort(AbstractIntegerPredefItem.getIntTypeName());
            this.sorts.push(intSort);

            this.expectedTypes.push(IntegerTools.getIntType(this.typeContext));
            left.apply(this);
            final AlgebraTerm l = this.terms.pop();

            this.sorts.push(intSort);
            this.expectedTypes.push(IntegerTools.getIntType(this.typeContext));
            right.apply(this);
            final AlgebraTerm r = this.terms.pop();

            AlgebraTerm funcAppTerm = null;

            switch (predefIndex) {

            case 0: // "+"
                funcAppTerm = (new IntegerPlusPredef(name, this.typeContext, this.prog, l, r)).toTerm();
                break;

            case 1: // "-"
                funcAppTerm = (new IntegerMinusPredef(name, this.typeContext, this.prog, l, r)).toTerm();
                break;

            case 2: // "*"
                funcAppTerm = (new IntegerMultPredef(name, this.typeContext, this.prog, l, r)).toTerm();
                break;

            case 3: // "/"
                funcAppTerm = (new IntegerQuotPredef(name, this.typeContext, this.prog, l, r)).toTerm();
                break;

            case 4: // "<"
            case 5: // "<="
                funcAppTerm = (new IntegerLessEqPredef(name, this.typeContext, this.prog, l, r)).toTerm();
                break;

            case 6: // ">"
            case 7: // ">="
                funcAppTerm = (new IntegerGreaterEqPredef(name, this.typeContext, this.prog, l, r)).toTerm();
                break;

            case 8: // "%"
                funcAppTerm = (new IntegerModPredef(name, this.typeContext, this.prog, l, r)).toTerm();
                break;

            default: // ERROR: unknown operator
                this.addParseError(id, "Internal Error: Integer predefined operator expected, but ,," + name
                    + "'' is not handled.");
                return;
            }

            // check whether the result type was expected
            final AlgebraTerm resultType =
                TypeTools.getResultTerm(this.typeContext.getSingleTypeOf(funcAppTerm.getSymbol()).getTypeMatrix());
            if (!this.checkTypes(expectedType, resultType, id)) {
                return;
            }

            this.terms.add(funcAppTerm);
            return;
        }

        if (name.equals("&&")) {
            name = "and";
        } else if (name.equals("||")) {
            name = "or";
        } else {
            this.addParseError(id, "Unknown operator ''" + name + "''");
            this.pushdummyterm(s);
            return;
        }
        SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(name);
        if (f == null) {
            f = this.prog.getPredefFunctionSymbol(name);
            if (f == null) {
                this.addParseError(id, "undeclared operator ''" + this.chop(id) + "''");
                //        this.pushdummyterm(s);
                this.pushdummyterm(Sort.create(expectedType.getSymbol().getName()));
                return;
            }
            try {
                this.prog.activatePredefFunctionSymbol(f.getName());
            } catch (final Exception e) {
                this.addParseError(id, e.getMessage());
            }
        }
        //    if (!checksorts(s, f.getSort(), id)) {
        final AlgebraTerm fTypeM = this.typeContext.getSingleTypeOf(f).getTypeMatrix();
        final AlgebraTerm fResType = TypeTools.getResultTerm(fTypeM);
        if (!this.checkTypes(expectedType, fResType, id)) {
            //        this.addParseError(id, "''"+id+"'' has got sort ''"+f.getSort().getName()+
            //            "'', but ''"+s.getName()+"'' expected.");
            //        this.pushdummyterm(s);
            this.addParseError(id, "''" + id + "'' has got sort ''" + fResType.getSymbol().getName() + "'', but ''"
                + expectedType.getSymbol().getName() + "'' expected.");
            this.pushdummyterm(Sort.create(expectedType.getSymbol().getName()));
            return;
        }
        // TODO remove me
        this.sorts.push(f.getArgSort(0));

        this.expectedTypes.push(TypeTools.getFunctionArgAt(fTypeM, 0));
        left.apply(this);
        final AlgebraTerm l = this.terms.pop();

        // TODO remove me
        this.sorts.push(f.getArgSort(1));

        this.expectedTypes.push(TypeTools.getFunctionArgAt(fTypeM, 1));
        right.apply(this);
        final AlgebraTerm r = this.terms.pop();
        final List<AlgebraTerm> tl = new Vector<AlgebraTerm>();
        tl.add(l);
        tl.add(r);
        this.terms.add(AlgebraFunctionApplication.create(f, tl));
    }

    @Override
    public void caseAFunctAppSterm(final AFunctAppSterm node) {
        final TId id = node.getId();
        String name = this.chop(id);
        if (name.equals("!")) {
            name = "not";
        }

        final AlgebraTerm expectedType = this.expectedTypes.pop();

        // TODO remove me
        final Sort s = this.sorts.pop();

        final PTermlist termlist = node.getTermlist();
        final int size = ((ATermlist) termlist).getCommaterm().size() + 1;
        SyntacticFunctionSymbol f = this.prog.getFunctionSymbol(name);
        if (f == null) {
            f = this.prog.getPredefFunctionSymbol(name);
            if (f == null) {
                this.addParseError(id, "undeclared function or constructor ''" + this.chop(id) + "''");
                //        this.pushdummyterm(s);
                this.pushdummyterm(Sort.create(expectedType.getSymbol().getName()));
                return;
            }
            try {
                this.prog.activatePredefFunctionSymbol(f.getName());
            } catch (final Exception e) {
                this.addParseError(id, e.getMessage());
            }
        }

        if (PredefDataStructureSymbols.isPredefinedSymbol(f)) {
            this.addParseError(id, "you are not allowed to use the predefined data structure symbol ''" + f.getName()
                + "''.");
            this.pushdummyterm(Sort.create(expectedType.getSymbol().getName()));
            return;
        }

        final Type fType = this.typeContext.getSingleTypeOf(f);

        if (fType == null) {
            this.addParseError(node.getId(), "no type found for symbol " + f.getName());
        }

        final AlgebraTerm fTypeM = this.typeContext.getSingleTypeOf(f).getTypeMatrix();

        if (!this.checkTypes(expectedType, TypeTools.getResultTerm(fTypeM), id)) {
            this.pushdummyterm(Sort.create(expectedType.getSymbol().getName()));
            return;
        }

        // TODO remove me
        if (!this.checksorts(s, f.getSort(), id)) {
            this.pushdummyterm(s);
            return;
        }

        // TODO remove me
        for (int i = f.getArity() - 1; i >= 0; i--) {
            this.sorts.push(f.getArgSort(i));
        }

        for (int i = f.getArity() - 1; i >= 0; --i) {
            this.expectedTypes.push(TypeTools.getFunctionArgAt(fTypeM, i));
        }

        if (f.getArity() != size) {
            this.addParseError(id, "expected " + Integer.valueOf(f.getArity()).toString() + " parameters, not "
                + Integer.valueOf(size).toString());
            //        this.pushdummyterm(s);
            this.pushdummyterm(Sort.create(expectedType.getSymbol().getName()));
            return;
        }
        termlist.apply(this);
        this.addArguments(id, f, size);
    }

    @Override
    public void caseAConstVarSterm(final AConstVarSterm node) {
        final TId id = node.getId();
        final String name = this.chop(id);
        Symbol sym = this.prog.getSymbol(name);

        final AlgebraTerm expectedType = this.expectedTypes.pop();

        // TODO remove me
        final Sort s = this.sorts.pop();

        if (sym == null) { // not a function or constructor
            //          if (this.prog.getSort(name) != null) {
            if (this.typeContext.getTypeDef(name) != null) {
                this.addParseError(id, "cannot use structure symbol ''" + name + "'' in term");
            }
            sym = this.curProcHead.getVariableSymbol(name);
            final AlgebraTerm symType = this.curProcHead.getVariableSymbolType(name);
            if (sym == null) { // new variable
                sym = VariableSymbol.create(name, s);
                this.addParseError(id, "variable ''" + name + "'' not declared");
            } else {
                if (!this.checkTypes(expectedType, symType, id)) {
                    this.addParseError(id, "variable ''" + name + "'' has got type ''" + symType.getSymbol().getName()
                        + "'', but ''" + expectedType + "'' expected.");
                    return;
                }

                // TODO remove me
                if (!this.checksorts(s, sym.getSort(), id)) {
                    this.addParseError(id, "variable ''" + name + "'' has got sort ''" + sym.getSort() + "', but ''"
                        + s + "'' expected.");
                    this.pushdummyterm(s);
                    return;
                }

                this.terms.add(AlgebraVariable.create((VariableSymbol) sym));
            }
        } else {
            if (((SyntacticFunctionSymbol) sym).getArity() != 0) {
                this.addParseError(id, "missing parameter list for function or constructor ''" + name + "''");
            }

            // f must be some kind of FunctionSymbol, according to comment at "if (sym == null)"
            final AlgebraTerm fTypeM = this.typeContext.getSingleTypeOf(sym).getTypeMatrix();
            final AlgebraTerm fResType = TypeTools.getResultTerm(fTypeM);
            if (!this.checkTypes(expectedType, fResType, id)) {
                this.addParseError(id, "function or constructor ''" + this.chop(id) + "'' has got type ''" + fResType
                    + "'', but ''" + expectedType + "'' expected.");
                this.pushdummyterm(Sort.create(expectedType.getSymbol().getName()));
                return;
            }

            // TODO remove me
            if (!this.checksorts(s, sym.getSort(), id)) {
                this.addParseError(id, "function or constructor ''" + this.chop(id) + "'' has got sort '" + sym.getSort()
                    + "'' but ''" + s + "'' expected.");
                this.pushdummyterm(s);
                return;
            }

            this.terms.add(AlgebraFunctionApplication.create((SyntacticFunctionSymbol) sym));
        }
    }

    @Override
    public void caseAUnaryOpSterm(final AUnaryOpSterm node) {
        final PSterm toNegate = node.getNegSterm();

        // only using peek, since after the negation sign another integer is expected
        final AlgebraTerm expectedType = this.expectedTypes.peek();

        if (!expectedType.equals(IntegerTools.getIntType(this.typeContext))) {
            this.addParseError(node.getUnary(), "Term has type ''" + AbstractIntegerPredefItem.getIntTypeName()
                + "'', but ''" + expectedType.getSymbol().getName() + "'' expected.");
            this.pushdummyterm(Sort.create(expectedType.getSymbol().getName()));
            return;
        }

        toNegate.apply(this);

        // quit in case of error
        if (!this.errors.isEmpty()) {
            return;
        }

        final AlgebraTerm toNegateTerm = this.terms.pop();

        final String operatorName = this.chop(node.getUnary());

        final AlgebraTerm negTerm = (new IntegerNegPredef(operatorName, this.typeContext, this.prog, toNegateTerm)).toTerm();

        if (negTerm == null) {
            this.addParseError(node.getUnary(), "unknown unary operator");
        } else {
            this.terms.add(negTerm);
        }
    }

    @Override
    public void caseATermlist(final ATermlist node) {
        node.getTerm().apply(this);
        final LinkedList tcs = node.getCommaterm();
        final Iterator it = tcs.iterator();
        while (it.hasNext()) {
            ((ACommaterm) it.next()).getTerm().apply(this);
        }
    }

    @Override
    public void caseACommaterm(final ACommaterm node) {
        node.getTerm().apply(this);
    }

    @Override
    public void caseAIntNumberSterm(final AIntNumberSterm node) {
        final TIntnumber intNum = node.getIntnum();

        // verifying that an int is expected
        final AlgebraTerm expectedType = this.expectedTypes.pop();
        if (!this.checkTypes(expectedType, IntegerTools.getIntType(this.typeContext), intNum)) {
            this.addParseError(node.getIntnum(), "Term has type ''" + AbstractIntegerPredefItem.getIntTypeName()
                + "'', but type ''" + expectedType.getSymbol().getName() + "'' expected.");
            this.pushdummyterm(Sort.create(expectedType.getSymbol().getName()));
            return;
        }

        // sorts are not being used
        this.sorts.pop();

        final IntegerPredefItem intPredef = new IntegerPredefItem(intNum.getText(), this.typeContext, this.prog);
        this.terms.add(intPredef.toTerm());
    }

    // Term-helpers

    private void addArguments(final Token id, final SyntacticFunctionSymbol f, final int n) {
        this.addArguments(id, f, f.getName(), n);
    }

    private void addArguments(final Token id, final SyntacticFunctionSymbol f, final String name, final int n) {
        final ProcHead callProcHead = (ProcHead) this.procHeads.get(name);
        final Vector<AlgebraTerm> ts = new Vector<AlgebraTerm>();
        try {
            for (int i = 0; i < n; i++) {
                ts.insertElementAt(this.terms.pop(), 0);
            }
        } catch (final EmptyStackException e) {
            return;
        }
        final Set refvars = new HashSet();
        final Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
        final Iterator it = ts.iterator();
        for (int i = 0; it.hasNext(); i++) {
            final AlgebraTerm t = (AlgebraTerm) it.next();
            final AlgebraTerm r = (AlgebraTerm) this.callReferences.get(t.getSymbol());
            args.add(r == null ? t : r.shallowcopy());
            if (callProcHead != null && callProcHead.isCallByReferenceArgument(i)) {
                if (t.isVariable()) {
                    if (refvars.contains(t)) {
                        this.addParseError(id, "cannot instantiate call-by-reference-variable twice");
                    } else {
                        refvars.add(t);
                        final Vector<AlgebraTerm> cargs = new Vector<AlgebraTerm>();
                        for (int j = 0; j < n; j++) {
                            cargs.add((j <= i ? args : ts).get(j));
                        }
                        final String cname = name + "_" + callProcHead.getArgName(i);
                        final SyntacticFunctionSymbol cfsym = this.prog.getFunctionSymbol(cname);
                        this.callReferences.put(t.getSymbol(), AlgebraFunctionApplication.create(cfsym, cargs));
                    }
                } else {
                    this.addParseError(id, "can instantiate call-by-reference-positions only with variables");
                }
            }
        }
        if (f != null) {
            this.terms.push(AlgebraFunctionApplication.create(f, args));
        }
    }

    // Some other helpers

    protected void pushdummyterm(final Sort s) {
        final ConstructorSymbol dummyconst = ConstructorSymbol.create(s.getName() + "dummy", new Vector<Sort>(), s);
        final AlgebraTerm t = ConstructorApp.create(dummyconst);
        this.terms.add(t);
    }

    protected boolean allFunctionsAreTerminating(final AlgebraTerm term) {
        final Iterator it = term.getDefFunctionSymbols().iterator();
        while (it.hasNext()) {
            final DefFunctionSymbol fsym = (DefFunctionSymbol) it.next();
            if (!fsym.getTermination()) {
                return false;
            }
        }
        return true;
    }

}
