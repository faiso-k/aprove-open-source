package aprove.input.Programs.simplify;

import java.math.*;
import java.util.*;

import aprove.input.Generated.simplify.analysis.*;
import aprove.input.Generated.simplify.node.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.FOFormulas.*;
import aprove.verification.theoremprover.Simplify.*;
import immutables.*;


/** Parses a simplify grammar tree and creates a FOFormulaSet
 * @author Andreas Kelle-Emden
 */
public class PassOne extends DepthFirstAdapter {
    // transformation stack: holds all necessary data for creating the FO formula tree structure
    private Stack<List<Object>> transformStack;
    private FOFormulaSet formulas;
    private List<TRSVariable> vars;
    private List<FunctionSymbol> funcs;

    private class Pair<T1, T2> {
        public T1 x;
        public T2 y;

        public Pair(T1 x, T2 y) {
            this.x = x;
            this.y = y;
        }
    }

    public FOFormulaSet getFormulaSet(){
        return this.formulas;
    }

    private TRSVariable addVar(String var) {
        TRSVariable v = TRSTerm.createVariable(var);
        if (!this.vars.contains(v)) {
            this.vars.add(v);
        }
        return v;
    }

    private FunctionSymbol addFunc(String func, int arity) {
        FunctionSymbol f = FunctionSymbol.create(func, arity);
        if (!this.funcs.contains(f)) {
            this.funcs.add(f);
        }
        return f;
    }

    private void saveLabel(TRSTerm t, String label, boolean isPos, boolean isNeg) {
        return;
    }

    public List<FOFormula> popFOFList(){
        List objs =  this.transformStack.pop();
        return objs;
    }

    public List<TRSTerm> popTermList(){
        List objs =  this.transformStack.pop();
        return objs;
    }

    public void addToTop(Object o){
        this.transformStack.peek().add(o);
    }

    @Override
    public void inAFosFormulasFormulaset(AFosFormulasFormulaset node)
    {
        this.transformStack = new Stack<List<Object>>();
        this.transformStack.push(new ArrayList<Object>());
        this.formulas = new FOFormulaSet();
        this.vars = new ArrayList<TRSVariable>();
        this.funcs = new ArrayList<FunctionSymbol>();
    }

    @Override
    public void outAFosFormulasFormulaset(AFosFormulasFormulaset node)
    {
        List<Object> frame = this.transformStack.pop();
        for (Object o : frame) {
            this.formulas.add((FOFormula)o);
        }
    }

    @Override
    public void inAFoDefpredFormula(AFoDefpredFormula node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outAFoDefpredFormula(AFoDefpredFormula node)
    {
        List<Object> frame = this.transformStack.pop();
        FunctionSymbol func;
        List<TRSVariable> args;
        FOFormula body;

        func = (FunctionSymbol)     frame.get(0);
        args = (List<TRSVariable>)frame.get(1);
        body = (FOFormula)          frame.get(2);
        FOFormulaDefpred formula = new FOFormulaDefpred(args, func, body);
        this.addToTop(formula);
    }

    @Override
    public void inAFoLiteralFormula(AFoLiteralFormula node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outAFoLiteralFormula(AFoLiteralFormula node)
        {
        List<Object> frame = this.transformStack.pop();
        if (frame.size() > 0) {
            TRSTerm t = (TRSTerm)frame.get(0);
            this.addToTop(new FOFormulaTerm(t));
        }
    }

    @Override
    public void inAFoAndFormula(AFoAndFormula node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outAFoAndFormula(AFoAndFormula node)
    {
        this.addToTop(new FOFormulaAnd(this.popFOFList()));
    }

    @Override
    public void inAFoOrFormula(AFoOrFormula node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outAFoOrFormula(AFoOrFormula node)
    {
        this.addToTop(new FOFormulaOr(this.popFOFList()));
    }

    @Override
    public void inAFoNotFormula(AFoNotFormula node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outAFoNotFormula(AFoNotFormula node)
    {
        List<Object> frame = this.transformStack.pop();
        FOFormulaNot form = new FOFormulaNot((FOFormula)frame.get(0));
        this.addToTop(form);
    }

    @Override
    public void inAFoImpliesFormula(AFoImpliesFormula node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outAFoImpliesFormula(AFoImpliesFormula node)
    {
        List<Object> frame = this.transformStack.pop();
        FOFormula form = new FOFormulaImplies((FOFormula)frame.get(0), (FOFormula)frame.get(1));
        this.addToTop(form);
    }

    @Override
    public void inAFoIffFormula(AFoIffFormula node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outAFoIffFormula(AFoIffFormula node)
    {
        List<Object> frame = this.transformStack.pop();
        FOFormula form = new FOFormulaIff((FOFormula)frame.get(0), (FOFormula)frame.get(1));
        this.addToTop(form);
    }

    @Override
    public void inAFoForallFormula(AFoForallFormula node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    public void parseSpecials(List<Object> frame, FOFormulaQuantifier form) {
        int i = frame.size();
        for (int j = 1; j < i-1; j++) {
            Pair<Integer, Object> p = (Pair<Integer, Object>)frame.get(j);
            int num = p.x.intValue();
            switch (num) {
            case FOFormulaQuantifier.SPECIAL_PROMOTE:
                form.setPromote(true);
                break;
            case FOFormulaQuantifier.SPECIAL_QID:
                String s = (String)p.y;
                form.setQid(s);
                break;
            case FOFormulaQuantifier.SPECIAL_SKOLEM:
                String s2 = (String)p.y;
                form.setSkolemId(s2);
                break;
            case FOFormulaQuantifier.SPECIAL_PATS:
                TRSTerm t = (TRSTerm)p.y;
                form.addPat(t);
                break;
            case FOFormulaQuantifier.SPECIAL_MPAT:
                TRSTerm t2 = (TRSTerm)p.y;
                form.addMPat(t2);
                break;
            case FOFormulaQuantifier.SPECIAL_NOPATS:
                TRSTerm t3 = (TRSTerm)p.y;
                form.addNoPat(t3);
                break;
            }
        }
    }

    @Override
    public void outAFoForallFormula(AFoForallFormula node)
    {
        List<Object> frame = this.transformStack.pop();
        int i = frame.size();
        FOFormulaQuantifier form = new FOFormulaForall((List)frame.get(0), (FOFormula)frame.get(i-1));
        this.parseSpecials(frame, form);
        this.addToTop(form);
    }

    @Override
    public void inAFoExistsFormula(AFoExistsFormula node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outAFoExistsFormula(AFoExistsFormula node)
    {
        List<Object> frame = this.transformStack.pop();
        int i = frame.size();
        FOFormulaQuantifier form = new FOFormulaExists((List)frame.get(0), (FOFormula)frame.get(i-1));
        this.parseSpecials(frame, form);
        this.addToTop(form);
    }

    @Override
    public void inAFoProofFormula(AFoProofFormula node)
    {
        this.transformStack.push(new ArrayList<Object>());
   }

    @Override
    public void outAFoProofFormula(AFoProofFormula node)
    {
        this.addToTop(new FOFormulaProof(this.popFOFList()));
    }

    @Override
    public void inAFoLemmaFormula(AFoLemmaFormula node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outAFoLemmaFormula(AFoLemmaFormula node)
    {
        this.addToTop(new FOFormulaLemma(this.popFOFList()));
    }

    @Override
    public void inAFoBackgroundPushFormula(AFoBackgroundPushFormula node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outAFoBackgroundPushFormula(AFoBackgroundPushFormula node)
    {
        List<Object> frame = this.transformStack.pop();
        FOFormula form = new FOFormulaBGPush((FOFormula)frame.get(0));
        this.addToTop(form);
    }

    @Override
    public void outAFoBackgroundPopFormula(AFoBackgroundPopFormula node)
    {
        this.addToTop(new FOFormulaBGPop());
    }

    @Override
    public void inAFoLetFormula(AFoLetFormula node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outAFoLetFormula(AFoLetFormula node)
    {
        List<Object> frame = this.transformStack.pop();
        List<String>    ids   = new ArrayList<String>();
        List<FOFormula> forms = new ArrayList<FOFormula>();
        int size = frame.size();
        for (int i = 0; i < size-1; i++) {
            Pair<String, FOFormula> pair = (Pair<String, FOFormula>)frame.get(i);
            ids.add(pair.x);
            forms.add(pair.y);
        }
        this.addToTop(new FOFormulaLet(ids, forms, (FOFormula)frame.get(size-1)));
    }

    @Override
    public void outAFoDefvalueFormula(AFoDefvalueFormula node)
    {
        this.addToTop(new FOFormulaDefvalue(node.getVar().getText()));
    }

    @Override
    public void inAFoIfthenelseFormula(AFoIfthenelseFormula node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outAFoIfthenelseFormula(AFoIfthenelseFormula node)
    {
        List<Object> frame = this.transformStack.pop();
        this.addToTop(new FOFormulaITE((FOFormula)frame.get(0), (FOFormula)frame.get(1), (FOFormula)frame.get(2)));
    }

    @Override
    public void inAFotTermFormOrTerm(AFotTermFormOrTerm node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outAFotTermFormOrTerm(AFotTermFormOrTerm node)
    {
        List<Object> frame = this.transformStack.pop();
        FOFormulaTerm lit = new FOFormulaTerm((TRSTerm)frame.get(0));
        Pair<String, FOFormula> pair = new Pair<String, FOFormula>(node.getVar().getText(),lit);
        this.addToTop(pair);
    }

    @Override
    public void inAFotFormulaFormOrTerm(AFotFormulaFormOrTerm node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outAFotFormulaFormOrTerm(AFotFormulaFormOrTerm node)
    {
        List<Object> frame = this.transformStack.pop();
        Pair<String, FOFormula> pair = new Pair<String, FOFormula>(node.getVar().getText(),(FOFormula)frame.get(0));
        this.addToTop(pair);
    }

    @Override
    public void inALiLabelLiteral(ALiLabelLiteral node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outALiLabelLiteral(ALiLabelLiteral node)
    {
        List<Object> frame = this.transformStack.pop();
        this.saveLabel((TRSTerm)frame.get(0), node.getLbl().getText(), false, false);
        this.addToTop(frame.get(0));
    }

    public void inALiLabelposLiteral(ALiLabelLiteral node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    public void outALiLabelposLiteral(ALiLabelLiteral node)
    {
        List<Object> frame = this.transformStack.pop();
        this.saveLabel((TRSTerm)frame.get(0), node.getLbl().getText(), true, false);
        this.addToTop(frame.get(0));
    }

    public void inALiLabelnegLiteral(ALiLabelLiteral node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    public void outALiLabelnegLiteral(ALiLabelLiteral node)
    {
        List<Object> frame = this.transformStack.pop();
        this.saveLabel((TRSTerm)frame.get(0), node.getLbl().getText(), false, true);
        this.addToTop(frame.get(0));
    }

    private void addFuncApp2(FunctionSymbol f)
    {
        List<Object> frame = this.transformStack.pop();
        ArrayList<TRSTerm> terms = new ArrayList<TRSTerm>();
        terms.add((TRSTerm)frame.get(0));
        terms.add((TRSTerm)frame.get(1));
        TRSTerm t = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(terms));
        this.addToTop(t);
     }

    @Override
    public void inALiEqualLiteral(ALiEqualLiteral node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outALiEqualLiteral(ALiEqualLiteral node)
    {
        this.addFuncApp2(StandardSymbols.fsEQ);
    }

    @Override
    public void inALiNotequalLiteral(ALiNotequalLiteral node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outALiNotequalLiteral(ALiNotequalLiteral node)
    {
        this.addFuncApp2(StandardSymbols.fsNEQ);
    }

    @Override
    public void inALiLessLiteral(ALiLessLiteral node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outALiLessLiteral(ALiLessLiteral node)
    {
        this.addFuncApp2(StandardSymbols.fsLess);
    }

    @Override
    public void inALiLessequalLiteral(ALiLessequalLiteral node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outALiLessequalLiteral(ALiLessequalLiteral node)
    {
        this.addFuncApp2(StandardSymbols.fsLessEQ);
    }

    @Override
    public void inALiGreaterLiteral(ALiGreaterLiteral node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outALiGreaterLiteral(ALiGreaterLiteral node)
    {
        this.addFuncApp2(StandardSymbols.fsGrt);
    }

    @Override
    public void inALiGreaterequalLiteral(ALiGreaterequalLiteral node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outALiGreaterequalLiteral(ALiGreaterequalLiteral node)
    {
        this.addFuncApp2(StandardSymbols.fsGrtEQ);
    }

    @Override
    public void inALiDistinctLiteral(ALiDistinctLiteral node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outALiDistinctLiteral(ALiDistinctLiteral node)
    {
        List<TRSTerm> terms = this.popTermList();
        ArrayList<TRSTerm> ts;
        if (terms instanceof ArrayList) {
            ts = (ArrayList<TRSTerm>)terms;
        } else {
            ts = new ArrayList<TRSTerm>();
            for (TRSTerm t : terms) {
                ts.add(t);
            }
        }
        TRSTerm t = TRSTerm.createFunctionApplication(StandardSymbols.getFsDistinct(ts.size()), ImmutableCreator.create(ts));
        this.addToTop(t);
    }

    @Override
    public void outALiTrueLiteral(ALiTrueLiteral node)
    {
        this.addToTop(TRSTerm.createFunctionApplication(StandardSymbols.csTrue, TRSTerm.EMPTY_ARGS));
    }

    @Override
    public void outALiFalseLiteral(ALiFalseLiteral node)
    {
        this.addToTop(TRSTerm.createFunctionApplication(StandardSymbols.csFalse, TRSTerm.EMPTY_ARGS));
    }

/*    public void inALiTermLiteral(ALiTermLiteral node)
    {
        transformStack.push(new ArrayList<Object>());
    }

    public void outALiTermLiteral(ALiTermLiteral node)
    {
        List<Object> frame = transformStack.pop();
        addToTop(new FOFormulaTerm((Term)frame.get(0)));
    }
*/
    @Override
    public void outATNumberTerm(ATNumberTerm node)
    {
        this.addToTop(TRSTerm.createFunctionApplication(
                StandardSymbols.getFsNumber(new BigInteger(node.getNumber().getText())),
                TRSTerm.EMPTY_ARGS));
    }

    @Override
    public void outATVarTerm(ATVarTerm node)
    {
        this.addToTop(this.addVar(node.getVar().getText()));
    }

    @Override
    public void inATStoreTerm(ATStoreTerm node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outATStoreTerm(ATStoreTerm node)
    {
        List<Object> frame = this.transformStack.pop();
        ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
        args.add((TRSTerm)frame.get(0));
        args.add((TRSTerm)frame.get(1));
        args.add((TRSTerm)frame.get(2));
        TRSTerm t = TRSTerm.createFunctionApplication(StandardSymbols.fsStore, ImmutableCreator.create(args));
        this.addToTop(t);
    }

    @Override
    public void inATSelectTerm(ATSelectTerm node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outATSelectTerm(ATSelectTerm node)
    {
        List<Object> frame = this.transformStack.pop();
        ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
        args.add((TRSTerm)frame.get(0));
        args.add((TRSTerm)frame.get(1));
        args.add((TRSTerm)frame.get(2));
        TRSTerm t = TRSTerm.createFunctionApplication(StandardSymbols.fsSelect, ImmutableCreator.create(args));
        this.addToTop(t);
    }

    @Override
    public void inATPlusTerm(ATPlusTerm node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outATPlusTerm(ATPlusTerm node)
    {
        List<Object> frame = this.transformStack.pop();
        ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
        args.add((TRSTerm)frame.get(0));
        args.add((TRSTerm)frame.get(1));
        TRSTerm t = TRSTerm.createFunctionApplication(StandardSymbols.fsPlus, ImmutableCreator.create(args));
        this.addToTop(t);
    }

    @Override
    public void inATMinusTerm(ATMinusTerm node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outATMinusTerm(ATMinusTerm node)
    {
        List<Object> frame = this.transformStack.pop();
        ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
        args.add((TRSTerm)frame.get(0));
        args.add((TRSTerm)frame.get(1));
        TRSTerm t = TRSTerm.createFunctionApplication(StandardSymbols.fsMinus, ImmutableCreator.create(args));
        this.addToTop(t);
    }

    @Override
    public void inATTimesTerm(ATTimesTerm node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outATTimesTerm(ATTimesTerm node)
    {
        List<Object> frame = this.transformStack.pop();
        ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
        args.add((TRSTerm)frame.get(0));
        args.add((TRSTerm)frame.get(1));
        TRSTerm t = TRSTerm.createFunctionApplication(StandardSymbols.fsTimes, ImmutableCreator.create(args));
        this.addToTop(t);
    }

    @Override
    public void inATFunctappTerm(ATFunctappTerm node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outATFunctappTerm(ATFunctappTerm node)
    {
        List<Object> frame = this.transformStack.pop();
        int arity = frame.size();
        ArrayList<TRSTerm> ts = new ArrayList<TRSTerm>();
        for (Object t : frame) {
            ts.add((TRSTerm)t);
        }
        TRSFunctionApplication func = TRSTerm.createFunctionApplication(this.addFunc(node.getVar().getText(), arity), ImmutableCreator.create(ts));
        this.addToTop (func);
    }

    @Override
    public void outAVarsetVarset(AVarsetVarset node)
    {
        List<TRSTerm> vars = new ArrayList<TRSTerm>();
        for (TVar v : node.getVar()) {
            TRSVariable var = this.addVar(v.getText());
            vars.add(var);
        }
        this.addToTop(vars);
    }

    @Override
    public void outAPatPromotePatterns(APatPromotePatterns node)
    {
        this.addToTop(new Pair<Integer, Boolean>(FOFormulaQuantifier.SPECIAL_PROMOTE, true));
    }

    @Override
    public void inAPatMpatPatterns(APatMpatPatterns node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outAPatMpatPatterns(APatMpatPatterns node)
    {
        List<Object> frame = this.transformStack.pop();
        for (Object o: frame) {
            this.addToTop(new Pair<Integer, TRSTerm>(FOFormulaQuantifier.SPECIAL_MPAT, (TRSTerm)o));
        }
    }

    @Override
    public void inAPatPatternPatterns(APatPatternPatterns node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outAPatPatternPatterns(APatPatternPatterns node)
    {
        List<Object> frame = this.transformStack.pop();
        for (Object o : frame) {
            this.addToTop(new Pair<Integer, TRSTerm>(FOFormulaQuantifier.SPECIAL_PATS, (TRSTerm)o));
        }
    }

    @Override
    public void inASpNopatsSpecial(ASpNopatsSpecial node)
    {
        this.transformStack.push(new ArrayList<Object>());
    }

    @Override
    public void outASpNopatsSpecial(ASpNopatsSpecial node)
    {
        List<Object> frame = this.transformStack.pop();
        this.addToTop(new Pair<Integer, TRSTerm>(FOFormulaQuantifier.SPECIAL_NOPATS, (TRSTerm)frame.get(0)));
    }

    @Override
    public void outASpSkolemNumSpecial(ASpSkolemNumSpecial node)
    {
        this.addToTop(new Pair<Integer, String>(FOFormulaQuantifier.SPECIAL_SKOLEM, node.getNumber().getText()));
    }

    @Override
    public void outASpSkolemVarSpecial(ASpSkolemVarSpecial node)
    {
        this.addToTop(new Pair<Integer, String>(FOFormulaQuantifier.SPECIAL_SKOLEM, node.getVar().getText()));
    }

    @Override
    public void outASpQidNumSpecial(ASpQidNumSpecial node)
    {
        this.addToTop(new Pair<Integer, String>(FOFormulaQuantifier.SPECIAL_QID, node.getNumber().getText()));
    }

    @Override
    public void outASpQidVarSpecial(ASpQidVarSpecial node)
    {
        this.addToTop(new Pair<Integer, String>(FOFormulaQuantifier.SPECIAL_QID, node.getVar().getText()));
    }

}
