package aprove.verification.oldframework.Haskell;

import java.math.*;
import java.util.*;

import aprove.input.Generated.haskell.node.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Literals.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Qualifiers.*;
import aprove.verification.oldframework.Haskell.Syntax.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Haskell.Visitors.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The HaskellFactory is a collection of methods used by the HaskellASTBuilder
 * which create various HaskellObjects of the Haskell Framework.
 *
 * If you search the object of an syntactic expression of haskell
 * it is created here or in the HaskellSymFactory.
 *
 * An empty prelude has to be initializied before a HaskellFactory can work
 * propably, cause the haskell type constructors Bool,->, (,...) and [] and thier
 * constructors True, False, (,...) and [] are declared in this empty prelude.
 *
 * every object needed by a create method has to offer non null token
 * cause the create methods expect an non null token.
 *
 */
public class HaskellFactory implements DoCompFactory{
    boolean isPrelude;
    HaskellSymFactory symfac;
    Prelude prelude;
    int count = 0;

    public HaskellFactory(HaskellSymFactory symfac, boolean isPrelude, Prelude prelude){
        this.symfac = symfac;
        this.isPrelude = isPrelude;
        this.prelude = prelude;
    }

    public String getUniqueName(){
        this.count++;
        return " "+"x"+this.count;
    }

    public HaskellExp buildQual(HaskellQual qu){
        return null;
    }

    public HaskellObject buildFlipApply(HaskellObject atom, HaskellObject arg){
        Token tok = atom.getToken();
        ((Atom) atom).getSymbol().setOperator(false);
        HaskellObject flip = this.buildVar(this.symfac.flip(tok));
        return this.buildApplies(new HaskellObject[]{flip,atom,arg});
    }

    public HaskellObject buildListCons(HaskellObject head,HaskellObject list){
        HaskellObject cons = this.buildCons(this.symfac.listCons(head.getToken()));
        return this.buildApplies(new HaskellObject[]{cons,head,list});
    }

    public HaskellObject buildList(HaskellObject[] list,Token t){
        HaskellObject cur = this.buildCons(this.symfac.emptyListCons(t));
        for (int i = (list.length-1);i>=0;i--){
            cur = this.buildListCons(list[i],cur);
        }
        return cur;
    }

    public HaskellObject buildArrow(HaskellObject a,HaskellObject b){
        HaskellObject cons = this.buildCons(this.symfac.arrowCons(a.getToken()));
        ((Cons) cons).setTYCONS();
        return this.buildApplies(new HaskellObject[]{cons,a,b});
    }

    public HaskellObject buildEmptyListCons(Token tok){
        return this.buildCons(this.symfac.emptyListCons(tok));
    }

    public HaskellObject buildApplies(List<HaskellObject> list){
        Iterator<HaskellObject> it = list.iterator();
        HaskellObject res = it.next();
        Token tok = res.getToken();
        while(it.hasNext()){
            res = (new Apply(res,it.next())).setToken(tok);
        }
        return res;
    }

    public HaskellObject buildAppliesInvers(List<HaskellObject> list){
        ListIterator<HaskellObject> it = list.listIterator(list.size());
        HaskellObject res = it.previous();
        Token tok = res.getToken();
        while(it.hasPrevious()){
            res = (new Apply(res,it.previous())).setToken(tok);
        }
        return res;
    }

    public List<HaskellObject> unApply(HaskellObject ho){
        List<HaskellObject> res = new Vector<HaskellObject>();
        while (ho instanceof Apply){
            Apply app = (Apply) ho;
            ho = app.getFunction();
            res.add(0,app.getArgument());
        }
        res.add(0,ho);
        return res;
    }

    public HaskellObject buildApplies(HaskellObject[] list){
        HaskellObject res = list[0];
        Token tok = res.getToken();
        for(int i=1;i<list.length;i++){
            res = (new Apply(res,list[i])).setToken(tok);
        }
        return res;
    }

    public HaskellObject buildAppliesInvers(HaskellObject[] list){
        HaskellObject res = list[0];
        Token tok = res.getToken();
        for(int i=list.length-1;i<=0;i++){
            res = (new Apply(res,list[i])).setToken(tok);
        }
        return res;
    }

    public HaskellObject buildApply(HaskellObject ho1,HaskellObject ho2){
        return (new Apply(ho1,ho2)).setToken(ho1.getToken());
    }

    public HaskellObject buildOperator(Atom op){
        op.getSymbol().setOperator(true);
        return (new Operator(op)).setToken(op.getToken());
    }

    public HaskellObject buildCons(HaskellSym co){
        return (new Cons(co)).setToken(co.getToken());
    }

    public HaskellObject buildVar(HaskellSym va){
        return (new Var(va)).setToken(va.getToken());
    }

    public HaskellObject buildAList(HaskellExp start,HaskellExp step, HaskellExp end){
        Token tok = start.getToken();
        if (step == null) {
           if (end == null) {
               HaskellObject en = this.buildVar(this.symfac.enumFrom(tok));
               return this.buildApplies(new HaskellObject[]{en,start});
           } else {
               HaskellObject en = this.buildVar(this.symfac.enumFromTo(tok));
               return this.buildApplies(new HaskellObject[]{en,start,end});
           }
        } else {
           if (end == null) {
               HaskellObject en = this.buildVar(this.symfac.enumFromThen(tok));
               return this.buildApplies(new HaskellObject[]{en,start,step});
           } else {
               HaskellObject en = this.buildVar(this.symfac.enumFromThenTo(tok));
               return this.buildApplies(new HaskellObject[]{en,start,step,end});
           }
        }
    }

    public HaskellObject buildJokerPat(Token t){
        return (new JokerPat()).setToken(t);
    }

    public HaskellObject buildIrrPat(HaskellPat pat, Token t){
        return (new IrrPat(pat)).setToken(t);
    }

    public HaskellObject buildBindPat(Var var,HaskellPat pat){
        return (new BindPat(var,pat)).setToken(var.getToken());
    }

    public HaskellObject buildIntegerLit(Token t){
        String text = t.getText();
        int radix = 10;
        if (text.startsWith("0x") || text.startsWith("0X")) {
            text = text.substring(2);
            radix = 16;
        } else if (text.startsWith("0O") || text.startsWith("0o")) {
            text = text.substring(2);
            radix = 8;
        }
        return (new IntegerLit(Integer.parseInt(text,radix))).setToken(t);
    }

    public HaskellObject buildCharLit(char c,Token t){
        return (new CharLit(c)).setToken(t);
    }

    public HaskellObject buildFloatLit(Token t){
        BigDecimal value = new BigDecimal(t.getText());
        return (new FloatLit(value)).setToken(t);
    }

    public HaskellObject buildIfExp(HaskellExp cond,HaskellExp texp,HaskellExp fexp,Token tok){
        return (new IfExp(cond,texp,fexp)).setToken(tok);
    }

    public HaskellObject buildLambdaExp(List<HaskellPat> pats,HaskellExp res,Token tok){
        PatternizeVisitor pv = new PatternizeVisitor(null);
        pats = pv.listWalk(pats,pv);
        return (new LambdaExp(pats,res)).setToken(tok);
    }

    public HaskellObject buildQuantorExp(List<Var> vars, HaskellExp res,Token tok){
        return (new QuantorExp(vars,res)).setToken(tok);
    }

    public HaskellObject buildLetExp(List<HaskellDecl> decls,HaskellExp res,Token tok){
        return (new LetExp(decls,res,LetExp.LET)).setToken(tok);
    }

    public HaskellObject buildWhereExp(List<HaskellDecl> decls,HaskellExp res,Token tok){
        return (new LetExp(decls,res,LetExp.WHERE)).setToken(tok);
    }

    public HaskellObject buildWhereExp(WhereDecls wdecls,HaskellExp res){
        if (wdecls == null) {
            return res;
        }
        return (new LetExp(wdecls.getDeclarations(),res,LetExp.WHERE)).setToken(wdecls.getToken());
    }

    public HaskellObject buildRawTerm(List<HaskellObject> objs){
        return (new RawTerm(objs)).setToken(objs.get(0).getToken());
    }

    @Override
    public HaskellExp buildMonadBind(HaskellPat pat,HaskellExp exp,HaskellExp next){
        List<HaskellPat> pats = new Vector<HaskellPat>();
        pats.add(pat);
        Token tok = pat.getToken();
        LambdaExp lexp = (LambdaExp) this.buildLambdaExp(pats,next,tok);
        return (HaskellExp)this.buildApplies(new HaskellObject[]{this.buildVar(this.symfac.monadBind(tok)),exp,lexp});
    }

    @Override
    public HaskellExp buildMonadThen(HaskellExp exp,HaskellExp next){
        return (HaskellExp)this.buildApplies(new HaskellObject[]{this.buildVar(this.symfac.monadThen(exp.getToken())),exp,next});
    }

    @Override
    public HaskellExp buildMonadLet(List<HaskellDecl> decls,HaskellExp res,LetQual lq){
        return (HaskellExp)(new LetExp(decls,res,LetExp.LET)).setToken(lq.getToken());
    }

    public HaskellObject buildMonad(HaskellQual[] list){
        HaskellExp cur = ((ExpQual) list[list.length-1]).getExpression();
        for (int i = (list.length-2);i>=0;i--){
            HaskellQual qu = list[i];
            cur = qu.toMonad(this,cur);
        }
        return cur;
    }

    @Override
    public HaskellExp buildListCompGen(HaskellPat pat,HaskellExp exp,HaskellExp next){
        Token tok = pat.getToken();
        List alts = new Vector<AltExp>();
        // pat -> next
        // _ -> []
        alts.add((AltExp) this.buildAltExp(pat,next));
        alts.add((AltExp) this.buildAltExp((HaskellPat) this.buildJokerPat(tok),(HaskellExp) this.buildEmptyListCons(tok)));
        List<HaskellPat> pats = new Vector<HaskellPat>();
    String name = this.getUniqueName();
        pats.add((HaskellPat) this.buildVar(this.symfac.createNameSym(tok,name)));
        LambdaExp lexp =(LambdaExp) this.buildLambdaExp(  //  \x -> case (x) of alts
           pats,
           (HaskellExp) this.buildCaseExp(tok,(HaskellExp)this.buildVar(this.symfac.createNameSym(tok,name)),alts),
           tok);
        return (HaskellExp)this.buildApplies(new HaskellObject[]{this.buildVar(this.symfac.concatMap(tok)),lexp,exp});
    }

    @Override
    public HaskellExp buildListCompGuard(HaskellExp exp,HaskellExp next){
        Token tok = exp.getToken();
        return (HaskellExp) this.buildIfExp(exp,next,(HaskellExp) this.buildEmptyListCons(tok),tok);
    }

    @Override
    public HaskellExp buildListCompLet(List<HaskellDecl> decls,HaskellExp res,LetQual lq){
        return (HaskellExp)(new LetExp(decls,res,LetExp.LET)).setToken(lq.getToken());
    }

    public HaskellObject buildListComp(HaskellExp cur,HaskellQual[] list){;
        cur = (HaskellExp) this.buildListCons(cur,this.buildEmptyListCons(cur.getToken()));
        for (int i = (list.length-1);i>=0;i--){
            HaskellQual qu = list[i];
            cur = qu.toListComp(this,cur);
        }
        return cur;
    }

    public HaskellObject buildLetQual(List<HaskellDecl> decls,Token tok){
        return (new LetQual(decls)).setToken(tok);
    }

    public HaskellObject buildGenQual(HaskellPat pat,HaskellExp exp){
        ((RawTerm) pat).patternize(null);
        return (new GenQual(pat,exp)).setToken(pat.getToken());
    }

    public HaskellObject buildExpQual(HaskellExp exp){
        return (new ExpQual(exp)).setToken(exp.getToken());
    }

    public HaskellObject buildImpSpec(Token hide,Token open,List<HaskellImport> imports){
        return (new ImpSpec(hide != null,imports)).setToken(open);
    }

    public HaskellObject buildConsImport(Cons cons,List<Atom> atoms){
        return (new ConsImport(cons,atoms)).setToken(cons.getToken());
    }

    public HaskellObject buildImpDecl(Token tok,Token quali,HaskellSym modid,HaskellSym alias,ImpSpec impSpec){
        return (new ImpDecl(quali!=null,modid,alias,impSpec)).setToken(tok);
    }

    public HaskellObject buildConsExport(Cons cons,List<Atom> atoms){
        return (new ConsExport(cons,atoms)).setToken(cons.getToken());
    }

    public HaskellObject buildModExport(Token tok,HaskellSym sym){
        return (new ModExport(sym)).setToken(tok);
    }

    public HaskellObject buildCondStackExp(List<CondExp> conds){
        return (new CondStackExp(conds)).setToken(conds.get(0).getToken());
    }

    public HaskellObject buildTypeDecl(List<Var> vars,HaskellPreType type){
        return (new TypeDecl(vars,type)).setToken(vars.get(0).getToken());
    }

    public HaskellObject buildFuncDecl(RawTerm lhs,HaskellExp exp,WhereDecls wdecs){
        return this.buildFuncDecl(lhs,(HaskellExp)this.buildWhereExp(wdecs,exp));
    }

    public HaskellObject buildFuncDecl(RawTerm lhs,List<CondExp> conds,WhereDecls wdecs){
        return this.buildFuncDecl(lhs,(HaskellExp)this.buildWhereExp(wdecs,(HaskellExp)this.buildCondStackExp(conds)));
    }

    public HaskellObject buildFuncDecl(RawTerm lhs,HaskellExp exp){
        HaskellSym sym = lhs.getDeclaredFunction();
        lhs.patternize(sym);
        if (sym != null) {
            return (new FuncDecl(sym,lhs,exp)).setToken(lhs.getToken());
        } else {
            return (new PatDecl(this.symfac.createNameSym(lhs.getToken(),this.getUniqueName()),lhs,exp)).setToken(lhs.getToken());
        }
    }

    public HaskellObject buildWhereDecls(Token tok,List<HaskellDecl> decls){
        return (new WhereDecls(decls)).setToken(tok);
    }

    public HaskellObject buildCondExp(HaskellExp guard,HaskellExp exp){
        return (new CondExp(guard,exp)).setToken(exp.getToken());
    }

    public HaskellObject buildModule(Token tok,HaskellSym name,List<HaskellExport> expList,List<ImpDecl> imps,List<HaskellDecl> decls){
        if (this.isPrelude) {
           this.prelude.setToken(tok);
           this.prelude.setExpList(expList);
           this.prelude.setImps(imps);
           this.prelude.setDecls(decls);
           return this.prelude;
        } else {
           return (new Module(name.getName(true),expList,imps,decls)).setToken(tok);
        }
    }

    public HaskellObject buildStartTerm(Token tok,List<Var> vars,HaskellExp exp){
        return this.buildQuantorExp(vars,exp,tok);
    }

    public HaskellObject buildInfixDecl(Token tok, int fixity, int priority,List<Operator> ops){
        return (new InfixDecl(fixity,priority,ops)).setToken(tok);
    }

    public HaskellObject buildCaseExp(Token tok,HaskellExp exp,List<AltExp> alts){
        return (new CaseExp(exp,alts)).setToken(tok);
    }

    public HaskellObject buildAltExp(HaskellPat pat, HaskellExp exp,WhereDecls wdecs){
        PatternizeVisitor pv = new PatternizeVisitor(null);
        pat = (HaskellPat) pat.visit(pv);
        return this.buildAltExp(pat,(HaskellExp)this.buildWhereExp(wdecs,exp));
    }

    public HaskellObject buildAltExp(HaskellPat pat, List<CondExp> conds,WhereDecls wdecs){
        return this.buildAltExp(pat,(HaskellExp)this.buildWhereExp(wdecs,(HaskellExp)this.buildCondStackExp(conds)));
    }

    public HaskellObject buildAltExp(HaskellPat pat,HaskellExp exp){
        return (new AltExp(pat,exp)).setToken(pat.getToken());
    }

    public HaskellObject buildLabeled(HaskellObject obj,List<FieldEqu> equs){
        if (obj instanceof Cons) {
            return (new LabCons((Cons)obj,equs)).setToken(obj.getToken());
        } else {
            return (new LabUpdate((HaskellExp)obj,equs)).setToken(obj.getToken());
        }
    }

    public HaskellObject buildFieldSelectorFunction(Var field, int pos, DataCon con) {
        RawTerm lhs;
        HaskellExp rhs=null;
        List<HaskellObject> hos = new Vector<HaskellObject>(con.getArity()+1);
        hos.add(new Cons(con.getSymbol()));
        for (int i=0;i<con.getArity();++i) {
            if (i!=pos) {
                hos.add(this.buildJokerPat(field.getToken()));
            }
            else { /* i == pos */
                rhs = (Var) new Var(new HaskellNamedSym("","x")).setToken(field.getToken());
                hos.add(Copy.deep(rhs));
            }
        }
        List<HaskellObject> rawTermComp = new ArrayList<HaskellObject>(1);
        rawTermComp.add(new Apply(field, HaskellTools.buildApplies(hos)));
        lhs = (RawTerm) new RawTerm(rawTermComp).setToken(field.getToken());
        return new SelectorDecl((FuncDecl)this.buildFuncDecl(lhs,rhs));
    }

    public HaskellObject buildFieldDecl(Var field, boolean isStrict, HaskellExp type) {
        return new FieldDecl(field, isStrict, type).setToken(field.getToken());
    }

    public HaskellObject buildFieldEqu(Var var,HaskellExp exp){
        return (new FieldEqu(var,exp)).setToken(var.getToken());
    }

    public HaskellObject buildType(Context context, HaskellObject matrix){
        return (new HaskellPreType(context,matrix)).setToken(context.getToken());
    }

    public HaskellObject buildContext(HaskellObject ho){
        List<HaskellObject> constraints = null;
        List<HaskellObject> list = this.unApply(ho);
        HaskellObject co = list.get(0);
        if (!(co instanceof Cons)) {
            HaskellError.output(co,"( or Classname expected");
        }
        Cons cons = (Cons) co;
        int i = cons.getSymbol().getTuple();
        if (i >= 0) {
            list.remove(0);
            constraints = list;
        } else {
            constraints = new Vector<HaskellObject>();
            constraints.add(ho);
        }
        for (HaskellObject cst : constraints){
            if (cst instanceof Apply) {
                Apply app = (Apply) cst;
                if (!(app.getFunction() instanceof Cons)) {
                    HaskellError.output(app,"Classname expected");
                }
                Cons curCons = (Cons) app.getFunction();
                curCons.setTYCLASS();
            } else {
                HaskellError.output(co,"Class constraint expected");
            }
        }
        return (new Context(constraints)).setToken(constraints.get(0).getToken());
    }

    public HaskellObject buildDataCon(HaskellSym sym, List<HaskellObject> types, List<Var> fields) {
        return (new DataCon(sym, types, false, fields)).setToken(sym.getToken());
    }

    public HaskellObject buildDataCon(HaskellSym op,HaskellObject a,HaskellObject b){
        List<HaskellObject> types = new Vector<HaskellObject>();
        types.add(a);
        types.add(b);
        return (new DataCon(op,types,true)).setToken(a.getToken());
    }

    public HaskellObject buildDataCon(HaskellObject ho){
        List<HaskellObject> types = this.unApply(ho);
        HaskellObject co = types.remove(0);
        if (!(co instanceof Cons)) {
            HaskellError.output(co,"Type constructor expected");
        }
        Cons cons = (Cons) co;
        return (new DataCon(cons.getSymbol(),types,false)).setToken(cons.getToken());
    }

    public HaskellObject buildDataCon(HaskellObject co,HaskellObject type){
        List<HaskellObject> types = new Vector<HaskellObject>();
        if (!(co instanceof Cons)) {
            HaskellError.output(co,"Type constructor expected");
        }
        Cons cons = (Cons) co;
        types.add(type);
        return (new DataCon(cons.getSymbol(),types,false)).setToken(cons.getToken());
    }

    public HaskellObject buildDataDecl(Token tok,Context context,HaskellObject defType,List<DataCon> dataCons,boolean newType,Derivings derivings){
        if (context == null) {
           context = new Context();
           context.setToken(tok);
        }
        for(DataCon dc : dataCons){
           dc.buildPreType(this,context,defType);
        }
        return (new DataDecl(context,defType,dataCons,newType,derivings)).setToken(tok);
    }

    public HaskellObject buildClassDecl(Token tok,Context context,HaskellObject defType,List<HaskellDecl> decls){
        if (context == null) {
           context = new Context();
           context.setToken(tok);
        }
        return (new ClassDecl(context,defType,decls)).setToken(tok);
    }

    public HaskellObject buildInstDecl(Token tok,Context context,HaskellObject defType,List<HaskellDecl> decls){
        if (context == null) {
           context = new Context();
           context.setToken(tok);
        }
        return (new InstDecl(context,defType,decls)).setToken(tok);
    }

    public HaskellObject buildDefaultDecl(Token tok,HaskellObject ho){
        List<HaskellObject> types = this.unApply(ho);
        List<Cons> tycos = new Vector<Cons>();
        if (types.size()>2) {
            types.remove(0);
        }
        for (HaskellObject type : types){
            if (type instanceof Cons) {
                Cons co = (Cons)type;
                co.setTYCONS();
                tycos.add(co);
            } else {
                HaskellError.output(type,"simple type constructor expected");
            }
        }
        return (new DefaultDecl(tycos)).setToken(tok);
    }

    public HaskellObject buildSynTypeDecl(Token tok,HaskellObject defType,HaskellObject type){
        return (new SynTypeDecl(defType,type)).setToken(tok);
    }

    public HaskellObject buildDerivings(Token tok,List<Cons> deris){
        return (new Derivings(deris)).setToken(tok);
    }

    public HaskellObject buildExcla(Token tok,HaskellObject type){
        return (new StrictnessFlag(type)).setToken(tok);
    }
}


