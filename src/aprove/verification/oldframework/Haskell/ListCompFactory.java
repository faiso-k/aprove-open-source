package aprove.verification.oldframework.Haskell;

import java.util.*;

import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Collectors.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Qualifiers.*;
import aprove.verification.oldframework.Utility.*;

public class ListCompFactory implements DoCompFactory {

    HaskellEntity concatMap;
    //HaskellEntity monadBind;
    //HaskellEntity monadThen;
    HaskellEntity emptyList;
    Module module;
    EntityFrame entityFrame;
    int varCount;

    public ListCompFactory(HaskellEntity concatMap/*,HaskellEntity monadBind,HaskellEntity monadThen*/,HaskellEntity emptyList,Module module){
        this.concatMap = concatMap;
      //  this.monadBind = monadBind;
      //  this.monadThen = monadThen;
        this.emptyList = emptyList;
        this.entityFrame = null;
        this.module = module;
        this.varCount = 0;
    }

    public EntityFrame getLastEntityFrame(){
        return this.entityFrame;
    }

    @Override
    public HaskellExp buildMonadBind(HaskellPat pat,HaskellExp exp,HaskellExp next){
        /*List<HaskellPat> pats = new Vector<HaskellPat>();
        pats.add(pat);
        LambdaExp lexp = (LambdaExp) new LambdaExp(pats,next,new EntityFrame());
        return (HaskellExp)this.buildApplies(this.buildVar(this.monadBind),exp,lexp);*/
        return null;
    }

    @Override
    public HaskellExp buildMonadThen(HaskellExp exp,HaskellExp next){
    //    return (HaskellExp)this.buildApplies(this.buildVar(this.monadThen),exp,next);
        return null;
    }

    @Override
    public HaskellExp buildMonadLet(List<HaskellDecl> decls,HaskellExp res,LetQual lq){
        //return (HaskellExp)(new LetExp(decls,res,LetExp.LET)).setToken(lq.getToken());
        return null;
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
        EntityFrame ef = new EntityFrame.EntityFrameSkeleton(null,new EntityMap());
        List<AltExp> alts = new Vector<AltExp>();
        // pat -> next
        // _ -> []
        Set<HaskellEntity> hes = new HashSet<HaskellEntity>();
        pat.visit(new FreeEntityCollector(hes));
        EntityFrame aef = new EntityFrame.EntityFrameSkeleton(ef,new EntityMap(hes));
        alts.add((AltExp) new AltExp(pat,next,aef));
        alts.add((AltExp) new AltExp((HaskellPat) new JokerPat(),(HaskellExp) this.buildCons(this.emptyList),new EntityFrame.EntityFrameSkeleton(ef,new EntityMap())));
        List<HaskellPat> pats = new Vector<HaskellPat>();
        if (this.entityFrame != null) {
            this.entityFrame.setParentEntityFrame(aef);
        }
        Var var = this.buildFreshVar();
        pats.add(var);
        ef.addEntity(var.getSymbol().getEntity());
        LambdaExp lexp =(LambdaExp) new LambdaExp(pats,(HaskellExp) new CaseExp(Copy.deep(var),alts),ef);
        this.entityFrame = ef;
        return (HaskellExp)this.buildApplies(this.buildVar(this.concatMap),lexp,exp);
    }

    @Override
    public HaskellExp buildListCompGuard(HaskellExp exp,HaskellExp next){
        return (HaskellExp) new IfExp(exp,next,(HaskellExp) this.buildCons(this.emptyList));
    }

    @Override
    public HaskellExp buildListCompLet(List<HaskellDecl> decls,HaskellExp res,LetQual lq){
        return null;
        //return (HaskellExp)(new LetExp(decls,res,LetExp.LET)).setToken(lq.getToken());
    }


    public HaskellObject buildApplies(HaskellObject exp, HaskellObject... hos){
        for (int i=0;i<hos.length;i++){
            exp = new Apply(exp,hos[i]);
        }
        return exp;
    }

    public Var buildVar(HaskellEntity e){
        return new Var(new HaskellNamedSym(e));
    }

    public Cons buildCons(HaskellEntity e){
        return new Cons(new HaskellNamedSym(e));
    }

    public Var buildFreshVar(){
        this.varCount++;
        return new Var(new HaskellNamedSym(new VarEntity("lv"+this.varCount,this.module,null,null,true)));
    }

    public static HaskellExp buildListComp(HaskellExp cur,List<HaskellQual> list,HaskellEntity concatMap,HaskellEntity listCons,HaskellEntity emptyList,Module module,EntityFrame pef){;
        ListCompFactory df = new ListCompFactory(concatMap,emptyList,module);
        cur = new Apply(new Apply(df.buildCons(listCons),cur),df.buildCons(emptyList));
        for (int i = (list.size()-1);i>=0;i--){
            HaskellQual qu = list.get(i);
            cur = qu.toListComp(df,cur);
        }
        df.getLastEntityFrame().setParentEntityFrame(pef);
        return cur;
    }

}
