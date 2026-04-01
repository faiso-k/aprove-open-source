package aprove.verification.oldframework.Haskell.Transformations;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Literals.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Typing.*;
import aprove.verification.oldframework.Utility.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 */
public class NumSplitVisitor extends HaskellVisitor {
     Stack<Boolean> rep;
     Stack<HaskellObject> hos;
     HaskellPat last;
     Var lastVar;
     Module curModule;
     int count;
     boolean allrep;
     List<HaskellEntity> currentEntities;
     Prelude prelude;

     public NumSplitVisitor(Module curModule,List<HaskellEntity> currentEntities,Prelude prelude){
         this.currentEntities = currentEntities;
         this.curModule = curModule;
         this.prelude = prelude;
         this.count = 0;
         this.allrep = false;
         this.hos = new Stack<HaskellObject>();
         this.rep = new Stack<Boolean>();
         this.last = null;
     }

     public List<HaskellObject> getCopies(){
         return this.hos;
     }

     public HaskellPat getNumPattern(){
         return this.last;
     }

     public Var getVariable(){
         return this.lastVar;
     }

     public Var newPatVar(HaskellType type){
        HaskellEntity e = null;
        if (this.count >= this.currentEntities.size()){
           e = new VarEntity(this.prelude.buildUniqueName(),this.curModule,null,null,true);
           this.currentEntities.add(e);
        } else {
           e = this.currentEntities.get(this.count);
        }
        this.count++;
        Var var = new Var(new HaskellNamedSym(e));
        var.setTypeTerm(type);
        return var;
     }

     @Override
    public HaskellObject caseBindPat(BindPat ho){
        if (this.allrep){
            Var var = this.newPatVar(ho.getTypeTerm());
            this.hos.push(var);
            return ho;
        }
        this.hos.push(ho.getVariable());
        this.allrep = true;
        this.last = ho.getSubPattern();
        this.lastVar = ho.getVariable();
        return Copy.deep(ho.getVariable());
     }

     @Override
    public HaskellObject casePlusPat(PlusPat ho) {
        return this.forLit(ho);
     }

     @Override
    public boolean guardPlusPat(PlusPat ho)                     { return false; }
     @Override
    public boolean guardBindPat(BindPat ho)                     { return false; }


     public HaskellObject forLit(HaskellPat ho){
        Var var = this.newPatVar(ho.getTypeTerm());
        this.hos.push(var);
        if (this.allrep) {
            return ho;
        }
        this.allrep = true;
        this.last = ho;
        this.lastVar = var;
        return Copy.deep(var);
     }

     @Override
    public HaskellObject caseIntegerLit(IntegerLit ho) {
        return this.forLit(ho);
     }

     @Override
    public HaskellObject caseFloatLit(FloatLit ho) {
        return this.forLit(ho);
     }

     @Override
    public HaskellObject caseCharLit(CharLit ho) {
        return this.forLit(ho);
     }

     @Override
    public HaskellObject caseCons(Cons ho){
        Var var = this.newPatVar(ho.getTypeTerm()) ;
        this.hos.push(this.allrep ? var : Copy.deep(ho));
        return ho;
     }

     @Override
    public HaskellObject caseVar(Var ho){
        this.hos.push(Copy.deep(ho));
        return ho;
     }

     @Override
    public void fcaseApply(Apply ho){
        this.rep.push(this.allrep);
     }

     @Override
    public HaskellObject caseApply(Apply ho){
        HaskellObject arg = this.hos.pop();
        HaskellObject func = this.hos.pop();
        if (this.rep.pop()) {
           this.hos.push(this.newPatVar(ho.getTypeTerm()));
        } else {
           this.hos.push(ho.hoCopy(new Apply(func,arg)));
        }
        return ho;
     }

     public List<HaskellPat> applyTo(List<HaskellPat> pats)   {
         List<HaskellPat> res = this.listWalk(pats,this);
         return res;
     }
}
