package aprove.verification.oldframework.Haskell.Transformations;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.HaskellProblem.Processors.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Collectors.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Patterns.*;
import aprove.verification.oldframework.Haskell.Substitutors.*;
import aprove.verification.oldframework.Utility.*;



/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * This reduktion reduces BindingPatterns ('x@pat') to a form without an '@'
 * also it replaces JokerPatterns ('_') with fresh variables
 */
public class BindingReduction extends BasicReduction {
    Stack<ReductionFrame> stack = new Stack<ReductionFrame>();

    private HaskellObject reduceBind(BindPat bp) {
         if (bp.getSubPattern() instanceof PlusPat) {
            return bp;
        }
         this.setChanged();

         // XXX DEBUG
         if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
             System.out.println("Binding Reduction: replace");
         }

         Module curModule = this.getCurModule();

         List<Var> freeVars = new Vector<Var>();
         HaskellPat pat = bp.getSubPattern();
         pat.visit(new FreeLocalVarCollector(freeVars));
         HaskellEntity bVarEntity = bp.getVariable().getSymbol().getEntity();
         for (Var var : freeVars){
             HaskellEntity e = var.getSymbol().getEntity();
             String name = this.getNextNewNameForVariable();
             VarEntity newVarEntity = new VarEntity(name,curModule,null,null,true);
             this.stack.peek().addEntity(newVarEntity);
             Var newVar = Copy.deep(var);
             newVar.getSymbol().setEntity(newVarEntity);
             this.stack.peek().putVarRep(e,newVar);
             this.stack.peek().removeEntity(e); // localframe without freeVarEntities
         }

         HaskellObject ho = Copy.deep(pat).visit(new BindPatSubstitutor());
         ho = (HaskellPat) this.stack.peek().replace(ho);
         this.stack.peek().removeEntity(bVarEntity);
         this.stack.peek().putVarRep(bVarEntity,ho);
         this.proofAdd(bp,curModule,pat,curModule);
         return pat;
     }

    @Override
    public HaskellObject casePlusPat(PlusPat pp) {
/*        Var var = pp.getVariable();
        IntegerLit il = pp.getInteger();
        if (this.plus == null){
            this.plus = this.prelude.getEntity(this,"Prelude","+",HaskellEntity.Sort.VAR);
        }
        HaskellType ht = this.prelude.buildArrow(var.getTypeTerm(),this.prelude.buildArrow(il.getTypeTerm(),pp.getTypeTerm()));
        HaskellObject res = new Var(new HaskellNamedSym(this.plus)).setTypeTerm(ht);
        res = this.prelude.buildApply(res,var);
        res = this.prelude.buildApply(res,il);
        */

        this.setChanged();
        String name = this.getNextNewNameForVariable();
        VarEntity newVarEntity = new VarEntity(name,this.curModule,null,null,true);
        this.stack.peek().addEntity(newVarEntity);
        Var newVar = new Var(new HaskellNamedSym(newVarEntity));
        newVar.setTypeTerm(pp.getTypeTerm());
        BindPat bp = new BindPat(newVar,pp);
        bp.setTypeTerm(pp.getTypeTerm());
        return bp;
    }

    @Override
    public boolean guardBindPat(BindPat bp){
        return (!(bp.getSubPattern() instanceof PlusPat));
    }

    @Override
    public HaskellObject caseBindPat(BindPat ho) {
        return this.reduceBind(ho);
    }

    @Override
    public HaskellObject caseJokerPat(JokerPat ho){
        String name = this.getNextNewNameForVariable();
        this.setChanged();
        VarEntity newVarEntity = new VarEntity(name,this.curModule,null,null,true);
        this.stack.peek().addEntity(newVarEntity);
        return new Var(new HaskellNamedSym(newVarEntity)).setTypeTerm(ho.getTypeTerm());
    }

    public void pushStack(){
         this.stack.push(new ReductionFrame());
    }

    public ReductionFrame popStack(){
         return this.stack.pop();
    }

    @Override
    public void fcaseLambdaExp(LambdaExp ho){
       this.pushStack();
    }

    @Override
    public HaskellObject caseLambdaExp(LambdaExp ho){
       this.popStack().replaceAndUpdate(ho);
       return ho;
    }

    @Override
    public void fcaseAltExp(AltExp ho){
       this.pushStack();
    }

    @Override
    public HaskellObject caseAltExp(AltExp ho){
       this.popStack().replaceAndUpdate(ho);
       return ho;
    }

    @Override
    public void fcaseHaskellRule(HaskellRule ho){
       this.pushStack();
    }

    @Override
    public HaskellObject caseHaskellRule(HaskellRule ho){
       this.popStack().replaceAndUpdate(ho);
       return ho;
    }

    public static boolean applyTo(Modules modules,HaskellProof hp,Abortion aborter){
        BindingReduction br = new BindingReduction();
        br.setAborter(aborter);
        br.setHaskellProof(hp);
        br.forModules(modules);
        return br.wasChanged();
        //return true;
    }



}
