package aprove.verification.oldframework.Haskell.Transformations;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.HaskellProblem.Processors.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Patterns.*;

/**
 * @author Stephan Swiderski
 * @version $Id$
 */
public class NewTypeReduction extends BasicReduction {
    boolean pats = false;
//     Stack<Boolean> foundStack = new Stack<Boolean>();
    Stack<Integer> foundStack = new Stack<Integer>();
    Set<TyConsEntity> tces = new HashSet<TyConsEntity>();
    int current = 0;

    public boolean isNewTypeConstructor(HaskellObject ho){
        if (ho instanceof Apply){
            Apply apply = (Apply) ho;
            if (apply.getFunction() instanceof Cons){
                Cons cons = (Cons) apply.getFunction();
                TyConsEntity tce = (TyConsEntity) cons.getSymbol().getEntity().getParentEntity();
                if (tce.getNewType()){
                    this.tces.add(tce);
                    return this.isNewTypeConstructor(apply.getArgument());
                }
            }
            return false;
        } else {
            return (ho instanceof Var);
        }
    }

    @Override
    public void fcaseApply(Apply ho){
         if (this.pats) {
  //           boolean b = (!this.foundStack.peek()) && this.isNewTypeConstructor(ho);
 //            this.foundStack.push(Boolean.valueOf(b));
               if (this.foundStack.isEmpty()) {
                 if (this.isNewTypeConstructor(ho)){
                    this.foundStack.push(this.current);
                 }
             }
             this.current++;
         }
    }

    @Override
    public HaskellObject caseApply(Apply ho){
         if (this.pats) {
            this.current--;
            if (!this.foundStack.isEmpty() && (this.current == this.foundStack.peek())) {
                this.foundStack.pop();

            //if (this.foundStack.pop()){
                this.setChanged();
                IrrPat ip = new IrrPat(ho);
                ip.setTypeTerm(ho.getTypeTerm());
                this.proofAdd(ho,this.curModule,ip,this.curModule);
                return ip;
            }
         }
         return ho;
    }

    @Override
    public void fcaseLambdaExp(LambdaExp ho){
        this.pats = true;
    }

    @Override
    public void icaseLambdaExp(LambdaExp ho){
        this.pats = false;
    }

    @Override
    public void fcaseAltExp(AltExp ho){
        this.pats = true;
    }

    @Override
    public void icaseAltExp(AltExp ho){
        this.pats = false;
    }

    @Override
    public void fcaseHaskellRule(HaskellRule ho){
        this.pats = true;
    }

    @Override
    public void icaseHaskellRule(HaskellRule ho){
        this.pats = false;
    }

    public static boolean applyTo(Modules modules,HaskellProof hp,Abortion aborter){
        NewTypeReduction lr = new NewTypeReduction();
        lr.setHaskellProof(hp);
        lr.prelude = modules.getPrelude();
        //lr.foundStack.push(false);
        lr.forModules(modules);
        for (TyConsEntity tce : lr.tces){
            tce.setNewType(false);
            lr.setChanged();
        }
        return lr.wasChanged();
        //return true;
    }

}
