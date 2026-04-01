/**
 *
 */
package aprove.verification.oldframework.Haskell.Narrowing;

import aprove.verification.oldframework.Haskell.Expressions.*;

public class Tag {
    HaskellExp[] reps;
    boolean varExpPred;
    public Tag(){
       this.reps= new HaskellExp[]{null,null};
       this.varExpPred = false;
    }

    public void setRep(int i,HaskellExp exp){
       this.reps[i] = exp;
    }

    public HaskellExp getRep(int i){
       return this.reps[i];
    }

    public boolean setVarExpFreeAppPred(boolean varExpPred){
       this.varExpPred = varExpPred;
       return this.varExpPred;
    }

    public boolean getVarExpFreeAppPred(){
       return this.varExpPred;
    }

}