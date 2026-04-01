package aprove.verification.oldframework.Haskell.Narrowing;

import aprove.verification.oldframework.Haskell.BasicTerms.*;

public class UniVarAnnotation extends Annotation{
    Var var;

    public UniVarAnnotation(Var var){
        this.setVar(var);
    }

    public void setVar(Var var){
        this.var = var;
    }

    public Var getVar(){
        return this.var;
    }

    @Override
    public Mode getMode(){
        return Mode.UNIVAR;
    }
}
