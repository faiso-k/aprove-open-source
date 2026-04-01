package aprove.verification.oldframework.Haskell.Narrowing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;

public class ConsAnnotation extends Annotation{
    HaskellObject cBase;
    List<Var> vars;

    public ConsAnnotation(HaskellObject cBase,List<Var> vars){
        this.setCBase(cBase);
        this.setVars(vars);
    }

    @Override
    public Mode getMode(){
        return Mode.CONS;
    }

    public void setCBase(HaskellObject cBase){
        this.cBase = cBase;
    }

    public HaskellObject getCBase(){
        return this.cBase;
    }

    public void setVars(List<Var> vars){
        this.vars = vars;
    }

    public List<Var> getVars(){
        return this.vars;
    }

    @Override
    public String toString(){
        return "";
    }

}

