package aprove.verification.oldframework.Haskell.Narrowing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;

public class InstanceAnnotation extends Annotation{
    NarrowNode base;
    List<Var> vars;
    HaskellSubstitution tySubs;

    public InstanceAnnotation(NarrowNode base,List<Var> vars,HaskellSubstitution tySubs){
        this.setBase(base);
        this.setVars(vars);
        this.setTyMatchSubs(tySubs);
    }

    @Override
    public Mode getMode(){
        return Mode.INSTANCE;
    }

    public void setBase(NarrowNode base){
        this.base = base;
    }

    public NarrowNode getBase(){
        return this.base;
    }

    public void setVars(List<Var> vars){
        this.vars = vars;
    }

    public List<Var> getVars(){
        return this.vars;
    }

    @Override
    public String toString(){
        return ">"+this.base.num;
    }

    public HaskellSubstitution getTyMatchSubs() {
        return this.tySubs;
    }

    public void setTyMatchSubs(HaskellSubstitution tySubs) {
        this.tySubs = tySubs;
    }
}

