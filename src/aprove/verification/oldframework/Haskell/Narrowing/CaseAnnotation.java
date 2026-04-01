package aprove.verification.oldframework.Haskell.Narrowing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;

public class CaseAnnotation extends Annotation {
    List<HaskellSubstitution> substitutions;

    public CaseAnnotation(){
        this.setSubstitutions(new Vector<HaskellSubstitution>());
    }

    @Override
    public Mode getMode(){
        return Mode.CASE;
    }

    public void setSubstitutions(List<HaskellSubstitution> substitutions){
        this.substitutions = substitutions;
    }

    public List<HaskellSubstitution> getSubstitutions(){
        return this.substitutions;
    }

    @Override
    public String toString(){
        return "$$";
    }
}

