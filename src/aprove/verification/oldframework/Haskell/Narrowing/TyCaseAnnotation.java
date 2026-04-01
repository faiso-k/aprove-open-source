package aprove.verification.oldframework.Haskell.Narrowing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Typing.*;

public class TyCaseAnnotation extends Annotation {
    List<HaskellSubstitution> tySubstitutions;
    List<HaskellType> varTypes;
    VarEntity ve;

    public TyCaseAnnotation(VarEntity ve){
        this.ve = ve;
        this.setTySubstitutions(new Vector<HaskellSubstitution>());
        this.setVarTypes(new Vector<HaskellType>());
    }

    @Override
    public Mode getMode(){
        return Mode.TYCASE;
    }

    public void setTySubstitutions(List<HaskellSubstitution> tySubstitutions){
        this.tySubstitutions = tySubstitutions;
    }

    public VarEntity getVarEntity(){
        return this.ve;
    }

    public List<HaskellSubstitution> getTySubstitutions(){
        return this.tySubstitutions;
    }

    public List<HaskellType> getVarTypes(){
        return this.varTypes;
    }

    public void setVarTypes(List<HaskellType> varTypes){
        this.varTypes = varTypes;
    }

    @Override
    public String toString(){
        return "$$";
    }
}

