/**
 *
 */
package aprove.verification.oldframework.Haskell.Evaluator;

import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Typing.*;

public class TyCaseResult extends NENMIResult{
    HaskellType type,varType;
    VarEntity ve;
    int subtermID;


    public TyCaseResult(VarEntity ve,HaskellType varType,HaskellType type,int subtermID){
        this.type = type;
        this.varType = varType;
        this.ve = ve;
        this.subtermID = subtermID;
    }

    @Override
    public ResultKind getKind(){
        return ResultKind.TYCASE;
    }

    public HaskellType getType(){
        return this.type;
    }

    public HaskellType getVarType(){
        return this.varType;
    }

    public VarEntity getVarEntity(){
        return this.ve;
    }

    public int getSubtermID(){
        return this.subtermID;
    }

}