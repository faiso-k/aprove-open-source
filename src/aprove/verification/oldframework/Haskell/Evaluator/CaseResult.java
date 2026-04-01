/**
 *
 */
package aprove.verification.oldframework.Haskell.Evaluator;

import aprove.verification.oldframework.Haskell.BasicTerms.*;

public class CaseResult extends NENMIResult {
    Var var;

    public CaseResult(Var var){
        this.var = var;
    }

    @Override
    public ResultKind getKind(){
        return ResultKind.CASE;
    }

    public Var getVariable(){
        return this.var;
    }

}