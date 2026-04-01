/**
 *
 */
package aprove.verification.oldframework.Haskell.Evaluator;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;

public class GenResult extends TermResult {
    HaskellObject instance;
    Var var;

    public GenResult(Var var,HaskellObject instance){
        super(var,((BasicTerm)instance).getSubtermNumber());
        this.var = var;
        this.instance = instance;
    }

    @Override
    public ResultKind getKind(){
        return ResultKind.GENERALIZE;
    }

    public Var getVariable(){
        return this.var;
    }

    public HaskellObject getInstance(){
        return this.instance;
    }

}