/**
 *
 */
package aprove.verification.oldframework.Haskell.Evaluator;


public class MatchResult implements Result {
    boolean match;

    public MatchResult(){
        this.match = false;
    }

    public MatchResult(boolean match){
        this.match = match;
    }

    @Override
    public ResultKind getKind(){
        return ResultKind.FINISH;
    }

    @Override
    public boolean isError(){
        return false;
    }

    @Override
    public boolean matched(){
        return this.match;
    }

    @Override
    public boolean interrupt(){
        return false;
    }

}