/**
 *
 */
package aprove.verification.oldframework.Haskell.Evaluator;

public abstract class NENMIResult implements Result {

    @Override
    public boolean isError(){
        return false;
    }

    @Override
    public boolean matched(){
        return false;
    }

    @Override
    public boolean interrupt(){
        return true;
    }

}