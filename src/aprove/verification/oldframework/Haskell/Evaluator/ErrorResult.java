/**
 *
 */
package aprove.verification.oldframework.Haskell.Evaluator;

import aprove.verification.oldframework.Haskell.*;

public class ErrorResult implements Result {

    ErrorType errorType;
    HaskellObject errStr;
    int errorFrameNumber;

    public ErrorResult(ErrorType errorType,HaskellObject errStr,int errorFrameNumber) {
        this.errorType = errorType;
        this.errStr = errStr;
        this.errorFrameNumber = errorFrameNumber;
    }

    @Override
    public ResultKind getKind(){
        return ResultKind.ERROR;
    }

    @Override
    public boolean isError(){
        return true;
    }

    @Override
    public boolean matched(){
        return false;
    }

    @Override
    public boolean interrupt(){
        return true;
    }

    public int getErrorFrameNumber() {
        return this.errorFrameNumber;
    }

    public ErrorType getErrorType() {
        return this.errorType;
    }

    public HaskellObject getErrStr() {
        return this.errStr;
    }

}