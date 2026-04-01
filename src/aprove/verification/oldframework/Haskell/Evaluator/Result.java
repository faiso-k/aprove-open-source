/**
 *
 */
package aprove.verification.oldframework.Haskell.Evaluator;


public interface Result{
    public ResultKind getKind();
    public boolean isError();
    public boolean matched();
    public boolean interrupt();
}