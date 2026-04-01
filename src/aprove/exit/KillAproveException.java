package aprove.exit;

/**
 * This Exception is a replacement for directly calling {@link System#exit(int)}.
 * It is thrown in places where it is necessary to terminate AProVE.
 * It should only be catched in main methods.
 * 
 * When AProVE is executed standalone and this exception is catched,
 * {@link #runSystemExit()} should be called, to actually terminate AProVE with all its threads.
 * 
 * When AProVE is used as an Eclipse plug-in and this exception is catched,
 * {@link #runSystemExit()} should NOT be called as this would terminate the Eclipse application.
 * Instead, the exception should be handled appropriately.
 * 
 * WARNING: We need to make sure to catch {@link KillAproveException} before {@link Exception} or {@link Throwable} is catched.
 * If we don't do this, we are unable to handle this exception appropriately.
 * 
 * For example, you can use the following code snippet to ensure this Exception is properly propagated:
 * 
 *      try {
 *          // code throwing KillAproveException
 *      } catch (KillAproveException e) {
 *          throw e;
 *      } catch (Exception e) {
 *          // general Exception error handling
 *      }
 */
public class KillAproveException extends Exception {

    private final int exitCode;

    public KillAproveException(int exitCode) {
        this.exitCode = exitCode;
    }

    public KillAproveException(int exitCode, Throwable cause) {
        super(cause);
        this.exitCode = exitCode;
    }

    public void runSystemExit() {
        System.exit(exitCode);
    }
}
