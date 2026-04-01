package aprove.verification.diophantine;

import aprove.cli.Generic.*;
import aprove.exit.*;

/**
 * Main method for the diophantine interface.
 * All functionality moved to
 * @see aprove.cli.Generic.GenericMain
 */
public class DiophantineMain {

    public static void main(String[] args) {
        try {
            doMain(args);
        } catch (KillAproveException e) {
            e.runSystemExit();
        }
    }

    public static void doMain(String[] args) throws KillAproveException {
        GenericMain.doMain(args, new DioOptions());
    }
}
