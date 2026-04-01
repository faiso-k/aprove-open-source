package aprove.cli;

import aprove.exit.*;

/**
 * Runme file for batch testing with CeTA certification
 */
public class RunmeCeTA {

    public static void main(String[] args) {
        try {
            doMain(args);
        } catch (KillAproveException e) {
            e.runSystemExit();
        }
    }

    private static void doMain(String[] args) throws KillAproveException {
        RunmeCertifyCommon.theMain(args, Certifier.CETA);
    }
}
