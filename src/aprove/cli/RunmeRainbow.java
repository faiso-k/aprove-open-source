package aprove.cli;

import aprove.exit.*;
import aprove.runtime.*;

/**
 * Runme file for batch testing with rainbow/color certification
 * @author Ulrich Schmidt-Goertz
 */
public class RunmeRainbow {

    public static void main(String[] args) {
        try {
            doMain(args);
        } catch (KillAproveException e) {
            e.runSystemExit();
        }
    }

    private static void doMain(String[] args) throws KillAproveException {
        if (Options.certifier.isA3pat()) {
            System.err.println("Warning: Flag a3pat is set, results may be compromised");
        }
        RunmeCertifyCommon.theMain(args, Certifier.RAINBOW);
    }
}
