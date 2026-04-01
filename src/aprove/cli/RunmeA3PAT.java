package aprove.cli;

import aprove.exit.*;
import aprove.runtime.*;

/**
 * Runme file for batch testing with A3PAT certification
 * @author Ulrich Schmidt-Goertz
 */
public class RunmeA3PAT {

    public static void main(String[] args) {
        try {
            doMain(args);
        } catch (KillAproveException e) {
            e.runSystemExit();
        }
    }

    private static void doMain(String[] args) throws KillAproveException {
        if (Options.certifier.isRainbow()) {
            System.err.println("Warning: Flag rainbow is set, results may be compromised");
        }
        RunmeCertifyCommon.theMain(args, Certifier.A3PAT);
    }
}
