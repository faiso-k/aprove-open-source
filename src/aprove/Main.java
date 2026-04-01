package aprove;

import java.io.*;
import java.util.logging.*;

import aprove.exit.*;
import aprove.logging.*;
import aprove.verification.oldframework.Utility.Profiling.*;
import gnu.getopt.*;

public class Main {

    public static boolean firstObligation = true;

    public static UI UI_MODE;

    public static void main(final String argv[]) {
        try {
            doMain(argv);
        } catch (KillAproveException e) {
            e.runSystemExit();
        }
    }

    private static void doMain(final String[] argv) throws KillAproveException {
        Logger.getLogger("").setLevel(Level.OFF);
        final String[] origArgv = new String[argv.length];
        System.arraycopy(argv, 0, origArgv, 0, argv.length);
        final Getopt g = new Getopt("testprog", argv, "u:");
        g.setOpterr(false);
        UI mode = UI.CLI;

        if (Globals.PROFILING || Globals.TRAINING) {
            AproveOutput.setMultiOutputFromParam("STDERR");
        }

        int c;
        while ((c = g.getopt()) != -1) {
            switch (c) {
                case 'u':
                    final String ui = g.getOptarg();
                    try {
                        mode = UI.valueOf(ui.toUpperCase());
                    } catch (final IllegalArgumentException e) {
                        System.err.println("Unknown user interface: " + ui + " - using default!");
                    }
                    break;
            }
        }
        Main.UI_MODE = mode;
        switch (mode) {
            case CLI:
                aprove.cli.Main.doMain(origArgv);
                break;
            case SRV:
                aprove.cli.Server.doMain();
                break;
            case BAT:
                aprove.cli.Batch.doMain(origArgv);
                break;
            case DIO:
                aprove.verification.diophantine.DiophantineMain.doMain(origArgv);
                break;
            default:
                throw new IllegalStateException("This Main class cannot handle UI mode " + Main.UI_MODE + "!");
        }

        if (Globals.PROFILING) {
            try {
                Profiling.getWriter().close();
            } catch (final IOException e) {
                System.err.println("Could not close \"profiling\" Writer");
            }
        }
    }

    public static enum UI {
        BAT, CLI, DIO, GUI, SRV
    }

}
