package aprove.cli;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.cli.ObligationCache.*;
import aprove.exit.*;
import aprove.input.*;
import aprove.prooftree.Export.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Export.Utility.Export_Util.*;
import aprove.runtime.*;
import aprove.strategies.Parameters.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Logic.*;
import gnu.getopt.*;

/**
 * This class implements the Aprove XML-RPC web service.
 *
 * @author Eric Bodden
 */
public class Batch {

    public static enum MODE {
        BOOL, PLAIN, HTML
    };

    public static String run(final String inputString,
        final String ext,
        final StrategyProgram strategyProgram,
        final MODE outputMode,
        final int timeout) {

        final Export_Util util;

        switch (outputMode) {
        case BOOL:
            util = new PLAIN_Util();
            break;
        case PLAIN:
            util = new PLAIN_Util();
            break;
        case HTML:
            util = new HTML_Util();
            break;
        default:
            util = new PLAIN_Util();
            return util.body(util.bold(util.fontcolor("USER ERROR: Invalid output mode!", Color.RED)));
        }

        //input check
        if (inputString == null || inputString.length() == 0) {
            return util.body(util.bold(util.fontcolor("USER ERROR: Empty input String!", Color.RED)));
        }
        if (ext == null || ext.length() == 0) {
            return util.body(util.bold(util.fontcolor("USER ERROR: Empty Extension!", Color.RED)));
        }
        if (timeout < 0) {
            return util.body(util.bold(util.fontcolor("USER ERROR: Timeout must be >= 0.", Color.RED)));
        }
        //

        final StringWriter writer = new StringWriter();
        final PrintWriter pw = new PrintWriter(writer);
        try {

            //generate input
            final Input input = new StringInput(inputString, "BatchInput", ext);

            final AProVE aprove = new AProVE(input);
            aprove.setStrategy(strategyProgram);
            aprove.setTimeout(1000L * timeout);

            final long startTime = System.nanoTime();
            final boolean res = aprove.run();
            final long duration = System.nanoTime() - startTime;

            //process result
            switch (outputMode) {
            case BOOL:
                if (res) {
                    pw.println("timed out");
                } else {
                    final YNM status = aprove.getRoot().getTruthValue().fallbackToYNM();
                    switch (status) {
                    case YES:
                        pw.println("true");
                        break;
                    case NO:
                        pw.println("false");
                        break;
                    case MAYBE:
                        pw.println("unknown");
                    }
                }
                break;
            case PLAIN:
            case HTML:
                if (res) {
                    pw.println("TIMEOUT");
                } else {
                    final TruthValue status = aprove.getRoot().getTruthValue();
                    pw.println(status);
                }
            }
            //process proof
            switch (outputMode) {
            case BOOL:
                //output duration (for other export utils, it's contained in the proof output)
                pw.println("Duration: " + (duration / 1000000) + "ms");
                break;
            case PLAIN:
            case HTML:
                pw.println(new GenericExportManager(aprove.getRoot(), "Batch problem", false).export(util));
            }
            return writer.toString();
        } catch (final Exception e) {
            //handle exception by dumping it
            String s = util.bold(util.fontcolor("ERROR: An exception occured.\n", Color.RED));
            s += Batch.extractExceptionTrace(e);
            pw.println(util.body(s));
            return writer.toString();
        }
    }

    /**
     * Extracts the trace from the excaption and returns its text.
     * @param e an exception
     * @return its trace
     */
    private static String extractExceptionTrace(final Exception e) {
        final ByteArrayOutputStream bos = new ByteArrayOutputStream();
        final PrintWriter out = new PrintWriter(bos);
        e.printStackTrace(out);
        out.flush();
        final String clean = bos.toString();
        return clean;
    }

    /**
     * make extension, delimiter, and timeout configurable
     */
    public static void main(final String[] argv) {
        try {
            doMain(argv);
        } catch (KillAproveException e) {
            e.runSystemExit();
        }
    }

    public static void doMain(final String[] argv) throws KillAproveException {
        Logger.getLogger("").setLevel(Level.OFF);
        final Getopt g = new Getopt("testprog", argv, "c:e:l:m:s:t:u:");
        g.setOpterr(false);
        String ext = "tes";
        String delimiter = ".";
        MODE mode = MODE.BOOL;
        int timeout = 0;
        int c;
        boolean needTimeout = false;
        StrategyProgram strategyProgram = null;
        BasicObligationCache.CACHE cMode = BasicObligationCache.CACHE.OFF;
        String cParam = null;
        while ((c = g.getopt()) != -1) {
            switch (c) {
            case 'c':
                final String[] carg = g.getOptarg().split(":", 2);
                final String cmode = carg[0];
                cParam = carg.length == 1 ? "0" : carg[1];
                if (cmode.equals("all")) {
                    cMode = BasicObligationCache.CACHE.ALL;
                } else if (cmode.equals("lru")) {
                    cMode = BasicObligationCache.CACHE.LRU;
                }
                break;
            case 'e':
                ext = g.getOptarg();
                break;
            case 'l':
                delimiter = g.getOptarg();
                break;
            case 'm':
                final String smode = g.getOptarg();
                if (smode.equals("bool")) {
                    mode = MODE.BOOL;
                } else if (smode.equals("plain")) {
                    mode = MODE.PLAIN;
                } else if (smode.equals("html")) {
                    mode = MODE.HTML;
                }
                break;
            case 's':
                final String strategyName = g.getOptarg();
                if (Main.IS_MODULE(strategyName)) {
                    strategyProgram = EasyInput.loadStrategyModule(strategyName);
                } else {
                    final File file = new File(strategyName);
                    try {
                        strategyProgram = EasyInput.loadStrategy(file.getCanonicalPath());
                    } catch (final IOException e) {
                        e.printStackTrace();
                    }
                }
                //              mode |= STRUCT_MODE;
                break;
            case 't':
                try {
                    timeout = Integer.parseInt(g.getOptarg());
                } catch (final NumberFormatException e) {
                    needTimeout = true;
                }
                break;
            }
        }
        BasicObligationCache.init(cMode, cParam);
        if (strategyProgram == null) {
            strategyProgram = EasyInput.loadStrategyModule("aprove.Auto.current");
        }
        try (final Scanner scanner = new Scanner(System.in)) {
            while (scanner.hasNextLine()) {
                // read timeout if needed
                if (needTimeout) {
                    final String line = scanner.nextLine();
                    timeout = Integer.parseInt(line);
                }
                final StringBuilder input = new StringBuilder();
                while (scanner.hasNextLine()) {
                    final String line = scanner.nextLine();
                    if (line.equals(delimiter)) {
                        break;
                    }
                    input.append(line);
                    input.append('\n');
                }
                if (input.length() == 0) {
                    throw new KillAproveException(0);
                }
                System.out.println(Batch.run(input.toString(), ext, strategyProgram, mode, timeout));
            }
        }
        throw new KillAproveException(0);
    }
}
