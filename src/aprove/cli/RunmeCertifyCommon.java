package aprove.cli;

import java.io.*;
import java.util.logging.*;

import aprove.exit.*;
import aprove.input.*;
import aprove.logging.config.*;
import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.strategies.Parameters.*;
import aprove.verification.oldframework.Input.*;

/**
 * Common functionality for several certifiers for runme files (i.e.,
 * main classes) for batch testing with certification
 *
 * @author Ulrich Schmidt-Goertz
 */
public class RunmeCertifyCommon {

    public static void theMain(String[] args, Certifier certifier) throws KillAproveException {
        Options.certifier = certifier;

        String strategyName = certifier.getDefaultStrategyName();
        StrategyProgram strategyProgram = args.length > 2 ? EasyInput.loadStrategy(args[2]) : EasyInput.loadStrategyModule(strategyName);
        String fileName = "";
        int timeout = 60;
        try {
            fileName = args[0];
            timeout = Integer.parseInt(args[1]);
        } catch (RuntimeException e) {
            // handles both NumberFormatException and ArrayIndexOutOfBoundsException
            System.err.println("Usage: java -jar $JARFILE path/to/problem timeout(seconds)");
            throw new KillAproveException(1);
        }

        LogConfig.init("cli");
        Logger rootLogger = Logger.getLogger("");
        rootLogger.setLevel(Level.SEVERE);

        Input input = new FileInput(new File(fileName));
        if (!input.isAvailable()) {
            throw new IllegalArgumentException("Cannot read from "+input.getPath());
        }

        AProVE aprove;
        try {
            aprove = new AProVE(input);
        } catch (SourceException e) {
            System.err.println("Fatal parse error:");
            e.printStackTrace();
            throw new KillAproveException(1);
        }

        aprove.setTimeout(1000L*timeout);
        aprove.setStrategy(strategyProgram);

        boolean killed = aprove.run();

        if (killed) {
            System.out.println("KILLED");
        } else {
            ObligationNode root = aprove.getRoot();

            // ugly quickfix: this hack should NOT be necessary here!
            // TODO grok (i.e., really completely understand) the truth value
            // management of the proof tree
            if (!root.isTruthValueKnown()) {
                root.recursiveRepropagateTruthValues();
                if (root.isTruthValueKnown()) {
                    Logger log = Logger.getLogger("aprove.CommandLineInterface.RunmeCertifyCommon");
                    if (log.isLoggable(Level.WARNING)) {
                          log.warning("Truth value repropagation in proof tree changed value to "
                                  + root.getTruthValue().toWstString());
                    }
                }
            }

            System.out.println(root.getTruthValue().toWstString());
            try {
                ProofExport.CPF.export(root, fileName);
            } catch (Exception e) {
                e.printStackTrace();
            }
        }
        throw new KillAproveException(0);
    }
}
