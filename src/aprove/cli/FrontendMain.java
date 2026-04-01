package aprove.cli;

import gnu.getopt.*;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.Globals.AproveVersion;
import aprove.exit.*;
import aprove.input.*;
import aprove.logging.config.*;
import aprove.prooftree.Export.*;
import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.verification.oldframework.Bytecode.Processors.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public abstract class FrontendMain<T extends FrontendMain.FrontendOpts> {

    /**
     * Record-like class holding all options that all frontends have in common.
     */
    static class FrontendOpts {

        /** Display proof. */
        boolean displayProof = false;

        /** Output directory for the resulting TRSs. */
        File outputdir = new File(".");

        /** Timeout. */
        int timeout = 60;

        /** Export the graph. */
        public boolean graphExport = false;

        String query = null;
    }

    T options;

    /**
     * @param longopts Some options that have to be known to the returned Getopt-instance.
     * @param argv The command line options.
     * @return The Getopt-instance used to parse the command line options.
     */
    abstract Getopt createGetopt(List<LongOpt> longopts, String[] argv);

    /** @return An object that holds the options for this frontend. */
    abstract T createFrontendOpts();

    /** @return The file extension of the input files handled by this frontend. */
    abstract String getExtension();

    /** @return The name of the strategy to use. */
    abstract String getStrategyName();

    /**
     * Allows subclasses to parse additional command line options.
     * @param g The command line options.
     * @param c The command line option that has to get parsed.
     */
    abstract void parseAdditionalCommandLineOption(Getopt g, int c) throws KillAproveException;

    /** Print out some useful help. */
    abstract void printHelp();

    /** Print out some useful information about the recognized command line options. */
    void printCmdOptionsInfo() {
        System.out.println(" -h, --help             print this help");
        System.out.println(" -o, --outputDir DIR    directory in which TRSs will be dumped (default '.')");
        System.out.println(" -t, --timeout SECONDS  timeout, in seconds (default 60)");
        System.out.println(" -p, --proof            print proof for steps from input to TRSs");
        System.out.println(" -g, --graph yes|no     export to Graph (default no)");
        System.out.println(" -q, --query QUERY      a query which tells AProVE what to analyze");
    }

    /**
     * @param g arguments for this call
     */
     private void parseCommandLineOptions(final Getopt g) throws KillAproveException {
        this.options = this.createFrontendOpts();

        int c;
        while ((c = g.getopt()) != -1) {
            switch (c) {
            case 'o':
                final String outputDir = g.getOptarg();
                final File outputDirFile = new File(outputDir);
                if (!outputDirFile.exists() || !outputDirFile.isDirectory()) {
                    System.err.println("Output directory does not exist/is no directoy, aborting.");
                    this.printHelp();
                    throw new KillAproveException(1);
                }
                this.options.outputdir = outputDirFile;
                break;
            case 'p':
                this.options.displayProof = true;
                break;
            case 't':
                final String timeout = g.getOptarg();
                try {
                    this.options.timeout = Integer.parseInt(timeout);
                } catch (final NumberFormatException e) {
                    System.err.println("Failed to parse timeout '" + timeout + "', using default 60 seconds.");
                }
                break;
            case 'h':
                this.printHelp();
                break;
            case 'g':
                final String graph = g.getOptarg();
                if (FrontendMain.isTrueString(graph)) {
                    this.options.graphExport = true;
                } else if (FrontendMain.isFalseString(graph)) {
                    this.options.graphExport = false;
                } else {
                    System.err.println("Failed to parse graph export option '" + graph + "', using default 'false'.");
                }
                break;
            case 'q':
                options.query = g.getOptarg();
                break;
            default:
                this.parseAdditionalCommandLineOption(g, c);
            }
        }
    }

     /**
      * @param fileName name of the file containing our input
      * @return an input handle
      */
     private Input getInput(final String fileName) throws KillAproveException {
         final Input result = new FileInput(new File(fileName), null, null);
         if (!result.isAvailable()) {
             System.err.println("Cannot read from '" + result.getName() + "', aborting.");
             this.printHelp();
             throw new KillAproveException(1);
         } else if (!this.getExtension().equals(result.getExtension())) {
             System.err.println("Input file is not a " + this.getExtension() + " file, aborting.");
             this.printHelp();
             throw new KillAproveException(1);
         }
         return result;
     }

    /**
     * Check that the full set of options (after parsing all of them) is sane.
     */
    void checkOptionSanity(final Getopt g, final String[] args) throws KillAproveException {
        if (g.getOptind() >= args.length) {
            System.err.println("No input file, aborting.");
            this.printHelp();
            throw new KillAproveException(1);
        }
    }

     /**
      * Initializes the frontend.
      * @param args The command line arguments.
      * @return The name of and a handle for the input file.
      */
     Pair<String, Input> init(final String[] args) throws KillAproveException {
         aprove.Main.UI_MODE = aprove.Main.UI.CLI;

         final List<LongOpt> longopts = new LinkedList<>();
         longopts.add(new LongOpt("help", LongOpt.NO_ARGUMENT, null, 'h'));
         longopts.add(new LongOpt("outputDir", LongOpt.REQUIRED_ARGUMENT, null, 'o'));
         longopts.add(new LongOpt("timeout", LongOpt.REQUIRED_ARGUMENT, null, 't'));
         longopts.add(new LongOpt("proof", LongOpt.NO_ARGUMENT, null, 'p'));
         longopts.add(new LongOpt("graph", LongOpt.REQUIRED_ARGUMENT, null, 'g'));
         longopts.add(new LongOpt("query", LongOpt.REQUIRED_ARGUMENT, null, 'q'));
         final Getopt g = this.createGetopt(longopts, args);
         this.parseCommandLineOptions(g);
         this.checkOptionSanity(g, args);

         final String fileName = args[g.getOptind()];
         final Input input = this.getInput(fileName);
         if (this.options.query != null) {
             input.setProtoAnnotation(this.options.query);
         }
         return new Pair<>(fileName, input);
     }

     /**
      * Should be invoked by the main method of the frontend.
      * @param args The arguments that were passed to the frontend.
      */
     public void run(final String[] args) throws KillAproveException {
         final Pair<String, Input> p = this.init(args);
         final String fileName = p.x;
         final Input input = p.y;

         AProVE aprove;
         try {
             //Set up AProVE:
             LogConfig.init("cli");
             final Logger rootLogger = Logger.getLogger("");
             rootLogger.setLevel(Level.SEVERE);
             aprove = new AProVE(input);
             aprove.setTimeout(1000L * this.options.timeout);
             DumpProcessor.outputDir = this.options.outputdir.toString();

             //Choose the right (predefined) strategy:
             aprove.setStrategy(EasyInput.loadStrategyModule(this.getStrategyName()));

             final aprove.verification.oldframework.Utility.Timer timer = new aprove.verification.oldframework.Utility.Timer();
             timer.start();
             final boolean killed = aprove.run();
             timer.stop();

             if (killed) {
                 System.out.println("TIMEOUT");
             }

             //Now print the proof
             final ObligationNode root = aprove.getRoot();
             if (this.options.displayProof) {
                 System.out.println("");
                 new ParallelPlainExportManager(root, fileName, true).exportToStdOut();
             }
         } catch (final SourceException e) {
             System.err.println("Could not parse input file, aborting.");
             if (Globals.aproveVersion == AproveVersion.DEVELOPER_VERSION) {
                 e.printStackTrace();
             }
             throw new KillAproveException(1);
         } catch (final Exception e) {
             System.err.println("Could not display proof.");
             if (Globals.aproveVersion == AproveVersion.DEVELOPER_VERSION) {
                 e.printStackTrace();
             }
             throw new KillAproveException(1);
         }
     }

     /**
      * @param s some string
      * @return true iff we believe the string to mean "true"
      */
     static boolean isTrueString(final String s) {
         return ("1".equals(s) || "true".equals(s) || "t".equals(s) || "yes".equals(s) || "y".equals(s));
     }

     /**
      * @param s some string
      * @return true iff we believe the string to mean "false"
      */
     static boolean isFalseString(final String s) {
         return ("0".equals(s) || "false".equals(s) || "f".equals(s) || "no".equals(s) || "n".equals(s));
     }
}
