package aprove.cli;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.exit.*;
import aprove.input.*;
import aprove.prooftree.Export.*;
import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.runtime.Options.JBCAnalysisOptions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.Parameters.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Annotations.*;
import aprove.verification.oldframework.Input.Annotators.*;
import aprove.verification.oldframework.Input.TypeAnalyzers.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.ObligationFactories.*;

/*
 * Main class compatible with the termination competition calling conventions.
 */
public class Runme {

    private final static ExtensionTypeAnalyzer typeAnalyzer = new ExtensionTypeAnalyzer();
    private final static DefaultAnnotator annotator = new DefaultAnnotator();
    private final static ObligationFactory obligationFactory = new MetaObligationFactory();
    private static final boolean PROFILING = false;

    public static void main(final String[] argv) throws SourceException, InterruptedException {
        try {
            doMain(argv);
        } catch (KillAproveException e) {
            e.runSystemExit();
        }
    }

    private static void doMain(final String[] argv) throws ParserErrorsSourceException,
                                                    SourceException,
                                                    InterruptedException,
                                                    KillAproveException {
        Logger.getLogger("").setLevel(Level.OFF);
        Options.embedHtmlProof = true;
        Options.defaultThreadingHasPriority = true;
        final long time = System.nanoTime();
        // unneeded: final int timeout = Integer.parseInt(argv[1]);
        if (Runme.PROFILING) {
            System.out.println("Parsing timeout: " + (System.nanoTime() - time) / 1000);
        }

        final String fileName = argv[0];
        final String query =
            (argv.length > 2 && !argv[2].startsWith("-P") && !argv[2].startsWith("-S") && !argv[2].startsWith("-J"))
                ? argv[2]
                    : null;

        String progName = "aprove.Auto.current";
        int index = query == null ? 2 : 3;

        if ((argv.length > index) && (argv[index].startsWith("-P"))) {
            aprove.input.Programs.haskell.Translator.setSearchPaths(argv[index].substring(2));
            index++;
        }
        if ((argv.length > index) && (argv[index].startsWith("-S"))) {
            // also give subdirectory for the strategy in argv
            progName = "aprove." + argv[index].substring(2);
        }
        // run the machine
        final Input input = new FileInput(new File(fileName));
        final TypedInput typedInput;
        try {
            typedInput = Runme.typeAnalyzer.analyze(input);
        } catch (final ParserErrorsSourceException e) {
            //            callRelease12(argv);
            System.err.println("ERROR\nError while parsing '" + fileName + "'");
            throw e;
        }
        if (Runme.PROFILING) {
            System.out.println("Parsing input: " + (System.nanoTime() - time) / 1000);
        }

        //        if (typedInput.getModedType().getLanguage().equals(Language.ETRS)) {
        //            callRelease12(argv);
        //        }

        final AnnotatedInput annotatedInput;
        try {
            annotatedInput = Runme.annotator.annotate(typedInput);
        } catch (final SourceException e) {
            System.out.println("ERROR\nError while annotating '" + fileName + "'");
            throw e;
        }
        if (query != null && annotatedInput.getAnnotation() instanceof JBCAnnotation) {
            annotatedInput.setAnnotation(new JBCAnnotation(query, "", HandlingMode.Termination));
        }
        if (Runme.PROFILING) {
            System.out.println("Annotating input: " + (System.nanoTime() - time) / 1000);
        }

        final Pair<ObligationNode, List<BasicObligationNode>> rootAndPositions =
            Runme.obligationFactory.getRootAndPositions(annotatedInput);
        final ObligationNode root = rootAndPositions.x;
        if (Runme.PROFILING) {
            System.out.println("Building root obligation: " + (System.nanoTime() - time) / 1000);
        }

        final StrategyProgram program;

        // always use strategy "main", which should ideally call a suitable heuristic
        final String stratName = "main";
        final UserStrategy startStrategy = new VariableStrategy(stratName);

        program = EasyInput.loadStrategyModule(progName);
        //        programInput = EasyInput.parseStrategy(timeout < 90 ? WST06_60 : WST06_300);
        if (Runme.PROFILING) {
            System.out.println("Loading strategy program: " + (System.nanoTime() - time) / 1000);
        }

        final StrategyExecutionHandle handle =
            Machine.theMachine.start(startStrategy, program, rootAndPositions.y, null);
        if (Runme.PROFILING) {
            System.out.println("Starting machine: " + (System.nanoTime() - time) / 1000);
        }

        // wait for the machine to finish
        try {
            handle.waitForFinish();
        } catch (final InterruptedException e) {
            System.out.println("ERROR\nunexpected interruption while running machine");
            throw e;
        }
        if (Runme.PROFILING) {
            System.out.println("Waiting for machine to finish: " + (System.nanoTime() - time) / 1000);
        }

        // ugly quickfix: this hack should NOT be necessary here!
        // TODO grok (i.e., really completely understand) the truth value
        // management of the proof tree
        if (!root.isTruthValueKnown()) {
            root.recursiveRepropagateTruthValues();
        }

        // print result
        System.out.println(root.getTruthValue().toWstString());
        System.out.flush();
        if (Runme.PROFILING) {
            System.out.println("Printing result: " + (System.nanoTime() - time) / 1000);
        }

        final ObligationAndStrategy rootProgram =
            new ObligationAndStrategy(root, rootAndPositions.y, program, fileName, 0);
        final ParallelHTMLExportManager expMan =
            new ParallelHTMLExportManager(rootProgram.getRoot(), rootProgram.getPathName());
        expMan.exportToStdOut();
        if (Runme.PROFILING) {
            System.out.println("Printing proof: " + (System.nanoTime() - time) / 1000);
        }
        throw new KillAproveException(0);
    }

    /*
    private static void callRelease12(String[] argv) {
        try {
            String cmd = "java -Xmx400m -cp aprove12.jar aprove.CommandLineInterface.Main -m wst -p html -t "+argv[1]+" "+(argv.length > 2 ? " -q '"+argv[2]+"' " : "")+argv[0];
            Process process = Runtime.getRuntime().exec(cmd);
            System.err.println(cmd);
            BufferedReader stdOut = new BufferedReader(new InputStreamReader(process.getInputStream()));
            while (true) {
                String line = stdOut.readLine();
                if (line == null) {
                    break;
                }
                System.out.println(line);
            }
        } catch (IOException e) {
            System.out.println("ERROR");
            e.printStackTrace();
            throw new KillAproveException(1);
        }
        throw new KillAproveException(0);
    }
     */
}
