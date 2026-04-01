package aprove.cli.Generic;

import java.io.*;

import aprove.exit.*;

/**
 * Main class for externally-accessible solvers.
 * Call from main with an instance of a CommandLineOptions subclass for your problem type
 *
 * @author Patrick Kabasci
 * @author Karsten Behrmann
 * @version $Id$
 */
public class GenericMain {
    public static void doMain(final String[] args, final CommandLineOptions solvingOpts) throws KillAproveException {
        int curIndex;
        try {
            // Set options and find first non-option argument
            curIndex = solvingOpts.setFromCommandLine(args);
        } catch (final IllegalArgumentException badOption) {
            System.err.println("Bad option specification: " + badOption);
            throw new KillAproveException(1);
        }

        if (solvingOpts.hasPort()) { // Server mode
            SocketServerThread.runServer(solvingOpts);
            return; // NOTREACHED
        }

        final String fileName = args[curIndex];
        if (!fileName.equals("-")) {
            // Process one file given as argument

            final Reader problemReader = new BufferedReader(GenericMain.openInput(fileName));
            GenericMain.runProblem(problemReader, solvingOpts, new PrintWriter(System.out));

        } else { // Interactive mode

            BufferedReader inputReader;
            PrintWriter outputWriter;
            String error = "<???>";
            String inputName;

            try {
                inputName = solvingOpts.getInputFileNameForInteractive();
                if (inputName == null) {
                    inputReader = new BufferedReader(new InputStreamReader(System.in));
                    inputName = "stdin";
                } else {
                    error = "read from " + inputName;
                    inputReader = new BufferedReader(new FileReader(inputName));
                }

                if (solvingOpts.getOutputFileNameForInteractive() == null) {
                    outputWriter = new PrintWriter(System.out, true);
                } else {
                    error = "write to " + solvingOpts.getOutputFileNameForInteractive();
                    try (final OutputStreamWriter writer =
                        new OutputStreamWriter(new FileOutputStream(solvingOpts.getOutputFileNameForInteractive()))) {
                        outputWriter = new PrintWriter(new BufferedWriter(writer), true);
                    }
                }
            } catch (final IOException e) {
                System.err.println("Cannot " + error + ":");
                System.err.println(e.toString());
                throw new KillAproveException(1);
            }

            /* We are probably reading from a fifo. This means several things:
             * - Opening for reading (above) will probably block until there's a writer opening it too
             * - at first, read() will block until stuff is written
             * - However, when the first writer has closed the fifo, read() will hit EOF (!)
             *   (the reasoning being that the writer didn't write any more, so it's logically the end of input)
             * - when another writer attaches, we'll start reading _his_ stuff, though.
             * - so in effect, a read() return of -1 means that there's nothing to do right now,
             *   if we wanted to block until there's something to do we'd need to close/reopen the input.
             */
            while (true) {
                final CommandLineOptions probOpts = solvingOpts.clone();
                String problem;
                try {
                    problem = InputUtil.readProblem(inputReader, probOpts, true);
                } catch (final IOException oops) {
                    System.err.println("Error reading problem from " + inputName + ":");
                    System.err.println(oops.getMessage());
                    throw new KillAproveException(1);
                } catch (final IllegalArgumentException badOpts) {
                    outputWriter.println("+ERROR: Bad option: " + badOpts);
                    outputWriter.println("#");
                    continue;
                }
                final Reader problemReader = new StringReader(problem);
                GenericMain.runProblem(problemReader, probOpts, outputWriter);
                outputWriter.println("#");
            }
        }
    }

    private static Reader openInput(final String fileName) throws KillAproveException {
        if (fileName.equals("/dev/stdin")) {
            return new InputStreamReader(System.in);
        }
        try {
            return new FileReader(fileName);
        } catch (final FileNotFoundException e) {
            System.err.println("Unable to open input file:");
            System.err.println(e.toString());
            throw new KillAproveException(1);
        }
    }

    private static void runProblem(final Reader problemReader, final CommandLineOptions opts, final PrintWriter output) throws KillAproveException {
        final ProblemExecutor de = opts.getExecutor(problemReader);
        if (de == null) {
            System.out.println("Not implemented yet.");
            throw new KillAproveException(1);
        } else {
            de.start();

            if (opts.hasTimeLimit()) {
                de.waitForResult(opts.getTimeLimit());
            } else {
                de.waitForResult();
            }

            de.printResult(output);
            output.flush();
        }
    }
}
