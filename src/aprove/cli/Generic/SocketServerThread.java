package aprove.cli.Generic;

import java.io.*;
import java.net.*;
import java.util.concurrent.atomic.*;

import aprove.exit.*;

/**
 * Class for implementing a basic SocketServer for problems.
 *
 * Every connection on the socket spawns a thread that waits for a problem,
 * then processes the problem (aborting when a 'q' is read on the socket),
 * and prints the result back on the connection, then closes it.
 *
 * The passed CommandLineOptions instance defines how problems should be handled.
 *
 * @author bearperson
 * @version $Id$
 */
class SocketServerThread extends Thread {

    public static void runServer(final CommandLineOptions opts) throws KillAproveException {
        try (final ServerSocket serverSock = new ServerSocket()) {
            serverSock.setReuseAddress(true);
            final SocketAddress bindAddr = new InetSocketAddress(opts.getPort());
            serverSock.bind(bindAddr);
            while (true) {
                final Socket client = serverSock.accept();
                new SocketServerThread(client, opts).start();
            }
        } catch (final IOException somethingWrong) {
            somethingWrong.printStackTrace();
            throw new KillAproveException(1);
        }
    }

    protected static final AtomicInteger workerThreads = new AtomicInteger(0);

    private final Socket conn;
    private final CommandLineOptions opts;
    private ProblemExecutor executor;

    public SocketServerThread(final Socket connection, final CommandLineOptions defaultOpts) {
        super("Socket server thread");
        this.conn = connection;
        // Clone options, so we can modify if we have to
        this.opts = defaultOpts.clone();
    }

    @Override
    public void run() {
        BufferedReader input = null;
        PrintWriter output = null;
        try {
            input = new BufferedReader(new InputStreamReader(this.conn.getInputStream()));
            output = new PrintWriter(this.conn.getOutputStream(), false);
            this.runProblem(input, output);
            output.flush();
        } catch (final IOException ohWell) {
            ohWell.printStackTrace();
        } finally {
            // Do cleanup to release resources. Everything has already been flushed.

            /* NOTE: we need to close the socket first, even if it seems counter-intuitive.
             * this aborts the SocketAborterThread, which otherwise would hold a lock
             * preventing us from doing input.close().
             */
            try {
                this.conn.close();
            } catch (final IOException justCleanup) {
            }
            if (input != null) {
                try {
                    input.close();
                } catch (final IOException justCleanupDamnit) {
                }
            }
            if (output != null) {
                output.close();
            }
        }
    }

    public void runProblem(final BufferedReader input, final PrintWriter output) throws IOException {
        String problem;
        try {
            problem = InputUtil.readProblem(input, this.opts, false);
        } catch (final IllegalArgumentException badOpts) {
            output.println("+ERROR: Bad option: " + badOpts);
            return;
        }

        if (this.opts.isSynchroneous() && SocketServerThread.workerThreads.get() > 0) {
            output.println("+ERROR: Already busy, and synchroneous mode was requested");
            return;
        }

        final Reader problemReader = new StringReader(problem);

        this.executor = this.opts.getExecutor(problemReader);
        if (this.executor == null) {
            output.println("+ERROR: Problem type not supported yet.");
            return;
        }
        try {
            SocketServerThread.workerThreads.incrementAndGet(); // track this worker
            this.executor.start();
            new SocketAborterThread(this.executor, input).start();
            this.executor.waitForResult();
            // If we're in synchroneous mode, try extra hard to make sure we are finished when we say so
            if (this.opts.isSynchroneous()) {
                try {
                    this.executor.join();
                } catch (final InterruptedException okayThenNot) {
                }
            }
        } finally {
            SocketServerThread.workerThreads.decrementAndGet(); // Done, untrack this worker
        }
        this.executor.printResult(output);
    }
}
