package aprove.cli;

import java.io.*;
import java.net.*;
import java.util.*;
import java.util.logging.*;

import aprove.input.*;
import aprove.prooftree.Export.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.Parameters.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Annotators.*;
import aprove.verification.oldframework.Input.TypeAnalyzers.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.ObligationFactories.*;

public class Server implements Runnable {
    /*
     * Request protocol:
     * numlines
     * filename
     * timeout
     * query
     *   where
     * - numlines is 1, 2 or 3 (if less than 3, the last 3-numlines
     *   lines should not be sent and are assumed to be default)
     * - filename is the name of a file, relative to the server's working dir
     * - timeout is the (wall-clock) timeout in milliseconds
     * - query is the prolog query to look at.
     *
     * Response format: One of
     * YES/NO/MAYBE
     * <html proof>
     *  -- or --
     * ERROR
     *  -- or --
     * TIMEOUT
     * OK
     *
     * Currently, strategy and other parameters are not variable
     * and hardcoded in the values below.
     */
    static final int THE_PORT = 5250;
    private static final String THE_STRATEGY = "aprove.Auto.current";
    private static final Level LOG_LEVEL = Level.WARNING;
    private static final Logger log = Logger.getLogger("aprove.Server");

    private int port;
    private volatile boolean running;
    private ServerSocket listener;

    public Server(int port) {
        this.port = port;
    }

    @Override
    public void run() {
        try {
            this.doRun();
        } catch (Exception e) {
            Server.log.log(Level.SEVERE, "Server main loop crashing", e);
        }
    }

    private void doRun() throws IOException {
        Server.log.info("Server starting up");
        this.running = true;

        this.listener = new ServerSocket(this.port);
        while(this.running) {
            Server.log.fine("Waiting for a connection...");
            Socket client;
            try {
                client = this.listener.accept();
            } catch (SocketException expectedDuringShutdown) {
                return;
            }
            new RequestHandler(client, this).start();
        }
    }

    public void shutdown() {
        this.running = false;
        try {
            this.listener.close();
        } catch (IOException nothingICanDo) {
        }
    }

    public static void main(String argv[]) {
        doMain();
    }

    public static void doMain() {
        Logger rootLogger = Logger.getLogger("");
        rootLogger.setLevel(Server.LOG_LEVEL);
        // todo: Potentially disable the stderrHandler?
        try {
            rootLogger.addHandler(new FileHandler("server.log"));
        } catch (IOException e) {
            System.err.println("Warning: Error setting up logging:");
            e.printStackTrace();
        }

        new Server(Server.THE_PORT).run();
    }


    private static class RequestHandler extends Thread {
        private static final ExtensionTypeAnalyzer typeAnalyzer = new ExtensionTypeAnalyzer();
        private static final DefaultAnnotator annotator = new DefaultAnnotator();
        private static final ObligationFactory obligationFactory = new MetaObligationFactory();


        private final Socket sock;
        private final Server myServer;

        private BufferedReader reader;
        private PrintWriter writer;


        public RequestHandler(Socket socket, Server myServer) {
            this.sock = socket;
            this.myServer = myServer;
        }

        @Override
        public void run() {
            try {
                String error = this.doRun();
                if (error != null) {
                    Server.log.warning(error);
                    this.writer.println("ERROR");
                    this.writer.flush();
                }
            } catch (Exception e) {
                Server.log.log(Level.WARNING, "Unexpected error in client", e);
                this.writer.println("ERROR");
                this.writer.flush();
            }

            try {
                this.sock.close();
            } catch (IOException nothingToSeeHereMoveAlong) {
                // Nothing to do
            }
        }

        /**
         * @return an error string on error, null on success.
         */
        private String doRun() throws IOException, InterruptedException, SourceException {
            this.reader = new BufferedReader(
                    new InputStreamReader(this.sock.getInputStream()));
            this.writer = new PrintWriter(this.sock.getOutputStream());

            String line = this.reader.readLine();
            if (line == null) {
                return "Unexpected EOF";
            }
            if (line.equals("SHUTDOWN")) {
                Server.log.info("Shutdown request from client");
                this.myServer.shutdown();
                this.writer.println("ACK");
                this.writer.flush();
                return null;
            }

            int numArgs = Integer.parseInt(line);
            if (numArgs < 1 || numArgs > 3) {
                return "Invalid NumArgs from client: only 1, 2 or 3 supported";
            }


            String fileName;
            int timeout = 0;
            String query = null;

            fileName = this.reader.readLine();
            if (fileName == null) {
                return "unexpected EOF";
            }
            if (numArgs > 1) {
                String timeoutLine = this.reader.readLine();
                if (timeoutLine == null) {
                    return "unexpected EOF";
                }
                try {
                    timeout = Integer.parseInt(timeoutLine)*1000-1000;
                } catch (NumberFormatException e) {
                    return "Invalid timeout: '" + timeoutLine + "'";
                }
            }
            if (numArgs > 2) {
                query = this.reader.readLine();
                if (query == null) {
                    return "unexpected EOF";
                }
            }

            return this.doProcess(fileName, timeout, query);
        }

        private String doProcess(String fileName, int timeout, String query) throws InterruptedException, SourceException {

            Server.log.info("Starting processing on " + fileName + " (" + timeout + ", " + query + ")");

            StrategyProgram program = EasyInput.loadStrategyModule(Server.THE_STRATEGY);

            // run the machine
            Pair<ObligationNode, List<BasicObligationNode>> rootAndPositions =
                this.produceProblem(fileName, query);
            ObligationNode root = rootAndPositions.x;
            StrategyExecutionHandle handle = Machine.theMachine.start(
                    null, program, rootAndPositions.y, null);

            // wait for the machine to finish
            boolean finished = false;
            if (timeout > 0) {
                finished = handle.waitForFinish(timeout);
            } else {
                handle.waitForFinish();
                finished = true;
            }

            // return result to client
            if (finished) {
                // proof finished within time
                this.writer.println(root.getTruthValue());
                this.writer.flush();
                ObligationAndStrategy rootProgram = new ObligationAndStrategy(root, rootAndPositions.y, program, fileName, 0);
                this.writer.println(new GenericExportManager(rootProgram ,false).export(new HTML_Util()));
                this.writer.flush();
            } else {
                // timed out
                Server.log.info("Aborted after " + timeout + " millis");
                this.writer.println("TIMEOUT");
                this.writer.flush();
                handle.stop("timeout from server");
                this.writer.println("OK");
                this.writer.flush();
            }
            return null;
        }

        private Pair<ObligationNode, List<BasicObligationNode>> produceProblem(
                String fileName, String query) throws SourceException {
            Input input = new FileInput(new File(fileName));
            TypedInput typedInput = RequestHandler.typeAnalyzer.analyze(input);
            AnnotatedInput annotatedInput = RequestHandler.annotator.annotate(typedInput);
            return RequestHandler.obligationFactory.getRootAndPositions(annotatedInput);
        }
    }
}
