package aprove.logging;

import java.io.*;

public class AproveOutput {

    private static IMultiOutput multiOut;

    public static void setMultiOutput(IMultiOutput multiOut) {
        AproveOutput.multiOut = multiOut;
    }

    /**
     * Helper method for unified handling in different main methods.
     *
     * Warning: This method may change System.out and System.err!
     */
    public static void setMultiOutputFromParam(String param) {
        try {
            if (param == null || param.equalsIgnoreCase("stderr")) {
                AproveOutput.setMultiOutput(OutputStreamMultiplexer.create(System.err));
                System.setErr(AproveOutput.openPrintStream("STDERR"));
            } else if (param.equals("-") || param.equalsIgnoreCase("stdin")) {
                AproveOutput.setMultiOutput(OutputStreamMultiplexer.create(System.out));
                System.setOut(AproveOutput.openPrintStream("STDOUT"));
            } else if (param.endsWith("/")) {
                System.err.println("Setting MultiOutput failed: Not implemented for directories!");
            } else {
                AproveOutput.setMultiOutput(OutputStreamMultiplexer.create(
                        new FileOutputStream(param)));
            }
        } catch (FileNotFoundException e) {
            System.err.println("Setting MultiOutput failed! " + e.getMessage());
        } catch (IOException e) {
            System.err.println("Setting MultiOutput failed! " + e.getMessage());
        }
    }

    public static IMultiOutput getMultiOutput() {
        return AproveOutput.multiOut;
    }

    public static boolean multiOutputEnabled() {
        return AproveOutput.multiOut != null;
    }

    public static OutputStream openStream(String name) throws IOException {
        if (AproveOutput.multiOut == null) {
            return new NullOutputStream();
        } else {
            return AproveOutput.multiOut.openStream(name);
        }
    }

    public static BufferedOutputStream openBufferedStream(String name) throws IOException {
        return new BufferedOutputStream(AproveOutput.openStream(name));
    }

    public static PrintStream openPrintStream(String name) {
        try {
            return new PrintStream(AproveOutput.openStream(name));
        } catch (IOException e) {
            return new PrintStream(new NullOutputStream()) {
                { this.setError(); }
            };
        }
    }

    public static Writer openWriter(String name) throws IOException {
        return AproveOutput.openWriter(name, false);
    }

    public static Writer openWriter(String name, boolean buffered) throws IOException {
        OutputStream os = AproveOutput.openStream(name);
        if (buffered) {
            os = new BufferedOutputStream(os);
        }
        return new OutputStreamWriter(os);
    }

    /**
     * Opens a stream for name, writes the data and closes the stream again.
     * @throws IOException
     */
    public static void writeBlob(String name, String data) throws IOException {
        Writer w = AproveOutput.openWriter(name);
        w.write(data);
        w.close();
    }
}
