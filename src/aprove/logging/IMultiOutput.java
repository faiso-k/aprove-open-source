package aprove.logging;

import java.io.*;

public interface IMultiOutput {

    /**
     * Creates a new multiplexed stream and wraps it in a OutputStream.
     */
    public abstract OutputStream openStream(String name) throws IOException;

}