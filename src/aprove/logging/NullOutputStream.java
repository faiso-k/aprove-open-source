package aprove.logging;

import java.io.*;

/**
 * An output stream which silently discards any output
 */
public class NullOutputStream extends OutputStream {

    @Override
    public void write(int b) throws IOException {
        /* do nothing */
    }

}
