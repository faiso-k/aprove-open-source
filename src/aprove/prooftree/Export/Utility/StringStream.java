package aprove.prooftree.Export.Utility;

import java.io.*;

/**
 * Offers a string as an output stream.
 * @author Tim Rohlfs
 */
public class StringStream extends OutputStream {
    protected StringBuilder sb;

    public StringStream() {
        this.sb = new StringBuilder();
    }

    @Override
    public void write(int c) throws IOException {
        this.sb.append((char)c);
    }

    @Override
    public String toString() {
        return this.sb.toString();
    }
}
