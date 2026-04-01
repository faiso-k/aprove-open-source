package aprove.verification.oldframework.Utility;

import java.io.*;

/**
 * A reader sequencing two readers.
 * @author cryingshadow
 * @version $Id$
 */
public class SequenceReader extends Reader {

    /**
     * The first reader.
     */
    private final Reader reader1;

    /**
     * The second reader.
     */
    private final Reader reader2;

    /**
     * Is the current reader the first one?
     */
    private boolean first;

    /**
     * A reader sequencing two readers.
     * @param r1 The first reader.
     * @param r2 The second reader.
     */
    public SequenceReader(Reader r1, Reader r2) {
        this.reader1 = r1;
        this.reader2 = r2;
        this.first = true;
    }

    @Override
    public void close() throws IOException {
        this.reader1.close();
        this.reader2.close();
    }

    @Override
    public int read(char[] cbuf, int off, int len) throws IOException {
        if (this.first) {
            int res = this.reader1.read(cbuf, off, len);
            if (res == -1) {
                this.first = false;
            } else {
                return res;
            }
        }
        return this.reader2.read(cbuf, off, len);
    }

}
