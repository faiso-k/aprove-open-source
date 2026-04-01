package aprove.logging;

import java.io.*;
import java.nio.charset.*;
import java.util.concurrent.atomic.*;

/**
 * Multiplexes different streams (mstreams) into one output stream (ostream).
 * <p>
 * This is done by wrapping each write to an mstream into a packet. The format
 * was chosen so that the ostream stays human readable, as long as the payload
 * of the mstreams is human readable.
 *
 * <h3>Description of the MOSTREAM format</h3>
 * The ostream output consists of a MULTIPLEX_START byte sequence followed by
 * zero or more packets. When parsing MOSTREAM data, anything before the
 * MULTIPLEX_START sequence has to be ignored.
 *
 * A packet has the following format:
 * <p>
 * <code>PACKET_START &lt;type&gt; &lt;id&gt; SEPERATOR &lt;size&gt;
 * SEPERATOR &lt;data&gt;</code>
 * <p>
 * <ul>
 * <li>PACKET_START is a '\n'
 * <li>SEPERATOR is a ':'
 * <li>&lt;type&gt; is a single byte, describing the type of the message
 * <li>&lt;id&gt; is a 8-digit, 0-padded, lowercase hex number giving the
 *      stream id.
 * <li>&lt;size&gt; is a 8-digit, 0-padded, lowercase hex number giving the
 *      length of the data section in bytes
 * <li>&lt;data&gt; is the raw (possible binary) data
 * </ul>
 *
 * There are three types of messages:
 * <ul>
 * <li>OPEN ('&lt;'): Creates a new stream with stream id &lt;id&gt; and
 *      name given in the data section (UTF-8 encoded).
 * <li>CLOSE ('&gt;'): Closes the stream &lt;id&gt;. The data section
 *      is ignored.
 * <li>DATA ('$'): Writes data into stream &lt;id&gt;.
 * </ul>
 */
public class OutputStreamMultiplexer implements IMultiOutput {

    private final static Charset STRING_CHARSET =
        Charset.forName("UTF-8");

    public final static byte[] MULTIPLEX_START =
        "\n@@@@_MULTIPLEX_START_@@@@\n".getBytes(OutputStreamMultiplexer.STRING_CHARSET);
    public final static byte PACKET_START = '\n';
    public final static byte TYPE_OPEN = '<';
    public final static byte TYPE_CLOSE = '>';
    public final static byte TYPE_DATA = '$';
    public final static byte SEPERATOR = ':';

    final AtomicInteger nextId = new AtomicInteger();
    final OutputStream outStream;
    final Object outStreamLock;

    private OutputStreamMultiplexer(OutputStream outStream) {
        this.outStream = outStream;
        this.outStreamLock = new Object();
    }

    public static OutputStreamMultiplexer create(OutputStream outStream) throws IOException {
        OutputStreamMultiplexer om = new OutputStreamMultiplexer(outStream);
        om.outStream.write(OutputStreamMultiplexer.MULTIPLEX_START);
        return om;
    }

    public static OutputStreamMultiplexer create(PrintStream outStream) {
        try {
            return OutputStreamMultiplexer.create((OutputStream)outStream);
        } catch (IOException e) {
            /* a PrintStream never throws an IOException */
        }
        throw new RuntimeException("This code should never be reached!");
    }

    /* (non-Javadoc)
     * @see aprove.logging.OM#openStream(java.lang.String)
     */
    @Override
    public OutputStream openStream(String name) throws IOException {
        int id = this.nextId.getAndIncrement();
        this.writePacket(id, OutputStreamMultiplexer.TYPE_OPEN, this.toBytes(name));
        return new MOStream(this, id);
    }

    /**
     * Creates a new multiplexed stream and wraps it in a Writer.
     * <p>
     * Uses UTF-8 encoding.
     */
    public Writer openWriter(String name) throws IOException {
        return new OutputStreamWriter(this.openStream(name), OutputStreamMultiplexer.STRING_CHARSET);
    }

    void writePacket(int id, byte type, byte[] data) throws IOException {
        this.writePacket(id, type, data, 0, data.length);
    }

    void writePacket(int id, byte type, byte[] data, int off, int len) throws IOException {
        if (off < 0 || len < 0 || off + len > data.length) {
            throw new IndexOutOfBoundsException();
        }
        synchronized(this) {
            this.outStream.write(OutputStreamMultiplexer.PACKET_START);
            this.outStream.write(type);
            this.outStream.write(this.toBytes(id));
            this.outStream.write(OutputStreamMultiplexer.SEPERATOR);
            this.outStream.write(this.toBytes(len));
            this.outStream.write(OutputStreamMultiplexer.SEPERATOR);
            this.outStream.write(data, off, len);
        }
    }

    void writeData(int id, byte[] b, int off, int len) throws IOException {
        this.writePacket(id, OutputStreamMultiplexer.TYPE_DATA, b, off, len);
    }

    public void close() throws IOException {
        this.outStream.close();
    }

    /**
     * Closes the multiplexed stream <code>id</code>.
     */
    void close(int id) throws IOException {
        this.writePacket(id, OutputStreamMultiplexer.TYPE_CLOSE, new byte[0]);
    }

    /**
     * Flushes the multiplexed stream <code>id</code>.
     */
    void flush(int id) throws IOException {
        this.outStream.flush();
    }

    private byte[] toBytes(int i) {
        return this.toBytes(String.format("%08x", i));
    }

    private byte[] toBytes(String str) {
        return str.getBytes(OutputStreamMultiplexer.STRING_CHARSET);
    }

    private static class MOStream extends OutputStream {

        private final OutputStreamMultiplexer outMp;
        private final int multiplexId;

        MOStream(OutputStreamMultiplexer outMp,
                int multiplexId) {
            this.outMp = outMp;
            this.multiplexId = multiplexId;
        }

        @Override
        public void close() throws IOException {
            this.outMp.close(this.multiplexId);
        }

        @Override
        public void flush() throws IOException {
            this.outMp.flush(this.multiplexId);
        }

        @Override
        public void write(byte[] b, int off, int len) throws IOException {
            this.outMp.writeData(this.multiplexId, b, off, len);
        }

        @Override
        public void write(byte[] b) throws IOException {
            this.outMp.writeData(this.multiplexId, b, 0, b.length);
        }

        @Override
        public void write(int b) throws IOException {
            this.outMp.writeData(this.multiplexId, new byte[]{(byte)b}, 0, 1);
        }

    }
}
