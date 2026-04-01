package aprove.verification.oldframework.Input;

import java.io.*;

public class StreamInput extends Input.InputSkeleton implements Input {

    protected BufferedReader reader;
    protected String ext;

    public StreamInput(final InputStream stream) {
        this(stream, false);
    }

    public StreamInput(final InputStream stream, final boolean extOnStream) {
        this.reader = new BufferedReader(new InputStreamReader(stream));
        if (extOnStream) {
            try {
                this.ext = this.reader.readLine().trim();
            } catch (final IOException e) {
                this.ext = "<stream>";
            }
        } else {
            this.ext = "<stream>";
        }
    }

    @Override
    public String getString() {
        throw new RuntimeException("AProVE internal error: string from stream not supported");
    }

    @Override
    public String getPath() {
        try {
            return new File(".").getCanonicalPath();
        } catch (final IOException e) {
            return ".";
        }
    }

    @Override
    public String getName() {
        return "<stream>";
    }

    @Override
    public String getExtension() {
        return this.ext;
    }

    @Override
    public Reader getContent() {
        return this.reader;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public BufferedInputStream getInputStream() throws FileNotFoundException {
        throw new RuntimeException("not supported");
    }

}
