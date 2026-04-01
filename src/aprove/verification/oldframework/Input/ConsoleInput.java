package aprove.verification.oldframework.Input;

import java.io.*;

public class ConsoleInput implements Input {

    protected BufferedReader reader;
    protected String content = null;
    protected String ext = null;
    protected String protoAnnotation = null;

    public ConsoleInput(final String ext, final String protoAnnotation) {
        this.protoAnnotation = protoAnnotation;
        this.reader = new BufferedReader(new InputStreamReader(System.in));
        if (ext == null) {
            try {
                this.ext = this.reader.readLine().trim();
            } catch (final IOException e) {
                this.ext = "";
            }
        } else {
            this.ext = ext;
        }
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
        return "/dev/stdin";
    }

    @Override
    public String getExtension() {
        return this.ext;
    }

    @Override
    public Reader getContent() {
        return new StringReader(this.getString());
    }

    @Override
    public boolean isAvailable() {
        return true;
    }

    @Override
    public String getString() {
        if (this.content == null) {
            this.content = this.readString();
        }
        return this.content;
    }

    protected String readString() {
        final StringBuffer s = new StringBuffer("");
        while (true) {
            int c = 0;
            try {
                c = this.reader.read();
            } catch (final IOException e) {
            }
            if (c == -1) {
                return s.toString();
            }
            s.append((char) c);
        }
    }

    @Override
    public String getProtoAnnotation() {
        return this.protoAnnotation;
    }

    @Override
    public void setProtoAnnotation(final String protoAnnotation) {
        this.protoAnnotation = protoAnnotation;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public BufferedInputStream getInputStream() throws FileNotFoundException {
        return new BufferedInputStream(new ByteArrayInputStream(this.getString().getBytes()));
    }

}
