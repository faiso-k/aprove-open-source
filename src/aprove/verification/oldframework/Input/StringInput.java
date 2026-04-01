/*
 * Created on Jan 7, 2005
 */
package aprove.verification.oldframework.Input;

import java.io.*;

/**
 * @author rabe
 */
public class StringInput extends Input.InputSkeleton {

    protected String content;
    protected String name;
    protected String ext;

    public StringInput(final String content) {
        this(content, "<string>", false);
    }

    public StringInput(final String content, final String name) {
        this(content, name, false);
    }

    public StringInput(final String content, final String name, final boolean extName) {
        this.name = name;
        this.content = content;

        if (extName) {
            this.ext = "<string>";
        }

    }

    public StringInput(final String content, final String name, final String extension) {
        this.content = content;
        this.name = name;
        this.ext = extension;
    }

    @Override
    public Reader getContent() {
        return new StringReader(this.getString());
    }

    @Override
    public String getName() {
        return this.name;
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
    public String getExtension() {
        return this.ext;
    }

    /**
     * @return the represented (un-encoded) string. Note that this method is overridden in Base64StringInput.
     */
    @Override
    public String getString() {
        return this.content;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public BufferedInputStream getInputStream() throws FileNotFoundException {
        return new BufferedInputStream(new ByteArrayInputStream(this.getString().getBytes()));
    }
}
