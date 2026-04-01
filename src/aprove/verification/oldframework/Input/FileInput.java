package aprove.verification.oldframework.Input;

import java.io.*;

public class FileInput extends Input.InputSkeleton implements Input {

    protected File file;
    protected String ext;

    public FileInput(final File file) {
        this(file, null, null);
    }

    public FileInput(final File file, final String ext) {
        this(file, ext, null);
    }

    public FileInput(final File file, final String ext, final String protoAnnotation) {
        this.file = file;
        this.ext = ext;
        this.protoAnnotation = protoAnnotation;
    }

    @Override
    public String getPath() {
        try {
            return this.file.getCanonicalPath();
        } catch (final IOException e) {
            return null;
        }
    }

    @Override
    public String getName() {
        return this.file.getName();
    }

    @Override
    public String getExtension() {
        if (this.ext == null) {
            return super.getExtension();
        }
        return this.ext;
    }

    @Override
    public Reader getContent() {
        return new StringReader(this.getString());
    }

    private Reader getReader() {
        try {
            final FileInputStream fileInputStream = new FileInputStream(this.file.getCanonicalPath());
            final BufferedInputStream bufferedInputStream = new BufferedInputStream(fileInputStream);
            return new InputStreamReader(bufferedInputStream);
        } catch (final FileNotFoundException e) {
            return null;
        } catch (final IOException e) {
            return null;
        }
    }

    @Override
    public String getString() {
        final StringBuilder s = new StringBuilder();
        final Reader reader = this.getReader();
        while (true) {
            int c = 0;
            try {
                c = reader.read();
            } catch (final IOException e) {
            }
            if (c == -1) {
                return s.toString();
            }
            s.append((char) c);
        }
    }

    @Override
    public boolean isAvailable() {
        return this.file.canRead();
    }

    @Override
    public boolean equals(final Object o) {
        final FileInput other = (FileInput) o;
        return this.file.equals(other.file);
    }

    @Override
    public int hashCode() {
        return this.file.hashCode();
    }

    @Override
    public String toString() {
        return this.file.toString();
    }

    public File getFile() {
        return this.file;
    }

    /**
     * {@inheritDoc}
     * @throws FileNotFoundException if the specified file cannot be found
     */
    @Override
    public BufferedInputStream getInputStream() throws FileNotFoundException {
        return new BufferedInputStream(new FileInputStream(this.getPath()));
    }
}
