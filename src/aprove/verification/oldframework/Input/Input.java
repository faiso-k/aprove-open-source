package aprove.verification.oldframework.Input;

import java.io.*;

public interface Input {

    public String getPath();

    public String getName();

    public String getExtension();

    public Reader getContent();

    public String getString();

    public String getProtoAnnotation();

    public void setProtoAnnotation(String protoAnnotation);

    public boolean isAvailable();

    public abstract class InputSkeleton implements Input {

        protected String protoAnnotation;

        @Override
        public String getExtension() {
            final String[] parts = this.getName().split("\\.");
            if (parts.length < 2) {
                return "";
            } else {
                return parts[parts.length - 1];
            }
        }

        @Override
        public boolean isAvailable() {
            return true;
        }

        @Override
        public String getProtoAnnotation() {
            return this.protoAnnotation;
        }

        @Override
        public void setProtoAnnotation(final String protoAnnotation) {
            this.protoAnnotation = protoAnnotation;
        }
    }

    /**
     * @return a buffered input stream giving access to the content
     * @throws FileNotFoundException if the specified file cannot be found
     */
    public BufferedInputStream getInputStream() throws FileNotFoundException;
}
