package aprove.verification.oldframework.Bytecode.Utils;

import java.io.*;

import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Input.*;

/**
 * Classes implementing this interface are responsible for delivering
 * byte streams containing Java class code.
 * Furthermore, those classes have to be iterable, delivering all the
 * class names they know of.
 */
public abstract class ClassStreamProvider implements Iterable<ClassName> {

    public enum Type {
        UserDefined, Library
    }

    private Type t;

    public ClassStreamProvider(Type t) {
        this.t = t;
    }

    public Type getType() {
        return t;
    }

    /**
     * @param className Name of the class to provide
     * @return InputStream containing class bytecode, or null, if not found
     */
    public abstract InputStream getClassStream(ClassName className);

    /**
     * @return a string representing the program in a human readable form (if
     * that information is available).
     */
    public abstract String readProgramInformation();

    /**
     * @return a class stream provider to the data in <code>file</code>
     */
    public static ClassStreamProvider create(final File file, Type t) {
        if (file.isFile() && file.getName().toLowerCase().endsWith(".class")) {
            return DirectoryClassProvider.create(file.toPath(), t);
        } else if (file.isFile() && file.getName().toLowerCase().endsWith(".jar")) {
            return JarClassProvider.create(file, "", t);
        } else {
            throw new IllegalArgumentException("Unhandled JBC problem file type: " + file);
        }
    }

    /**
     * @param input defining where we get the program to analyze from
     * @return a class stream provider to the data in <code>file</code>
     */
    public static ClassStreamProvider create(final Input input, Type t) {
        if (input instanceof FileInput) {
            return create(((FileInput) input).getFile(), t);
        }
        final File file = dumpToFile(input);
        return create(file, t);
    }

    /**
     * @param input defining where we get the program to analyze from
     * @return a (temp) file containing the data
     */
    private static File dumpToFile(Input input) {
        try {
            File tmpFile = File.createTempFile("aprove", "." + input.getExtension());
            tmpFile.deleteOnExit();

            try (InputStream is = input.getInputStream();
                 OutputStream tmpOut = new FileOutputStream(tmpFile)) {
                readInputStreamToOutputStream(is, tmpOut, new byte[4096]);
            }

            return tmpFile;
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    protected static void readInputStreamToOutputStream(InputStream in, OutputStream out, byte[] b) throws IOException {
        for (int length = in.read(b); length != -1; length = in.read(b)) {
            out.write(b, 0, length);
        }
    }
}
