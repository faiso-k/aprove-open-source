/**
 *
 */
package aprove.verification.oldframework.Bytecode.Utils;

import java.io.*;
import java.util.*;
import java.util.jar.*;
import java.util.stream.*;
import java.util.zip.*;

import aprove.verification.oldframework.Bytecode.Parser.*;

/**
 * This class delivers java class code streams from a jar file.
 */
public class JarClassProvider extends ClassStreamProvider {

    /**
     * @param path Path of the jar file
     * @param topParam Place in the jar file to start searching from
     */
    public static JarClassProvider create(File path, String topParam, Type t) {
        return new JarClassProvider(createJarFile(path), getTop(topParam), t);
    }

    private static String getTop(String topParam) {
        if (topParam.isEmpty() || topParam.endsWith("/")) {
            return topParam;
        } else {
            return topParam + '/';
        }
    }

    private static JarFile createJarFile(File path) {
        try {
            return new JarFile(path);
        } catch (IOException e) {
            throw new RuntimeException("Could not parse jar file: " + path, e);
        }
    }

    private static final String CLASS_FILE_EXTENSION = ".class";
    private static final int LENGTH_OF_CLASS_FILE_EXTENSION = CLASS_FILE_EXTENSION.length();

    private final JarFile file;
    /**
     * Place in the jar where the search for classes starts.
     */
    private final String top;

    public JarClassProvider(JarFile file, String top, Type t) {
        super(t);
        this.file = file;
        this.top = top;
    }

    /**
     * @return information about the original program source, which should be
     *  stored in the jar file in META-INF/source
     */
    @Override
    public String readProgramInformation() {
        byte[] b = new byte[4096];
        ZipEntry metaInfEntry = this.file.getEntry("META-INF/source");
        if (metaInfEntry != null) {
            return readSourcesFromMetaInf(metaInfEntry, b);
        } else {
            ZipEntry sourceZipEntry = this.file.getEntry("source.zip");
            if (sourceZipEntry != null) {
                return readSourceZipFileFromJarFile(sourceZipEntry, b);
            } else {
                return "No human-readable program information known.";
            }
        }
    }

    private String readSourcesFromMetaInf(ZipEntry entry, byte[] b) {
        try (InputStream programInfoStream = this.file.getInputStream(entry)) {
            StringBuilder result = new StringBuilder();
            readInputStreamToStringBuilder(programInfoStream, result, b);
            return result.toString();
        } catch (IOException e) {
            throw new RuntimeException("Couldn't read jar file", e);
        }
    }

    private String readSourceZipFileFromJarFile(ZipEntry entry, byte[] b) {
        try {
            // create temporary file
            File tmpFile = File.createTempFile("aprove", "zipTmp");
            tmpFile.deleteOnExit();

            // extract source.zip file to temporary file
            try (InputStream zipFileStream = this.file.getInputStream(entry);
                 OutputStream tmpOut = new FileOutputStream(tmpFile)) {
                readInputStreamToOutputStream(zipFileStream, tmpOut, b);
            }

            // read sources from temporary file
            try (ZipFile zipFile = new ZipFile(tmpFile)) {
                return readSourceText(zipFile, b);
            }
        } catch (IOException e) {
            return "No human-readable program information known.";
        }
    }

    private String readSourceText(ZipFile zipFile, byte[] b) throws IOException {
        Enumeration<? extends ZipEntry> zipEntries = zipFile.entries();
        StringBuilder result = new StringBuilder();
        while (zipEntries.hasMoreElements()) {
            ZipEntry zipEntry = zipEntries.nextElement();
            if (zipEntry.getName().endsWith(".java")) {
                try (InputStream sourceInputS = zipFile.getInputStream(zipEntry)) {
                    readInputStreamToStringBuilder(sourceInputS, result, b);
                }
                result.append("\n\n");
            }
        }
        return result.toString();
    }

    private void readInputStreamToStringBuilder(InputStream in, StringBuilder out, byte[] b) throws IOException {
        for (int length = in.read(b); length != -1; length = in.read(b)) {
            out.append(new String(b, 0, length));
        }
    }

    @Override
    public InputStream getClassStream(ClassName name) {
        ZipEntry entry = this.file.getEntry(this.top + name.toSlashed() + CLASS_FILE_EXTENSION);
        if (entry != null) {
            try {
                return this.file.getInputStream(entry);
            } catch (IOException e) {
                throw new RuntimeException("Couldn't read jar file", e);
            }
        } else {
            return null;
        }
    }

    @Override
    public Iterator<ClassName> iterator() {
        return enumerationAsStream(file.entries()).map(JarEntry::getName)
                                                  .filter(r -> r.startsWith(top))
                                                  .filter(r -> r.endsWith(CLASS_FILE_EXTENSION))
                                                  .map(r -> r.substring(top.length()))
                                                  .map(r -> r.substring(0, r.length() - LENGTH_OF_CLASS_FILE_EXTENSION))
                                                  .map(ClassName::fromSlashed)
                                                  .collect(Collectors.toList())
                                                  .iterator();
    }

    public static <T> Stream<T> enumerationAsStream(Enumeration<T> enumeration) {
        return StreamSupport.stream(Spliterators.spliteratorUnknownSize(enumerationAsIterator(enumeration),
                                                                        Spliterator.ORDERED),
                                    false);
    }

    private static <T> Iterator<T> enumerationAsIterator(Enumeration<T> enumeration) {
        return new Iterator<T>() {

            @Override
            public T next() {
                return enumeration.nextElement();
            }

            @Override
            public boolean hasNext() {
                return enumeration.hasMoreElements();
            }
        };
    }
}
