/**
 *
 */
package aprove.verification.oldframework.Bytecode.Utils;

import java.io.*;
import java.net.*;
import java.util.*;
import java.util.stream.*;
import java.util.zip.*;

import aprove.api.osgi.*;
import aprove.verification.oldframework.Bytecode.Parser.*;

/**
 * This class delivers java class code streams from an OSGi Bundle (Eclipse Plug-in).
 */
public class OsgiBundleClassProvider extends ClassStreamProvider {

    /**
     * @param topParam Place in the OSGi Bundle file to start searching from
     */
    public static OsgiBundleClassProvider create(String topParam, Type t) {
        return new OsgiBundleClassProvider(AprovePlugin.getDefault().getClassResourcePrefix() + getTop(topParam), t);
    }

    private static String getTop(String topParam) {
        if (topParam.isEmpty() || topParam.endsWith("/")) {
            return topParam;
        } else {
            return topParam + '/';
        }
    }

    private static final String CLASS_FILE_EXTENSION = ".class";
    private static final int LENGTH_OF_CLASS_FILE_EXTENSION = CLASS_FILE_EXTENSION.length();

    /**
     * Place in the OSGi Bundle where the search for classes starts.
     */
    private final String top;

    public OsgiBundleClassProvider(String top, Type t) {
        super(t);
        this.top = top;
    }

    /**
     * @return information about the original program source, which should be
     *  stored in the bundle in META-INF/source
     */
    @Override
    public String readProgramInformation() {
        byte[] b = new byte[4096];
        URL metaInfEntry = AprovePlugin.getDefault().getResource("META-INF/source");
        if (metaInfEntry != null) {
            return readSourcesFromMetaInf(metaInfEntry, b);
        } else {
            URL sourceEntry = AprovePlugin.getDefault().getResource("source.zip");
            if (sourceEntry != null) {
                return readSourceZipFileFromBundle(sourceEntry, b);
            } else {
                return "No human-readable program information known.";
            }
        }
    }

    private String readSourcesFromMetaInf(URL metaInfEntry, byte[] b) {
        try (InputStream programInfoStream = metaInfEntry.openStream()) {
            StringBuilder result = new StringBuilder();
            readInputStreamToStringBuilder(programInfoStream, result, b);
            return result.toString();
        } catch (IOException e) {
            throw new RuntimeException("Couldn't read bundle resource", e);
        }
    }

    private String readSourceZipFileFromBundle(URL sourceEntry, byte[] b) {
        try {
            // create temporary file
            File tmpFile = File.createTempFile("aprove", "zipTmp");
            tmpFile.deleteOnExit();

            // extract source.zip file to temporary file
            try (InputStream zipFileStream = sourceEntry.openStream();
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
        URL entry = AprovePlugin.getDefault().getResource(this.top + name.toSlashed() + CLASS_FILE_EXTENSION);
        if (entry != null) {
            try {
                return entry.openStream();
            } catch (IOException e) {
                throw new RuntimeException("Couldn't read bundle resource", e);
            }
        } else {
            return null;
        }
    }

    @Override
    public Iterator<ClassName> iterator() {
        Iterator<URL> resources = AprovePlugin.getDefault().getResources(top, "*.class", true);
        return iteratorAsStream(resources).map(URL::getFile)
                                          .map(r -> r.substring(top.length()))
                                          .map(r -> r.substring(0, r.length() - LENGTH_OF_CLASS_FILE_EXTENSION))
                                          .map(ClassName::fromSlashed)
                                          .collect(Collectors.toList())
                                          .iterator();
    }

    public static <T> Stream<T> iteratorAsStream(Iterator<T> resources) {
        return StreamSupport.stream(Spliterators.spliteratorUnknownSize(resources, Spliterator.ORDERED), false);
    }
}
