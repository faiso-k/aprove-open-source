package aprove.verification.oldframework.Bytecode.Utils;

import java.io.*;
import java.nio.file.*;
import java.util.*;
import java.util.logging.*;
import java.util.regex.*;
import java.util.stream.*;

import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.Exceptions.*;

/**
 * This class delivers Java class streams from a given directory that contains .class files.
 */
public class DirectoryClassProvider extends ClassStreamProvider {

    /**
     * @return a new class provider where the given .class file defines the
     *         directories to scan for other .class files.
     * @param classFile some .class file
     */
    public static DirectoryClassProvider create(Path classFile, Type t) {
        assert (Files.isRegularFile(classFile) && Files.isReadable(classFile));

        // Parse the file and get the package name as declared in that file
        try (InputStream fileInput = Files.newInputStream(classFile);
             InputStream in = new BufferedInputStream(fileInput)) {

            // Do not check the class name, we do not know what to expect
            ParsedClassFile parsedClassFile = new ParsedClassFile(null, in);

            String packageString = parsedClassFile.getClassName().getPkgName();
            Path classFileDirectory = classFile.toRealPath().getParent();
            assert (Files.isDirectory(classFileDirectory) && Files.isReadable(classFileDirectory));

            if (packageString.isEmpty()) {
                return new DirectoryClassProvider(classFileDirectory, t);
            } else {
                return new DirectoryClassProvider(getDirectoryOfDefaultPackage(classFileDirectory, packageString), t);
            }
        } catch (IOException e) {
            String message = "Problem reading '" + classFile + "'";
            DirectoryClassProvider.LOGGER.log(Level.SEVERE, message, e);
            throw new RuntimeException(message, e);
        } catch (ClassParseException e) {
            String message = "Problem parsing '" + classFile + "'";
            DirectoryClassProvider.LOGGER.log(Level.SEVERE, message, e);
            throw new RuntimeException(message, e);
        }
    }

    private static Path getDirectoryOfDefaultPackage(Path classFileDirectory, String packageString) {
        // for every component of the package name, walk back one directory in the directory structure
        Path result = classFileDirectory;
        Deque<String> packageComponents = new ArrayDeque<>(Arrays.asList(packageString.split(Pattern.quote("/"))));
        do {
            assert (packageComponents.getLast().equals(result.getFileName().toString()));
            packageComponents.removeLast();
            result = result.getParent();
        } while (!packageComponents.isEmpty());
        return result;
    }

    private static final String CLASS_FILE_EXTENSION = ".class";
    private static final int LENGTH_OF_CLASS_FILE_EXTENSION = CLASS_FILE_EXTENSION.length();

    private static final Logger LOGGER = Logger.getLogger("DirectoryClassProvider");

    private final Path absoluteBaseDirectory;

    public DirectoryClassProvider(Path baseDirectory, Type t) {
        super(t);
        assert (Files.isDirectory(baseDirectory) && Files.isReadable(baseDirectory));
        this.absoluteBaseDirectory = baseDirectory.toAbsolutePath();
    }

    /**
     * @param name Name of the class file to be provided
     * @return InputStream of data in the specified class file.
     */
    @Override
    public InputStream getClassStream(ClassName name) {
        Path path = absoluteBaseDirectory.resolve(name.toSlashed() + CLASS_FILE_EXTENSION);
        if (Files.exists(path)) {
            try {
                return Files.newInputStream(path);
            } catch (IOException e) {
                throw new RuntimeException("Could not open " + path, e);
            }
        } else {
            return null;
        }
    }

    @Override
    public Iterator<ClassName> iterator() {
        try (Stream<Path> files = Files.walk(absoluteBaseDirectory)) {
            return files.filter(r -> r.getFileName().toString().endsWith(CLASS_FILE_EXTENSION))
                        .map(absoluteBaseDirectory::relativize)
                        .map(r -> StreamSupport.stream(r.spliterator(), false)
                                               .map(Path::toString)
                                               .collect(Collectors.joining("/")))
                        .map(r -> r.substring(0, r.length() - LENGTH_OF_CLASS_FILE_EXTENSION))
                        .map(ClassName::fromSlashed)
                        .collect(Collectors.toList())
                        .iterator();
        } catch (IOException e) {
            String message = "unable to create iterator: " + absoluteBaseDirectory.toString();
            DirectoryClassProvider.LOGGER.log(Level.SEVERE, message, e);
            throw new RuntimeException(message, e);
        }
    }

    /**
     * @return information about the original program source, which should be
     *         stored in the jar file in META-INF/source
     */
    @Override
    public String readProgramInformation() {
        return "No human-readable program information known.";
    }
}
