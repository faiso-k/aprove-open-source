package aprove.input.Programs.jbc;

import java.io.*;
import java.net.*;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.*;
import java.util.logging.*;

import aprove.runtime.Options.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;
import aprove.verification.oldframework.Bytecode.Parser.Exceptions.*;
import aprove.verification.oldframework.Bytecode.Processors.BareJBCToJBCProcessor.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Bytecode.Utils.ClassStreamProvider.*;

/**
 * Handles all information we have about classes.
 */
public class ClassPath {

    private static final Logger logger = Logger.getLogger(ClassPath.class.getName());

    /**
     * The directory where the class files are stored. This must be in the same
     * directory as JBCProgram.class.
     */
    private static final String CLASSPATH_DIR = "classpath";

    /**
     * The class stream provider giving access to the very important class
     * files.
     */
    private static final ClassStreamProvider BASE_PROVIDER = createClassProvider(JBCProgram.class.getResource(""), Type.Library);

    /**
     * This is a stack of objects that provide access to the stored classes.
     * When loading a class, the providers are consulted in reversed order of
     * insertion (i.e., the newest provider is asked first) until the class is
     * found or we run out of providers.
     */
    private final LinkedList<ClassStreamProvider> classProviders;

    /**
     * Map from fully qualified class names to the respective parsed class.
     */
    private final Map<ClassName, IClass> parsedClasses;

    /**
     * Map from fully qualified class names to the respective node in the
     * tree of all known type class.
     */
    private final Map<ClassName, TypeTree> typeTrees;

    /**
     * Marks that we have initialized the class path (i.e. computed all
     * information we expect in our cache).
     */
    private final boolean initialized;

    /**
     * Create the class provider giving access to the class files needed from
     * the JVM.
     */
    private static ClassStreamProvider createClassProvider(URL baseUrl, Type t) {
        if ("jar".equals(baseUrl.getProtocol())) {
            return createJarClassProvider(decodeUrl(baseUrl), t);
        } else if ("bundleresource".equals(baseUrl.getProtocol())) {
            return createOsgiBundleClassProvider(decodeUrl(baseUrl), t);
        } else {
            return createDirectoryClassProvider(decodeUrl(baseUrl), t);
        }
    }

    private static String decodeUrl(URL defaultUrl) {
        try {
            return URLDecoder.decode(defaultUrl.getFile(), "UTF-8");
        } catch (UnsupportedEncodingException e) {
            String message = "UTF-8 encoding not found";
            logger.log(Level.SEVERE, message, e);
            throw new IllegalArgumentException(message, e);
        }
    }

    private static JarClassProvider createJarClassProvider(String file, Type t) {
        int limitIndex = file.indexOf('!');
        String jarFile = file.substring(5, limitIndex);
        String classPath = file.substring(limitIndex + 2) + ClassPath.CLASSPATH_DIR;
        return JarClassProvider.create(new File(jarFile), classPath, t);
    }

    /**
     * Here, it is safe to instantiate {@link OsgiBundleClassProvider}, because we know that Aprove is executed as an Eclipse Plug-in.
     */
    private static OsgiBundleClassProvider createOsgiBundleClassProvider(String file, Type t) {
        return OsgiBundleClassProvider.create(file + ClassPath.CLASSPATH_DIR, t);
    }

    private static DirectoryClassProvider createDirectoryClassProvider(String file, Type t) {
        return new DirectoryClassProvider(Paths.get(file, ClassPath.CLASSPATH_DIR), t);
    }

    /**
     * Constructs a new class object. Does not do any of the needed caching.
     * Uses the default classes provided with AProVE iff the given set of jar-files is empty.
     * @param jarFile a JAR with the VM classes we need.
     */
    public ClassPath(final Set<File> jarFiles, BareJBCOptions options) {
        this.classProviders = new LinkedList<>();
        if (jarFiles.isEmpty()) {
            this.classProviders.add(BASE_PROVIDER);
        } else {
            for (File jar: jarFiles) {
                this.addClassStreamProvider(jar, ClassStreamProvider.Type.Library);
            }
        }
        this.parsedClasses = new ConcurrentHashMap<>();
        this.typeTrees = new ConcurrentHashMap<>(30000);
        this.initialized = false;
    }

    public void addClassStreamProvider(ClassStreamProvider p) {
        this.classProviders.add(p);
    }

    /**
     * @param file some .jar/.class file
     */
    public void addClassStreamProvider(final File file, ClassStreamProvider.Type t) {
        if (this.initialized) {
            throw new UnsupportedOperationException("Class stream providers cannot be added after the classpath"
                                                    + "was initialized.");
        }
        this.addClassStreamProvider(ClassStreamProvider.create(file, t));
    }

    public void addClass(DynamicClass toAdd) {
        this.parsedClasses.put(toAdd.getClassName(), toAdd);
        this.typeTrees.put(toAdd.getClassName(), toAdd.getType());
    }

    /**
     * Initialize all caches, perform sanity checks. After calling this method,
     * no new class stream providers may be added.
     */
    public void initialize() {
        assert (!this.initialized) : "Trying to initialize ClassPath twice.";
        for (final ClassStreamProvider provider : this.classProviders) {
            this.readTypeTree(provider, true);
        }
        this.parseImportantClasses();

        IClass stringClass = this.getClass(Important.JAVA_LANG_STRING.getClassName());

        if (stringClass == null || stringClass.getLocalMethod("isEmpty", new ParsedMethodDescriptor("()Z")) == null) {
            die("The files you provided are not complete. Please use the default.");
        }
    }

    /**
     * Ensure that all classes that were marked as important are parsed.
     */
    private void parseImportantClasses() {
        for (final Important important : Important.values()) {
            if (JBCAnalysisOptions.Competition && !important.isKnownInCompetition()) {
                continue;
            }
            ClassName className = important.getClassName();
            if (!this.parsedClasses.containsKey(className)) {
                /*
                 * Parse the important class. Classes which are allowed at the competition have to be
                 * known since they are shipped with AProVE. The remaining classes are only known if
                 * the user provides them (by adding some version of rt.jar to the classpath), so we
                 * may fail for those.
                 */
                boolean mayFail = !JBCAnalysisOptions.Competition && !important.isKnownInCompetition();
                final TypeTree typeTree = this.getTypeTree(className, BASE_PROVIDER, true, mayFail);

                if (typeTree != null) {
                    /*
                     * What happens if the JVM accesses e.g. java.lang.String, but
                     * it is declared private?
                     */
                    if (!typeTree.isPublic()) {
                        die("The class " + className + " is not public!");
                    }
                }
            }
        }
    }

    /**
     * Return the raw class file of the class with the given name. If an error
     * occurs, we will stop analysis.
     * @param className the name of the class file
     * @param in the inputstream giving access to the content of the class file
     * @return the raw class file
     * @throws WrongPackageNameException if the file does not match the expected
     * package name
     */
    private static ParsedClassFile getClassFile(ClassName className, InputStream in) throws WrongPackageNameException {
        assert (in != null);
        ParsedClassFile classFile = null;
        try {
            BufferedInputStream bin = new BufferedInputStream(in);
            classFile = new ParsedClassFile(className, bin);
            bin.close();
        } catch (IOException e) {
            ClassPath.die("Error while reading class file " + className + ".class", e);
        } catch (WrongPackageNameException e) {
            // The package name does not match, but we may ignore the class file
            throw e;
        } catch (ClassParseException e) {
            ClassPath.die("Error while parsing class code from " + className + ".class", e);
        }
        return classFile;
    }

    /**
     * Creates the type trees for all classes defined by the given provider.
     * @param provider a provider giving access to the class files
     */
    private synchronized void readTypeTree(final ClassStreamProvider provider, boolean failOK) {
        for (final ClassName name : provider) {
            this.getTypeTree(name, provider, false, failOK);
        }
    }

    /**
     * Return the type tree for the given type and construct it if it is not
     * known, yet. For each type tree we also ensure that the trees for all
     * super types and super interfaces exist. This corresponds to JVMS 5.3.5
     * and does a lot of checks defined in the JVMS, if needed.
     * @param className the name of the type to add.
     * @param provider this provider gives access to the class files.
     * @param doParse iff not set, we also parse the given file.
     * @return the type tree for the given type name.
     */
    public synchronized TypeTree getTypeTree(
        final ClassName className,
        final ClassStreamProvider provider,
        final boolean doParse,
        boolean failOK)
    {
        TypeTree thisTree = this.typeTrees.get(className);
        // do we already know the type?
        if (thisTree == null) {
            // get the corresponding class file
            InputStream in = provider.getClassStream(className);
            if (in == null) {
                if (failOK) {
                    logger.info("Incomplete classpath: cannot find file for " + className);
                    return null;
                } else {
                    die("Cannot find file for " + className + "\nRun 'ant -f build-aprove.xml copyResources'?");
                }
            }
            ParsedClassFile classFile;
            try {
                classFile = ClassPath.getClassFile(className, in);
            } catch (WrongPackageNameException e1) {
                // better ignore this class then
                return null;
            }

            assert (classFile != null);
            ClassName superType = classFile.getSuperClassName();
            TypeTree superTree = null;
            if (superType != null) {
                // make sure we know the tree for the super type
                superTree = this.getTypeTree(superType, provider, doParse, failOK);

                if (superTree == null){
                    if (failOK) {
                        logger.info("Incomplete classpath: no TypeTree for " + superType);
                        return null;
                    } else {
                        die("no TypeTree for " + superType);
                    }
                }

                // IncompatibleClassChangeError
                if (superTree.isInterface()) {
                    ClassPath.die("The type "
                                  + superTree.getClassName()
                                  + " is used as a super class of "
                                  + className
                                  + ", but is an interface!");
                }

                // ClassCircularityError
                if (superType.equals(className) || superTree.containsSuperType(className)) {
                    die("The type " + className + " (indirectly) extends itself!");
                }
            }

            List<TypeTree> implementedInterfaceTrees = new LinkedList<>();
            for (ClassName implementedInterface : classFile.getImplementedInterfaces()) {
                // make sure we know the tree for the implemented interface
                final TypeTree implementedInterfaceTree = this.getTypeTree(implementedInterface, provider, doParse, failOK);

                if (implementedInterfaceTree == null) {
                    if (failOK) {
                        logger.info("Incomplete classpath: no TypeTree for " + implementedInterface);
                        return null;
                    } else {
                        die("no TypeTree for " + implementedInterface);
                    }
                }

                implementedInterfaceTrees.add(implementedInterfaceTree);

                // IncompatibleClassChangeError
                if (!implementedInterfaceTree.isInterface()) {
                    ClassPath.die("The type "
                                  + implementedInterfaceTree.getClassName()
                                  + " is implemented by "
                                  + className
                                  + ", but is no interface!");
                }

                // ClassCircularityError
                if (implementedInterface.equals(className)
                    || implementedInterfaceTree.containsImplementedInterface(className)) {
                    ClassPath.die("The type " + className + " (indirectly) implements itself!");
                }
            }

            thisTree = new TypeTree(className, superTree, implementedInterfaceTrees, classFile);
            this.typeTrees.put(className, thisTree);

            if (doParse) {
                final ParsedClass parsedClass = new ParsedClass(classFile, this, thisTree, provider.getType());
                this.parsedClasses.put(className, parsedClass);
            }
        }
        return thisTree;
    }

    /**
     * @param important Classname of the class to load
     * @return loaded class
     */
    public IClass getClass(Important important) {
        return this.getClass(important.getClassName(), false);
    }

    /**
     * @param className Classname of the class to load
     * @return loaded class
     */
    public IClass getClass(ClassName className) {
        return this.getClass(className, false);
    }

    /**
     * @param className Classname of the class to load
     * @param failOK if not set, this analysis will crash when asked for a class
     * that cannot be found
     * @return loaded class (if failOK: null if not found)
     */
    public synchronized IClass getClass(ClassName className, boolean failOK) {
        // Check if the class was already loaded
        IClass c = this.parsedClasses.get(className);
        if (c == null) {
            InputStream in = null;
            Iterator<ClassStreamProvider> it = this.classProviders.descendingIterator();
            ClassStreamProvider provider = null;
            while (it.hasNext()) {
                provider = it.next();
                in = provider.getClassStream(className);
                if (in != null) {
                    // force that the typeTree for the class is added
                    TypeTree typeTree = getTypeTree(className, provider, true, true);
                    if (typeTree == null) {
                        in = null;
                    } else {
                        break;
                    }
                }
            }
            if (in == null) {
                if (failOK) {
                    return null;
                }
                ClassPath.die("Could not find class code for class " + className);
            }
            ParsedClassFile classFile;
            try {
                classFile = new ParsedClassFile(className, in);
                c = new ParsedClass(classFile, this, this.typeTrees.get(className), provider.getType());
                this.parsedClasses.put(className, c);
                in.close();
            } catch (IOException e) {
                throw new RuntimeException("IO Error while parsing class code for " + className + ": " + e);
            } catch (ClassParseException e) {
                if (failOK) {
                    return null;
                }
                throw new RuntimeException("Error while parsing class code for " + className + ": " + e);
            }
        }
        return c;
    }

    /**
     * @param fuzzyType type of the class to load
     * @return type tree node corresponding to className
     */
    public TypeTree getTypeTree(FuzzyClassType fuzzyType) {
        return this.typeTrees.get(fuzzyType.getMinimalClass());
    }

    /**
     * @param className {@link ClassName} of the class to load
     * @return type tree node corresponding to className
     */
    public TypeTree getTypeTree(ClassName className) {
        return this.typeTrees.get(className);
    }

    /**
     * Log the given message and throw a RuntimeException.
     */
    private static void die(String message) {
        logger.log(Level.SEVERE, message);
        throw new RuntimeException(message);
    }

    /**
     * Log the given message and throw a RuntimeException.
     */
    private static void die(String message, Throwable t) {
        logger.log(Level.SEVERE, message, t);
        throw new RuntimeException(message, t);
    }

    /**
     * @return the set of known ClassNames.
     */
    public Set<ClassName> getClasses() {
        return this.typeTrees.keySet();
    }

    /**
     * @return true if all of the described type have only one ref field.
     */
    public boolean typeHasOnlyOneRefField(AbstractType abstractType, JBCOptions options) {
        for (FuzzyType fuzzyType : abstractType.getPossibleClassesCopy()) {
            if (fuzzyType instanceof FuzzyClassType && fuzzyType.getArrayDimension() == 0) {
                FuzzyClassType fuzzyClassType = (FuzzyClassType) fuzzyType;
                Set<FuzzyType> possibleTypes = new LinkedHashSet<>();
                fuzzyClassType.expand(possibleTypes, this, options);
                for (FuzzyType possibleType : possibleTypes) {
                    //The type was expanded to an array. We lost:
                    if (!(possibleType instanceof FuzzyClassType)) {
                        return false;
                    }
                    if (!this.typeHasOnlyOneRefField(((FuzzyClassType) possibleType).getMinimalClass())) {
                        return false;
                    }
                }
            } else {
                return false;
            }
        }
        return true;
    }

    public boolean typeHasOnlyPrimitiveFields(AbstractType abstractType, JBCOptions options) {
        for (FuzzyType fuzzyType : abstractType.getPossibleClassesCopy()) {
            if (fuzzyType instanceof FuzzyClassType && fuzzyType.getArrayDimension() == 0) {
                FuzzyClassType fuzzyClassType = (FuzzyClassType) fuzzyType;
                Set<FuzzyType> possibleTypes = new LinkedHashSet<>();
                fuzzyClassType.expand(possibleTypes, this, options);
                for (FuzzyType possibleType : possibleTypes) {
                    //The type was expanded to an array. We lost:
                    if (!(possibleType instanceof FuzzyClassType)) {
                        return false;
                    }
                    if (!this.typeHasOnlyPrimitiveFields(((FuzzyClassType) possibleType).getMinimalClass())) {
                        return false;
                    }
                }
            } else {
                return false;
            }
        }
        return true;
    }

    /**
     * @return true if this type (and all its possible subtypes) have only one ref field.
     */
    public boolean typeHasOnlyOneRefField(ClassName className) {
        return this.refFieldTypesOf(className).size() == 1;
    }

    public boolean typeHasOnlyPrimitiveFields(ClassName className) {
        return this.refFieldTypesOf(className).size() == 0;
    }

    /**
     * @return the list of fields with reference type
     */
    public List<FuzzyType> refFieldTypesOf(ClassName className) {
        List<FuzzyType> refFieldTypes = new LinkedList<>();
        TypeTree currentT = this.getTypeTree(className);
        while (currentT.isProperSubClassOf(ClassName.Important.JAVA_LANG_OBJECT.getClassName())) {
            IClass parsedClass = this.getClass(currentT.getClassName());
            for (Field field : parsedClass.getInstanceFields().values()) {
                FuzzyType fuzzyType = FuzzyType.parseTypeDescriptor(field.getDescriptor());
                if (!(fuzzyType instanceof FuzzyPrimitiveType) || fuzzyType.getArrayDimension() > 0) {
                    refFieldTypes.add(fuzzyType);
                }
            }
            currentT = currentT.getSuperType();
        }

        return refFieldTypes;
    }

    public boolean reachableTypesHaveOnlyOneRefField(ClassName className, JBCOptions options) {
        LinkedList<ClassName> todo = new LinkedList<>();
        todo.add(className);
        LinkedHashSet<ClassName> seen = new LinkedHashSet<>();
        while (!todo.isEmpty()) {
            ClassName current = todo.poll();
            //Seen that one already:
            if (!seen.add(current)) {
                continue;
            }

            Set<Field> fields = new LinkedHashSet<>();
            TypeTree currentT = this.getTypeTree(current);
            while (currentT.isProperSubClassOf(ClassName.Important.JAVA_LANG_OBJECT.getClassName())) {
                IClass pc = this.getClass(currentT.getClassName());
                fields.addAll(pc.getInstanceFields().values());
                currentT = currentT.getSuperType();
            }

            boolean seenOneRefType = false;
            for (Field field : fields) {
                FuzzyType fuzzyType = FuzzyType.parseTypeDescriptor(field.getDescriptor());
                if (fuzzyType instanceof FuzzyClassType) {
                    if (seenOneRefType) {
                        return false;
                    } else {
                        seenOneRefType = true;
                        Set<FuzzyType> possibleValueTypes = new LinkedHashSet<>();
                        fuzzyType.expand(possibleValueTypes, this, options);
                        for (FuzzyType ft : possibleValueTypes) {
                            if (ft.isArrayType()) {
                                return false;
                            } else if (ft instanceof FuzzyClassType) {
                                todo.add(((FuzzyClassType) ft).getMinimalClass());
                            }
                        }
                    }
                }
                if (fuzzyType.isArrayType()) {
                    return false;
                }
            }
        }

        return true;
    }

    public boolean isLibraryClass(ClassName cn) {
        return this.parsedClasses.get(cn).getClassStreamProviderType() == ClassStreamProvider.Type.Library;
    }
}
