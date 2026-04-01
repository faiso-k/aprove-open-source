package aprove.verification.oldframework.Bytecode.Parser;

import aprove.*;

/**
 * Smart representation of fully qualified class names, splitting package and
 * class name and providing convenience methods to work on them.
 *
 * @author Christian von Essen
 */
public final class ClassName implements Comparable<ClassName> {
    /**
     * The types that are used from the VM.
     * @author cotto
     */
    public static enum Important {
        // Some important classes

        /**
         * java.lang.Object
         */
        JAVA_LANG_OBJECT("java.lang.Object"),

        /**
         * java.lang.String
         */
        JAVA_LANG_STRING("java.lang.String"),

        /**
         * java.lang.System
         */
        JAVA_LANG_SYSTEM("java.lang.System", false),

        /**
         * java.lang.Thread
         */
        JAVA_LANG_THREAD("java.lang.Thread", false),

        /**
         * java.lang.ThreadGroup
         */
        JAVA_LANG_THREADGROUP("java.lang.ThreadGroup", false),

        /**
         * java.lang.Class
         */
        JAVA_LANG_CLASS("java.lang.Class", false),

        /**
         * java.lang.ClassLoader
         */
        JAVA_LANG_CLASSLOADER("java.lang.ClassLoader", false),

        /**
         * java.lang.Integer
         */
        JAVA_LANG_INTEGER("java.lang.Integer", false),

        // Important interfaces

        /**
         * java.lang.Cloneable
         */
        JAVA_LANG_CLONEABLE("java.lang.Cloneable"),

        /**
         * java.io.Serializable
         */
        JAVA_IO_SERIALIZABLE("java.io.Serializable"),

        /**
         * java.lang.reflect.AnnotatedElement
         */
        JAVA_LANG_REFLECT_ANNOTATEDELEMENT("java.lang.reflect.AnnotatedElement", false),

        /**
         * java.lang.reflect.GenericDeclaration
         */
        JAVA_LANG_REFLECT_GENERICDECLARATION("java.lang.reflect.GenericDeclaration", false),

        /**
         * java.lang.CharSequence
         */
        JAVA_LANG_CHARSEQUENCE("java.lang.CharSequence", false),

        /**
         * java.lang.Comparable
         */
        JAVA_LANG_COMPARABLE("java.lang.Comparable", false),

        /**
         * java.lang.reflect.Type
         */
        JAVA_LANG_REFLECT_TYPE("java.lang.reflect.Type", false),

        // Some exceptions

        /**
         * java.lang.NullPointerException
         */
        NPE_EXC("java.lang.NullPointerException"),

        /**
         * "java.lang.ArithmeticException"
         */
        ARITH_EXC("java.lang.ArithmeticException"),

        /**
         * java.lang.ArrayStoreException
         */
        ARRAYSTORE_EXC("java.lang.ArrayStoreException"),

        /**
         * java.lang.ArrayIndexOutOfBoundsException
         */
        ARRAYINDEXOOB_EXC("java.lang.ArrayIndexOutOfBoundsException"),

        /**
         * java.lang.ClassCastException
         */
        CLASSCAST_EXC("java.lang.ClassCastException"),

        /**
         * java.lang.NegativeArraySizeException
         */
        NEGARRAYSIZE_EXC("java.lang.NegativeArraySizeException"),

        /**
         * java.lang.ClassNotFoundException
         */
        CLASSNOTFOUND_EXC("java.lang.ClassNotFoundException"),

        // Some errors

        /**
         * java.lang.NoClassDefFoundError
         */
        NOCLASSDEFFOUND_ERR("java.lang.NoClassDefFoundError"),

        /**
         * java.lang.IllegalAccessError
         */
        ILLEGALACCESS_ERR("java.lang.IllegalAccessError"),

        /**
         * java.lang.NoSuchFieldError
         */
        NOSUCHFIELD_ERR("java.lang.NoSuchFieldError"),

        /**
         * java.lang.IncompatibleClassChangeError
         */
        INCOMPATIBLECLASSCHANGE_ERR("java.lang.IncompatibleClassChangeError"),

        /**
         * java.lang.NoSuchMethodError
         */
        NOSUCHMETHOD_ERR("java.lang.NoSuchMethodError"),

        /**
         * java.lang.AbstractMethodError
         */
        ABSTRACTMETHOD_ERR("java.lang.AbstractMethodError");

        /**
         * The class name.
         */
        private final ClassName className;

        /**
         * If false, this class will be unknown in the competition.
         */
        private boolean knownInCompetition;

        /**
         * @param classNameParam the class name of the class (qualified,
         * dotted).
         */
        private Important(final String classNameParam) {
            this(classNameParam, true);
        }

        /**
         * @param classNameParam the class name of the class (qualified,
         * dotted).
         * @param knownInCompetitionParam if false, this class will be unknown
         * in the competition 2009.
         */
        private Important(final String classNameParam, final boolean knownInCompetitionParam) {
            this.className = ClassName.fromDotted(classNameParam);
            this.knownInCompetition = knownInCompetitionParam;
        }

        /**
         * @return this type as a string
         */
        @Override
        public String toString() {
            return this.className.toString();
        }

        /**
         * @return the class name
         */
        public ClassName getClassName() {
            return this.className;
        }

        /**
         * @return false iff this class is unknown in the competition
         */
        public boolean isKnownInCompetition() {
            return this.knownInCompetition;
        }
    }

    /**
     * Package portion of fully qualified class name. '/' is used as delimiter
     * i.e. java/lang
     */
    private String packageSpec;

    /**
     * Class portion of fully qualified class name.
     */
    private String classSpec;

    /**
     * String representation in dotted form.
     */
    private String dottedStringRepresentation = null;

    /**
     * String representation in slashed form.
     */
    private String slashedStringRepresentation = null;

    /**
     * Private constructor, allowing only from(Slash)Dotted/fromSlashed
     * to create new instances.
     */
    private ClassName() {
        super();
    }

    /**
     * @param s Dotted fully qualified class name, e.g. java.lang.Object
     * @return Parsed class name
     */
    public static ClassName fromDotted(final String s) {
        final ClassName c = new ClassName();
        final int pkgEnd = s.lastIndexOf('.');
        if (pkgEnd == -1) {
            c.packageSpec = "";
            c.classSpec = s;
        } else {
            c.packageSpec = s.substring(0, pkgEnd).replace(".", "/");
            c.classSpec = s.substring(pkgEnd + 1);
        }

        c.dottedStringRepresentation = s;
        c.slashedStringRepresentation = c.toString('/', '/');

        assert (c.packageSpec.isEmpty() || c.packageSpec.charAt(0) != '[') : "Support for ClassNames of array types broken";

        return c;
    }

    /**
     * @param s Partially dotted and slashed fully qualified class name,
     *  e.g. java/lang.Object
     * @return Parsed class name
     */
    public static ClassName fromSlashDotted(final String s) {
        final ClassName c = new ClassName();
        final int pkgEnd = s.lastIndexOf('.');
        if (pkgEnd == -1) {
            c.packageSpec = "";
            c.classSpec = s;
        } else {
            c.packageSpec = s.substring(0, pkgEnd);
            c.classSpec = s.substring(pkgEnd + 1);
        }

        c.dottedStringRepresentation = c.toString('.', '.');
        c.slashedStringRepresentation = c.toString('/', '/');

        assert (c.packageSpec.isEmpty() || c.packageSpec.charAt(0) != '[') : "Support for ClassNames of array types broken";

        return c;
    }

    /**
     * @param s Slashed fully qualified class name, e.g. java/lang/Object
     * @return Parsed class name
     */
    public static ClassName fromSlashed(final String s) {
        final ClassName c = new ClassName();
        final int pkgEnd = s.lastIndexOf('/');
        if (pkgEnd == -1) {
            c.packageSpec = "";
            c.classSpec = s;
        } else {
            c.packageSpec = s.substring(0, pkgEnd);
            c.classSpec = s.substring(pkgEnd + 1);
        }

        c.dottedStringRepresentation = c.toString('.', '.');
        c.slashedStringRepresentation = s;

        assert (c.packageSpec.isEmpty() || c.packageSpec.charAt(0) != '[') : "Support for ClassNames of array types broken";

        return c;
    }

    /**
     * @param pkgDelim delimiter symbol used to separate components of the
     *  package name
     * @param classDelim delimiter symbol used to separate the package part
     *  from the class name
     * @return string representation of this class name
     */
    private String toString(final char pkgDelim, final char classDelim) {
        if (this.packageSpec.equals("")) {
            return this.classSpec;
        }

        if (pkgDelim == '/') {
            return this.packageSpec + classDelim + this.classSpec;
        }
        return this.packageSpec.replace('/', pkgDelim) + classDelim + this.classSpec;
    }

    /**
     * @return string representation of this class name, e.g. java/lang/Object
     */
    public String toSlashed() {
        return this.slashedStringRepresentation;
    }

    /**
     * @return string representation of this class name (using dots as delimiter
     * of class and package names)
     */
    @Override
    public String toString() {
        if (Globals.DEBUG_COTTO && this.equals(ClassName.Important.JAVA_LANG_OBJECT.className)) {
            return "jlO";
        }
        return this.dottedStringRepresentation;
    }

    /**
     * @return the class name, without the fully-qualifying package part
     */
    public String getClassName() {
        return this.classSpec;
    }

    /**
     * @return the package name, with '/' as delimiter
     */
    public String getPkgName() {
        return this.packageSpec;
    }

    /**
     * @return the package as ClassName.
     */
    public ClassName getPkg() {
        return ClassName.fromSlashed(this.packageSpec);
    }

    /**
     * @param delim delimiter to separate the parts of the package name
     * @return the package name, with the given symbol as delimiter
     */
    public String getPkgName(final char delim) {
        return this.packageSpec.replace('/', delim);
    }

    /**
     * @param other some other object this is compared to.
     * @return true iff this object is equal to some other one.
     */
    @Override
    public boolean equals(final Object other) {
        if (!(other instanceof ClassName)) {
            return false;
        }
        return this.packageSpec.equals(((ClassName) other).packageSpec)
            && this.classSpec.equals(((ClassName) other).classSpec);
    }

    /**
     * @return hash code value for the object.
     */
    @Override
    public int hashCode() {
        return this.toString().hashCode();
    }

    /**
     * Compare according to the string representation:
     * <br/><br/>
     * {@inheritDoc}
     */
    @Override
    public int compareTo(final ClassName arg0) {
        return this.toString().compareTo(arg0.toString());
    }
}
