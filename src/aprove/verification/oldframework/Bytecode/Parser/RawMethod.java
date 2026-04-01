package aprove.verification.oldframework.Bytecode.Parser;

import aprove.verification.oldframework.Bytecode.Parser.Attributes.*;

/**
 * Representation of methods in Java Bytecode class files.
 *
 * @author Marc Brockschmidt
 */
public class RawMethod {
    /** Parsed class file in which this method is defined. */
    private final ParsedClassFile classFile;

    /** Bitmask of access flags of the method. */
    private final int accessFlags;

    /** Name of the method. */
    private final String name;

    /** Type descriptor of the method. */
    private final String descriptor;

    /** List of attributes of the method. */
    private final Attribute[] attributes;

    /** The unparsed code attribute, if there is one. */
    private Attribute rawCodeAttribute;

    /** The parsed code attribute, if there is one. */
    private CodeAttribute codeAttribute;

    /** The unparsed exceptions attribute, if there is one. */
    private Attribute rawExceptionsAttribute;

    /**
     * Creates a new representation of a method in a Java Bytecode class file.
     * @param classF parsed class file in which this method is defined.
     * @param accessF bitmask of access flags of the method.
     * @param n Name of the method.
     * @param desc Type descriptor of the method.
     * @param attrs List of attributes of the method.
     */
    public RawMethod(
        final ParsedClassFile classF,
        final int accessF,
        final String n,
        final String desc,
        final Attribute[] attrs)
    {
        this.classFile = classF;
        this.accessFlags = accessF;
        this.name = n;
        this.descriptor = desc;
        this.attributes = attrs;
        for (final Attribute attr : this.attributes) {
            final String attrName = attr.getAttributeName();
            if (attrName.equals("Code")) {
                this.rawCodeAttribute = attr;
            } else if (attrName.equals("Exceptions")) {
                this.rawExceptionsAttribute = attr;
            }
        }
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IMethod#toString()
     */
    @Override
    public String toString() {
        return this.name + " (type " + this.descriptor + ")";
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IMethod#getCodeAttr()
     */
    public CodeAttribute getCodeAttr() {
        if (this.codeAttribute == null && this.rawCodeAttribute != null) {
            this.codeAttribute = new CodeAttribute(this.classFile, this.rawCodeAttribute.getUnparsedData());
        }
        return this.codeAttribute;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IMethod#isStatic()
     */
    public boolean isStatic() {
        return ((this.accessFlags & ClassFileParserConstants.METHOD_ACCESS_FLAG_STATIC) != 0);
    }

    /**
     * @param flags the access flags
     * @return true iff this method is declared as <code>public</code>.
     */
    public static boolean isPublic(final int flags) {
        return ((flags & ClassFileParserConstants.METHOD_ACCESS_FLAG_PUBLIC) != 0);
    }

    /**
     * @param flags the access flags
     * @return true iff this method is declared as <code>protected</code>.
     */
    public static boolean isProtected(final int flags) {
        return ((flags & ClassFileParserConstants.METHOD_ACCESS_FLAG_PROTECTED) != 0);
    }

    /**
     * @param flags the access flags
     * @return true iff this method does not have a visibility flag.
     */
    public static boolean isDefaultAccess(final int flags) {
        return !RawMethod.isPrivate(flags) && !RawMethod.isPublic(flags) && !RawMethod.isProtected(flags);
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IMethod#isDefaultAccess()
     */
    public boolean isDefaultAccess() {
        return RawMethod.isDefaultAccess(this.accessFlags);
    }

    /**
     * @param flags the access flags
     * @return true iff this method is declared as <code>private</code>.
     */
    public static boolean isPrivate(final int flags) {
        return ((flags & ClassFileParserConstants.METHOD_ACCESS_FLAG_PRIVATE) != 0);
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IMethod#isPrivate()
     */
    public boolean isPrivate() {
        return RawMethod.isPrivate(this.accessFlags);
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IMethod#isPublic()
     */
    public boolean isPublic() {
        return RawMethod.isPublic(this.accessFlags);
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IMethod#isProtected()
     */
    public boolean isProtected() {
        return RawMethod.isProtected(this.accessFlags);
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IMethod#isStrictFP()
     */
    public boolean isStrictFP() {
        return ((this.accessFlags & ClassFileParserConstants.METHOD_ACCESS_FLAG_STRICT) != 0);
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IMethod#isSynchronized()
     */
    public boolean isSynchronized() {
        return ((this.accessFlags & ClassFileParserConstants.METHOD_ACCESS_FLAG_SYNCHRONIZED) != 0);
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IMethod#isNative()
     */
    public boolean isNative() {
        return ((this.accessFlags & ClassFileParserConstants.METHOD_ACCESS_FLAG_NATIVE) != 0);
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IMethod#isAbstract()
     */
    public boolean isAbstract() {
        return ((this.accessFlags & ClassFileParserConstants.METHOD_ACCESS_FLAG_ABSTRACT) != 0);
    }

    /**
     * @param flags the access flags
     * @return true iff this method is declared as <code>abstract</code>.
     */
    public static boolean isAbstract(final int flags) {
        return ((flags & ClassFileParserConstants.METHOD_ACCESS_FLAG_ABSTRACT) != 0);
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IMethod#isFinal()
     */
    public boolean isFinal() {
        return ((this.accessFlags & ClassFileParserConstants.METHOD_ACCESS_FLAG_FINAL) != 0);
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IMethod#getName()
     */
    public String getName() {
        return this.name;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IMethod#getDescriptor()
     */
    public String getDescriptor() {
        return this.descriptor;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IMethod#getAccessFlags()
     */
    public int getAccessFlags() {
        return this.accessFlags;
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Bytecode.Parser.IMethod#isVarArgs()
     */
    public boolean isVarArgs() {
        return ((this.accessFlags & ClassFileParserConstants.METHOD_ACCESS_FLAG_VARAGS) != 0);
    }
}
