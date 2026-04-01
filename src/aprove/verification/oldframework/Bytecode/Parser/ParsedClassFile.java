package aprove.verification.oldframework.Bytecode.Parser;

import java.io.*;
import java.util.*;

import aprove.*;
import aprove.verification.oldframework.Bytecode.Parser.Attributes.*;
import aprove.verification.oldframework.Bytecode.Parser.ConstantPool.*;
import aprove.verification.oldframework.Bytecode.Parser.Exceptions.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Representation of a (partly) parsed Java Bytecode class file.
 *
 * @author Marc Brockschmidt
 */
public class ParsedClassFile {
    /** The maximal class file version supported by JDK 1.5 */
    public static final Pair<Integer, Integer> JDK_1_5_VERSION = new Pair<>(49, 0);
    /** The maximal class file version supported by JDK 1.6 */
    public static final Pair<Integer, Integer> JDK_1_6_VERSION = new Pair<>(50, 0);
    /** The maximal class file version supported by JDK 1.7 */
    public static final Pair<Integer, Integer> JDK_1_7_VERSION = new Pair<>(51, 0);
    public static final Pair<Integer, Integer> JDK_1_8_VERSION = new Pair<>(52, 0);

    public static final Pair<Integer, Integer> CURRENT_VERSION = JDK_1_8_VERSION;

    /** Stream from which the class file is read. */
    private final DataInputStream classStream;

    /** The first 4 bytes of the read file. */
    private final int magicBytes;

    /** Major version of the read class file. */
    private final int majorVersion;

    /** Minor version of the read class file. */
    private final int minorVersion;

    /** Constant pool of the read class file. */
    private final CPEntry[] constantPool;

    /** Access flag of the read class or interface. */
    private final int accessFlags;

    /** Name of the class or interface defined in this Java Bytecode class
     *  file. */
    private final ClassName thisClassName;

    /** Name of the superclass of the class or interface defined in
     *  this Java Bytecode class file. */
    private final ClassName superClassName;

    /** List of names of implemented interfaces. */
    private final ClassName[] implementedInterfaceNames;

    /** List of class fields in this Java Bytecode class file. */
    private final List<Field> classFields;

    /** List of instance fields in this Java Bytecode class file. */
    private final List<Field> instanceFields;

    /** List of methods in this Java Bytecode class file. */
    private final RawMethod[] methods;

    /** List of attributes of this Java Bytecode class file. */
    private final Attribute[] attributes;

    private Optional<BootstrapMethodAttribute> bootstrapMethods = Optional.empty();

    /**
     * Creates a new (more or less parsed) instance of a Java Bytecode class
     * file.
     * @param expectedName the expected name of the contained type
     * @param input Some stream from which the class file data is read.
     * @throws IOException if reading from the stream failed.
     * @throws ClassParseException if we do not like the class file
     */
    public ParsedClassFile(final ClassName expectedName, final InputStream input)
        throws IOException,
            ClassParseException
    {
        this.classStream = new DataInputStream(input);
        this.magicBytes = this.classStream.readInt();

        //Check the magic:
        if (this.magicBytes != ClassFileParserConstants.CLASS_FILE_MAGIC_NUMBER) {
            throw new WrongMagicNumberException(this.magicBytes);
        }

        //Get the version number of this class file:
        this.minorVersion = this.classStream.readUnsignedShort();
        this.majorVersion = this.classStream.readUnsignedShort();

        if (this.majorVersion > ParsedClassFile.JDK_1_8_VERSION.x) {
            throw new JBCUnsupportedClassVersionError(this.majorVersion, this.minorVersion);
        }

        //Parse the constant pool, we need it for every non-trivial analysis:
        this.constantPool = new CPEntry[this.classStream.readUnsignedShort()];
        this.parseConstantPool();

        //Get the access flags:
        this.accessFlags = this.classStream.readUnsignedShort();

        //Get type information about this class:
        this.thisClassName = this.resolveClassNameRef(this.classStream.readUnsignedShort());
        this.superClassName = this.resolveClassNameRef(this.classStream.readUnsignedShort());

        if (expectedName != null) {
            if (!this.thisClassName.getPkgName().equals(expectedName.getPkgName())) {
                throw new WrongPackageNameException(this.thisClassName, expectedName.getPkgName());
            }
            if (!this.thisClassName.getClassName().equals(expectedName.getClassName())) {
                throw new JBCNoClassDefFoundError(expectedName, this.thisClassName.toString());
            }
        }

        //Parse the list of implemented interfaces:
        this.implementedInterfaceNames = new ClassName[this.classStream.readUnsignedShort()];
        this.parseImplementedInterfaces();

        //Parse the list of class and instance fields:
        this.classFields = new LinkedList<>();
        this.instanceFields = new LinkedList<>();
        this.parseFields(this.classStream.readUnsignedShort());

        //Parse the list of methods:
        this.methods = new RawMethod[this.classStream.readUnsignedShort()];
        this.parseMethods();

        //Now get the class attributes:
        this.attributes = this.parseAttributes(this.classStream.readUnsignedShort());

        assert (this.classStream.read() == -1) : "Found garbage at end of class file";
        this.classStream.close();
    }

    /**
     * @return the name of the class or interface defined in this Java
     *  Bytecode class file.
     */
    public ClassName getClassName() {
        return this.thisClassName;
    }

    /**
     * @return the name of the superclass of the class or interface defined
     *  in this Java Bytecode class file.
     */
    public ClassName getSuperClassName() {
        return this.superClassName;
    }

    /**
     * @return the list of names of implemented interfaces.
     */
    public ClassName[] getImplementedInterfaces() {
        return this.implementedInterfaceNames;
    }

    /**
     * @return List of class fields in this Java Bytecode class file.
     */
    public List<Field> getClassFields() {
        return this.classFields;
    }

    /**
     * @return List of instance fields in this Java Bytecode class file.
     */
    public List<Field> getInstanceFields() {
        return this.instanceFields;
    }

    /**
     * @return the list of methods in this Java Bytecode class file.
     */
    public RawMethod[] getMethods() {
        return this.methods;
    }

    /**
     * Parses a constant pool starting at the beginning of <code>classStream</code>.
     *
     * @throws IOException if reading from <code>classStream</code> failed.
     * @throws UnknownConstantPoolTagException if a constant pool entry with an
     *  unknown tag was found.
     */
    private void parseConstantPool() throws IOException, UnknownConstantPoolTagException {
        for (int cpIndex = 1; cpIndex < this.constantPool.length; cpIndex++) {
            boolean takesTwoIndexPositions = false;
            final int cpTag = this.classStream.readUnsignedByte();
            final CPEntry entry;
            switch (cpTag) {
            case ClassFileParserConstants.CONSTANT_POOL_UTF8_TAG:
                entry = new CPString(this.classStream.readUTF());
                break;
            case ClassFileParserConstants.CONSTANT_POOL_INTEGER_TAG:
                entry = new CPInteger(this.classStream.readInt());
                break;
            case ClassFileParserConstants.CONSTANT_POOL_FLOAT_TAG:
                entry = new CPFloat(this.classStream.readFloat());
                break;
            case ClassFileParserConstants.CONSTANT_POOL_LONG_TAG:
                entry = new CPLong(this.classStream.readLong());
                takesTwoIndexPositions = true;
                break;
            case ClassFileParserConstants.CONSTANT_POOL_DOUBLE_TAG:
                entry = new CPDouble(this.classStream.readDouble());
                takesTwoIndexPositions = true;
                break;
            case ClassFileParserConstants.CONSTANT_POOL_STRING_REF_TAG:
                entry = new CPStringRef(this.classStream.readShort());
                break;
            case ClassFileParserConstants.CONSTANT_POOL_CLASS_REF_TAG:
                entry = new CPClassRef(this.classStream.readShort());
                break;
            case ClassFileParserConstants.CONSTANT_POOL_FIELD_REF_TAG:
                entry = new CPFieldRef(this.classStream.readShort(), this.classStream.readShort());
                break;
            case ClassFileParserConstants.CONSTANT_POOL_METHOD_REF_TAG:
                entry = new CPMethodRef(this.classStream.readShort(), this.classStream.readShort());
                break;
            case ClassFileParserConstants.CONSTANT_POOL_INTERFACE_METHOD_REF_TAG:
                entry = new CPInterfaceMethodRef(this.classStream.readShort(), this.classStream.readShort());
                break;
            case ClassFileParserConstants.CONSTANT_POOL_NAME_AND_TYPE_REF_TAG:
                entry = new CPNameAndTypeRef(this.classStream.readShort(), this.classStream.readShort());
                break;
            case ClassFileParserConstants.CONSTANT_POOL_METHOD_HANDLE:
                entry = new CPMethodHandle(this.classStream.readByte(), this.classStream.readShort());
                break;
            case ClassFileParserConstants.CONSTANT_POOL_METHOD_TYPE:
                entry = new CPMethodType(this.classStream.readShort());
                break;
            case ClassFileParserConstants.CONSTANT_POOL_INVOKE_DYNAMIC:
                entry = new CPInvokeDynamic(this.classStream.readShort(), this.classStream.readShort());
                break;
            default:
                throw new UnknownConstantPoolTagException(cpIndex, cpTag);
            }
            this.constantPool[cpIndex] = entry;

            /*
             * "In retrospect, making 8-byte constants take two constant pool entries was a
             *  poor choice." -- JVMS
             */
            if (takesTwoIndexPositions) {
                cpIndex++;
            }
        }
    }

    /**
     * Parses the list of implemented interfaces starting at the beginning of
     * <code>classStream</code>.
     *
     * @throws IOException if reading from <code>classStream</code> failed.
     */
    private void parseImplementedInterfaces() throws IOException {
        for (int interfIndex = 0; interfIndex < this.implementedInterfaceNames.length; interfIndex++) {
            final int interfaceRef = this.classStream.readShort();
            this.implementedInterfaceNames[interfIndex] = this.resolveClassNameRef(interfaceRef);
        }
    }

    /**
     * Read a field list list from the beginning of <code>classStream</code>.
     * @param fieldNumber number of fields in this class file.
     * @throws IOException if reading from <code>classStream</code> failed.
     */
    private void parseFields(final int fieldNumber) throws IOException {
        for (int fieldIndex = 0; fieldIndex < fieldNumber; fieldIndex++) {
            final int fieldAccessFlags = this.classStream.readUnsignedShort();
            final String fieldName = this.resolveStringRef(this.classStream.readUnsignedShort());
            final String fieldDescriptor = this.resolveStringRef(this.classStream.readUnsignedShort());
            final Attribute[] fieldAttributes = this.parseAttributes(this.classStream.readUnsignedShort());
            final Field f = new Field(this, fieldAccessFlags, fieldName, fieldDescriptor, fieldAttributes);
            if (f.isStatic()) {
                this.classFields.add(f);
            } else {
                this.instanceFields.add(f);
            }
        }
    }

    /**
     * Read a method list list from the beginning of <code>classStream</code>.
     * @throws IOException if reading from <code>classStream</code> failed.
     */
    private void parseMethods() throws IOException {
        for (int methodIndex = 0; methodIndex < this.methods.length; methodIndex++) {
            final int methodAccessFlags = this.classStream.readUnsignedShort();
            final String methodName = this.resolveStringRef(this.classStream.readUnsignedShort());
            final String methodDescriptor = this.resolveStringRef(this.classStream.readUnsignedShort());
            final Attribute[] methodAttributes = this.parseAttributes(this.classStream.readUnsignedShort());
            this.methods[methodIndex] =
                new RawMethod(this, methodAccessFlags, methodName, methodDescriptor, methodAttributes);
        }
    }

    /**
     * Read an attribute list from the beginning of <code>classStream</code>.
     * @param attrCount Length of the list of attributes.
     * @return array of UnparsedAttribute objects
     * @throws IOException if reading from <code>classStream</code> failed.
     */
    private Attribute[] parseAttributes(final int attrCount) throws IOException {
        final Attribute[] res = new Attribute[attrCount];
        for (int attrIndex = 0; attrIndex < attrCount; attrIndex++) {
            final String attributeName = this.resolveStringRef(this.classStream.readUnsignedShort());

            final int attributeDataLength = this.classStream.readInt();
            final byte[] attributeData = new byte[attributeDataLength];
            if (attributeDataLength > 0) {
                int readBytes = 0;
                int lastReadBytes = 0;
                do {
                    lastReadBytes = this.classStream.read(attributeData, readBytes, attributeDataLength - readBytes);
                    readBytes += lastReadBytes;
                } while (lastReadBytes > 0 && readBytes < attributeDataLength);
                if (attributeDataLength != readBytes) {
                    throw new IOException("Couldn't read all attribute data");
                }
            }
            res[attrIndex] = new Attribute(attributeName, attributeData);
        }

        return res;
    }

    /**
     * Read an attribute list from <code>rawAttrs</code>
     * @param attrCount Length of the list of attributes.
     * @param rawAttrs Byte array containing the raw, unparsed attributes.
     * @param firstBytePos First position in <code>rawAttrs</code> that contains attribute data.
     * @return array of UnparsedAttribute objects
     */
    public Attribute[] parseAttributes(final int attrCount, final byte[] rawAttrs, final int firstBytePos) {
        int bytePos = firstBytePos;
        final Attribute[] res = new Attribute[attrCount];
        for (int attrIndex = 0; attrIndex < attrCount; attrIndex++) {
            final String attributeName = this.resolveStringRef((int) ParsedClassFile.getUSignedFromByteArray(rawAttrs, bytePos, 2));
            bytePos += 2;

            final int attributeDataLength = (int) ParsedClassFile.getUSignedFromByteArray(rawAttrs, bytePos, 4);
            bytePos += 4;
            final byte[] attributeData = new byte[attributeDataLength];
            if (attributeDataLength > 0) {
                System.arraycopy(rawAttrs, bytePos, attributeData, 0, attributeDataLength);
                bytePos += attributeDataLength;
            }
            res[attrIndex] = new Attribute(attributeName, attributeData);
        }

        return res;
    }

    /**
     * @param index index to the constant pool
     * @return the constant pool entry at the specified index.
     */
    public CPEntry getConstant(final int index) {
        return this.constantPool[index];
    }

    /**
     * Fetches the name of a class from the constant pool when given an index to
     * a CONSTANT_Class_info entry.
     * @param index Index of a constant class information constant pool entry.
     * @return ClassName object for the referenced class name
     */
    public ClassName resolveClassNameRef(final int index) {
        final FuzzyType fuzzyType = this.resolveClassNameRefFuzzy(index);
        if (fuzzyType == null) {
            return null;
        }
        assert (fuzzyType instanceof FuzzyClassType);
        assert (fuzzyType.getArrayDimension() == 0);
        return ((FuzzyClassType) fuzzyType).getMinimalClass();
    }

    /**
     * Fetches the name of a class from the constant pool when given an index to
     * a CONSTANT_Class_info entry.
     * @param index Index of a constant class information constant pool entry.
     * @return FuzzyType representing the referenced class name (type)
     */
    public FuzzyType resolveClassNameRefFuzzy(final int index) {
        assert (this.constantPool[index] instanceof CPClassRef || (index == 0)) : "Constant pool entry # "
            + index
            + " is not a class reference as expected";
        if (index != 0) {
            final CPClassRef classRef = (CPClassRef) this.constantPool[index];
            final String string = this.resolveStringRef(classRef.getClassRefIndex());
            return FuzzyType.parseType(string);
        }
        return null;
    }

    /**
     * Fetches a string from the constant pool when given an index to a
     * CONSTANT_Utf8_info entry.
     * @param index Index of a constant string information constant pool entry.
     * @return the actual string
     */
    public String resolveStringRef(final int index) {
        assert (this.constantPool[index] instanceof CPString) : "Constant pool entry #"
            + index
            + " is not a string as expected";
        final CPString string = (CPString) this.constantPool[index];
        return string.getString();
    }

    /**
     * Retrieve an unsigned number from an array of bytes.
     * @param bytes the byte array to fetch data from
     * @param pos the position of the requested data in the byte array
     * @param num the number of bytes to be considered
     * @return the retrieved number
     */
    public static long getUSignedFromByteArray(final byte[] bytes, final int pos, final int num) {
        long r = 0;
        for (int i = 0; i < num; i++) {
            r = (r << 8) | (bytes[pos + i] & 0xFF);
        }

        return r;
    }

    /**
     * @param name Some field name.
     * @return The field object corresponding to field <code>name</code>
     *  of this class.
     */
    public Field getField(final String name) {
        for (final Field f : this.instanceFields) {
            if (f.getName().equals(name)) {
                return f;
            }
        }
        for (final Field f : this.classFields) {
            if (f.getName().equals(name)) {
                return f;
            }
        }
        return null;
    }

    /**
     * @return true iff this class is declared as <code>public</code>
     */
    public boolean isPublic() {
        return ((this.accessFlags & ClassFileParserConstants.CLASS_ACCESS_FLAG_PUBLIC) != 0);
    }

    /**
     * @return true iff this is an interface.
     */
    public boolean isInterface() {
        final boolean res = (this.accessFlags & ClassFileParserConstants.CLASS_ACCESS_FLAG_INTERFACE) != 0;
        if (res) {
            // Hack... package-info.java is not compiled correctly with OpenJDK 7. Hence, we need this workaround. See also TypeTree.java.
            assert (this.isAbstract() || this.getClassName().toString().endsWith("package-info"));
            assert (!this.isFinal());
            assert (!this.hasSuperFlag());
            assert ((this.accessFlags & ClassFileParserConstants.CLASS_ACCESS_FLAG_ENUM) == 0);
        }
        return res;
    }

    /**
     * @return true iff this is an abstract class.
     */
    public boolean isAbstract() {
        return ((this.accessFlags & ClassFileParserConstants.CLASS_ACCESS_FLAG_ABSTRACT) != 0);
    }

    /**
     * @return true iff this is a final class.
     */
    public boolean isFinal() {
        return ((this.accessFlags & ClassFileParserConstants.CLASS_ACCESS_FLAG_FINAL) != 0);
    }

    /**
     * @return true iff this class is marked with the super flag.
     */
    public boolean hasSuperFlag() {
        return ((this.accessFlags & ClassFileParserConstants.CLASS_ACCESS_FLAG_SUPER) != 0);
    }

    /**
     * @param name Some method name.
     * @return true iff this class contains a method of this name.
     */
    public boolean hasMethod(final String name) {
        for (final RawMethod m : this.methods) {
            if (m.getName().equals(name)) {
                return true;
            }
        }
        return false;
    }

    /**
     * @return the class file version, as pair (majorVersion, minorVersion).
     */
    public Pair<Integer, Integer> getClassFileVersion() {
        return new Pair<>(this.majorVersion, this.minorVersion);
    }

    public List<BootstrapMethod> getBootstrapMethods() {
        try {
            if (bootstrapMethods.isPresent()) {
                return bootstrapMethods.get().getBootstrapMethods();
            } else {
                List<BootstrapMethod> bootstrapMethods = new ArrayList<>();
                for (Attribute a: attributes) {
                    if (a.getAttributeName().equals("BootstrapMethods")) {
                        DataInputStream stream = new DataInputStream(new ByteArrayInputStream(a.getUnparsedData()));
                        int numBootstrapMethods = stream.readShort();
                        for (int i = 0; i < numBootstrapMethods; i++) {
                            short bootstrapMethodRef = stream.readShort();
                            short numBootstrapArguments = stream.readShort();
                            List<Short> bootstrapArguments = new ArrayList<>(numBootstrapArguments);
                            for (int j = 0; j < numBootstrapArguments; j++) {
                                bootstrapArguments.add(j, stream.readShort());
                            }
                            bootstrapMethods.add(i, new BootstrapMethod(bootstrapMethodRef, bootstrapArguments));
                        }
                        break;
                    }
                }
                this.bootstrapMethods = Optional.of(new BootstrapMethodAttribute(bootstrapMethods));
                return bootstrapMethods;
            }
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}
