package aprove.verification.oldframework.Bytecode.Parser;

import aprove.verification.oldframework.Bytecode.Parser.Attributes.*;
import aprove.verification.oldframework.Bytecode.Parser.ConstantPool.*;
import aprove.verification.oldframework.Bytecode.Utils.*;

/**
 * Representation of fields in Java Bytecode class files.
 *
 * @author Marc Brockschmidt
 */
public class Field implements HasAccessFlags {
    /** Bitmask of access flags of the field. */
    private final int accessFlags;

    /** Name of the field. */
    private final String name;

    /** Type descriptor of the field. */
    private final String descriptor;

    /** The constant value, if it was defined as ConstantValue attribute. */
    private final Object constantValue;

    /** List of attributes of the field. */
    private final Attribute[] attributes;

    /**
     * The name of the class declaring this field.
     */
    private final ClassName className;

    /**
     * Creates a new representation of a field in a Java Bytecode class file.
     * @param classFile parsed class file in which this field is defined
     * @param accessF bitmask of access flags of the field.
     * @param n Name of the field.
     * @param desc Type descriptor of the field.
     * @param attrs List of attributes of the field.
     */
    public Field(
        final ParsedClassFile classFile,
        final int accessF,
        final String n,
        final String desc,
        final Attribute[] attrs)
    {
        this.className = classFile.getClassName();
        this.accessFlags = accessF;
        this.name = n;
        this.descriptor = desc;
        this.attributes = attrs;
        if (this.isStatic()) {
            Attribute constantAttr = null;
            for (final Attribute attr : this.attributes) {
                if (attr.getAttributeName().equals("ConstantValue")) {
                    constantAttr = attr;
                    break;
                }
            }
            if (constantAttr == null) {
                this.constantValue = null;
            } else {
                //The only content of the attribute is a reference to the value:
                final int valueIndexRef =
                    (int) ParsedClassFile.getUSignedFromByteArray(constantAttr.getUnparsedData(), 0, 2);
                final CPEntry constantValueEntry = classFile.getConstant(valueIndexRef);
                if (constantValueEntry instanceof CPLong) {
                    this.constantValue = Long.valueOf(((CPLong) constantValueEntry).getLong());
                } else if (constantValueEntry instanceof CPFloat) {
                    this.constantValue = Float.valueOf(((CPFloat) constantValueEntry).getFloat());
                } else if (constantValueEntry instanceof CPDouble) {
                    this.constantValue = Double.valueOf(((CPDouble) constantValueEntry).getDouble());
                } else if (constantValueEntry instanceof CPInteger) {
                    this.constantValue = Integer.valueOf(((CPInteger) constantValueEntry).getInt());
                } else if (constantValueEntry instanceof CPStringRef) {
                    this.constantValue =
                        classFile.resolveStringRef(((CPStringRef) constantValueEntry).getStringRefIndex());
                } else {
                    assert (false) : "ConstantValue attribute points to non-fitting constant pool entry. Behaviour unspecified.";
                    this.constantValue = null;
                }
            }
        } else {
            this.constantValue = null;
        }
    }

    public Field(
            final ClassName cname,
            final int accessF,
            final String n,
            final String desc,
            final Attribute[] attrs,
            final Object constantValue)
    {
        this.className = cname;
        this.accessFlags = accessF;
        this.name = n;
        this.descriptor = desc;
        this.attributes = attrs;
        this.constantValue = constantValue;
        if (!this.isStatic()) {
            assert constantValue == null;
        }
    }

    /**
     * @return true iff this is a static field.
     */
    @Override
    public boolean isStatic() {
        return ((this.accessFlags & ClassFileParserConstants.FIELD_ACCESS_FLAG_STATIC) != 0);
    }

    /**
     * @return true iff this is field is declared as <code>public</code>
     */
    @Override
    public boolean isPublic() {
        return ((this.accessFlags & ClassFileParserConstants.FIELD_ACCESS_FLAG_PUBLIC) != 0);
    }

    /**
     * @return true iff this is field is declared as <code>protected</code>
     */
    @Override
    public boolean isProtected() {
        return ((this.accessFlags & ClassFileParserConstants.FIELD_ACCESS_FLAG_PROTECTED) != 0);
    }

    /**
     * @return true iff this is field is declared as <code>private</code>
     */
    @Override
    public boolean isPrivate() {
        return ((this.accessFlags & ClassFileParserConstants.FIELD_ACCESS_FLAG_PRIVATE) != 0);
    }

    /**
     * @return true iff this is field is declared as <code>final</code>
     */
    public boolean isFinal() {
        return ((this.accessFlags & ClassFileParserConstants.FIELD_ACCESS_FLAG_FINAL) != 0);
    }

    /**
     * @return object holding the constant value defined for this static field, null if there isn't one.
     */
    public Object getConstantValue() {
        return this.constantValue;
    }

    /**
     * @return Name of the field.
     */
    public String getName() {
        return this.name;
    }

    /**
     * @return Type descriptor of the field.
     */
    public String getDescriptor() {
        return this.descriptor;
    }

    /** @inheritDoc
     *  @return string representation of this object. */
    @Override
    public String toString() {
        return this.name + " (type " + this.descriptor + ")";
    }

    /**
     * @return the class name of the type declaring this field
     */
    @Override
    public ClassName getClassName() {
        return this.className;
    }
}
