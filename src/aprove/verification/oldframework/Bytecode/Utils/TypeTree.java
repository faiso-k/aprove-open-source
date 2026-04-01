package aprove.verification.oldframework.Bytecode.Utils;

import static aprove.verification.oldframework.Bytecode.Parser.ClassName.Important.*;

import java.util.*;

import aprove.Globals;
import aprove.runtime.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Parser.ClassName.*;

/**
 * Simple tree structure used to represent the known class hierarchy. The
 * elements of the constructed type tree are all classes and interfaces
 * mentioned in the program. Arrays and primitives are not part of this
 * hierarchy! Furthermore, the implicit connection between interfaces and
 * java.lang.Object is not represented.
 * @author Marc Brockschmidt
 */
public final class TypeTree implements Cloneable {
    /**
     * A list of objects of direct subclasses.
     */
    private final List<TypeTree> subTypes;

    /**
     * A list of objects of types that implement this interface.
     */
    private final List<TypeTree> implementingTypes;

    /**
     * A reference to the direct superclass.
     */
    private final TypeTree superType;

    /**
     * A reference to the implemented interfaces.
     */
    private final Collection<TypeTree> implementedInterfaces;

    /**
     * (Fully qualified) name of this class.
     */
    private final ClassName className;

    /**
     * Indicates whether this type is an interface.
     */
    private final boolean isInterface;

    /**
     * Indicates whether this type is an abstract class.
     */
    private final boolean isAbstract;

    /**
     * Cache for the type expansion (that, is all successors in the type tree)
     */
    private Set<TypeTree> typeExpansion;

    /**
     * For all known methods that are declared in this class/interface we store
     * the access flags as an Integer. The index is the concatenation of name
     * and descriptor (e.g. <code>&lt;init&gt;()V</code>).
     */
    private Map<String, Integer> methods;

    /**
     * True iff this is a public type.
     */
    private final boolean isPublic;

    /**
     * ACC_SUPER.
     */
    private final boolean superFlag;

    /**
     * Creates a new, uniquely identified Type.
     * @param id Name of the this class.
     * @param parent Reference to the direct superclass.
     * @param implInterfaces References to the implemented interfaces
     * @param classFile the class file giving further information
     */
    public TypeTree(final ClassName id, final TypeTree parent,
            final List<TypeTree> implInterfaces,
            final ParsedClassFile classFile) {
        this(id,
                parent,
                implInterfaces,
                classFile.isInterface(),
                classFile.isAbstract(),
                classFile.isPublic(),
                classFile.hasSuperFlag(),
                null);
        this.methods =
                new LinkedHashMap<String, Integer>(classFile.getMethods().length);
        for (final RawMethod method : classFile.getMethods()) {
            final ParsedMethodDescriptor descriptor =
                    new ParsedMethodDescriptor(method.getDescriptor());
            final MethodIdentifier identifier =
                    new MethodIdentifier(this.className, method.getName(),
                            descriptor);
            this.methods.put(identifier.getMethodName()
                    + identifier.getDescriptor(), method.getAccessFlags());
        }
    }

    public TypeTree(final ClassName id, final TypeTree parent,
            final List<TypeTree> implInterfaces,
            boolean isInterface,
            boolean isAbstract,
            boolean isPublic,
            boolean hasSuperFlag,
            Map<String, Integer> methods) {
        assert (id != null) : "Need name for each type";
        assert (parent != null || id.equals(JAVA_LANG_OBJECT.getClassName()));
        this.className = id;
        this.superType = parent;
        this.subTypes = new LinkedList<TypeTree>();
        this.implementingTypes = new LinkedList<TypeTree>();
        this.implementedInterfaces = new LinkedList<TypeTree>(implInterfaces);
        this.isInterface = isInterface;
        this.isAbstract = isAbstract;
        // Hack... package-info.java is not compiled correctly with OpenJDK 7. Hence, we need this workaround. See also ParsedClassFile.java.
        assert (!this.isInterface || this.className.toString().endsWith("package-info") || this.isAbstract);
        this.isPublic = isPublic;
        this.superFlag = hasSuperFlag;
        this.methods = methods;

        if (parent != null) {
            assert (parent.isAccessibleFrom(this));
            parent.subTypes.add(this);
        }
        for (final TypeTree typeTree : implInterfaces) {
            assert (typeTree.isAccessibleFrom(this));
            typeTree.implementingTypes.add(this);
        }
    }

    /**
     * @param other some type
     * @return true iff this type is accessible from the other type according to
     * JVMS 5.4.4.
     */
    public boolean isAccessibleFrom(final TypeTree other) {
        if (this.isPublic) {
            return true;
        }
        return this.className.getPkgName().equals(
            other.getClassName().getPkgName());
    }

    /**
     * Returns a deep (!) copy of this {@link TypeTree} object
     * @return Deep copy of this object
     */
    @Override
    public TypeTree clone() {
        try {
            return (TypeTree) super.clone();
        } catch (final CloneNotSupportedException e) {
            // This should never, ever happen
            throw new AssertionError();
        }
    }

    /**
     * @param superName fully qualified name of a class
     * @return list of types on the path down from a subclass of superName to
     * the current type.
     */
    public List<TypeTree> findPathFrom(final ClassName superName) {
        final List<TypeTree> res = new LinkedList<TypeTree>();
        if (!this.getClassName().equals(superName)) {
            this.findPathFrom(superName, res);
        }
        return res;
    }

    /**
     * @param superName fully qualified name of a class
     * @param res list of types on the path down from a subclass of superName to
     * the current type.
     */
    private void findPathFrom(final ClassName superName, final List<TypeTree> res) {
        if (this.superType != null) {
            if (this.superType.className.equals(superName)) {
                res.add(this);
            } else {
                this.superType.findPathFrom(superName, res);
                if (res.size() > 0) {
                    res.add(this);
                }
            }
        } else {
            res.clear();
        }
    }

    /**
     * @return fully qualified name of this class.
     */
    public ClassName getClassName() {
        return this.className;
    }

    /**
     * @param that some other node in the type tree
     * @return the maximal common supertype of this and that
     */
    public TypeTree getMaxCommonSupertype(final TypeTree that) {
        //Climb the type-tree until that is a subclass of curType. Terminates
        //at java.lang.Object
        TypeTree curType = this;
        while (!that.isSubClassOf(curType)) {
            curType = curType.getSuperType();
        }

        return curType;
    }

    /**
     * @param classes a collection of known classes
     * @return the class name without package identifier, if the class name
     * suffices to identify this class.
     */
    public String getShortClassName(final Collection<ClassName> classes) {
        for (final ClassName cn : classes) {
            if (cn.getClassName().equals(this.className.getClassName())
                && !cn.equals(this.className)) {
                return this.className.toString();
            }
        }
        return this.className.getClassName();
    }

    /**
     * Do not modify!
     * @return the subTypes
     */
    public List<TypeTree> getSubTypes() {
        return this.subTypes;
    }

    /**
     * @return the implementing types
     */
    public Collection<TypeTree> getImplementingTypes() {
        return this.implementingTypes;
    }

    /**
     * Do not modify!
     * @return the interfaces implemented/extended by this class/interface
     */
    public Collection<TypeTree> getImplementedInterfaces() {
        return this.implementedInterfaces;
    }

    /**
     * @return the superType
     */
    public TypeTree getSuperType() {
        return this.superType;
    }

    /**
     * @return the set of all supertypes of this type (without interfaces)
     */
    public Collection<TypeTree> getAllSuperClasses() {
        final Collection<TypeTree> res = new LinkedHashSet<TypeTree>();
        TypeTree curType = this;
        while (curType != null) {
            res.add(curType);
            curType = curType.getSuperType();
        }
        return res;
    }

    /**
     * @return the set of all supertypes of this type, including all implemented
     * interfaces.
     * @param strict if set, this type itself will not be returned
     */
    public Collection<TypeTree> getAllSuperTypes(final boolean strict) {
        final Collection<TypeTree> res = new LinkedHashSet<TypeTree>();
        final LinkedList<TypeTree> todo = new LinkedList<>();
        todo.add(this);
        TypeTree curType;
        while (!todo.isEmpty()) {
            curType = todo.pop();
            res.add(curType);
            todo.add(this.superType);
            todo.addAll(this.implementedInterfaces);
        }
        if (strict) {
            res.remove(this);
        }
        return res;
    }

    /**
     * @return true iff this type is an abstract class
     */
    public boolean isAbstract() {
        return this.isAbstract;
    }

    /**
     * @return true iff this type is an interface
     */
    public boolean isInterface() {
        return this.isInterface;
    }

    /**
     * @param superName fully qualified name of a class
     * @return true iff the current type class is a true (but possibly indirect)
     *  subclass of superName
     */
    public boolean isProperSubClassOf(final ClassName superName) {
        if (this.superType != null) {
            if (this.superType.className.equals(superName)) {
                return true;
            }
            return this.superType.isProperSubClassOf(superName);
        }
        return false;
    }

    /**
     * @param superName fully qualified name of a class
     * @return true iff the current type class is either superName or a
     * (possibly indirect) subclass of superName
     */
    public boolean isSubClassOf(final ClassName superName) {
        return (this.className.equals(superName) || this.isProperSubClassOf(superName));
    }

    /**
     * @param superClass type tree node of a class
     * @return true iff the current type class is either superName or a
     *  (possibly indirect) subclass of superName
     */
    public boolean isSubClassOf(final TypeTree superClass) {
        if (superClass.isInterface) {
            return false;
        }
        return this.isSubClassOf(superClass.getClassName());
    }

    /**
     * @return String representation of this {@link TypeTree}.
     */
    @Override
    public String toString() {
        final StringBuilder t = new StringBuilder();
        t.append(this.getClassName());
        boolean hadSubTypes = false;
        for (final TypeTree tmp : this.subTypes) {
            if (!hadSubTypes) {
                t.append("(");
                hadSubTypes = true;
            } else {
                t.append(",");
            }
            t.append(tmp.toString());
        }
        if (hadSubTypes) {
            t.append(")");
        }
        return t.toString();
    }

    /**
     * @return true iff this type has a supertype.
     */
    public boolean hasSuperType() {
        return this.superType != null;
    }

    /**
     * @return true iff a subtype is known
     */
    public boolean hasSubTypes() {
        return !this.subTypes.isEmpty();
    }

    /**
     * @param interfaceName the name of an interface
     * @return true iff this type implements the given interface (maybe not
     * directly)
     */
    public boolean implementsInterface(final ClassName interfaceName) {
        if (this.isInterface && this.className.equals(interfaceName)) {
            return true;
        }
        for (final TypeTree implementedInterfaceName : this.implementedInterfaces) {
            if (implementedInterfaceName.implementsInterface(interfaceName)) {
                return true;
            }
        }
        //Also allow the parent class to implement the interface:
        if (this.superType != null) {
            return this.superType.implementsInterface(interfaceName);
        }
        return false;
    }

    /**
     * @param interfaceType the interface
     * @return true iff this type implements the given interface (maybe not
     * directly)
     */
    public boolean implementsInterface(final TypeTree interfaceType) {
        if (!interfaceType.isInterface) {
            return false;
        }
        return this.implementsInterface(interfaceType.getClassName());
    }

    /**
     * @return true if this type is a class and not an interface.
     */
    public boolean isClass() {
        return !this.isInterface;
    }

    /**
     * @param other some other node in the type tree
     * @return true iff this type is an instance of other
     */
    public boolean instanceOf(final TypeTree other) {
        return (this.isSubClassOf(other) || this.implementsInterface(other) || (this.isInterface && other.className.equals(JAVA_LANG_OBJECT.getClassName())));
    }

    /**
     * This does not include implicit connections: Object/Serializable/Cloneable
     * to arrays
     * @return the type expansion, that is, all successors in the type tree
     */
    public synchronized Set<TypeTree> expand(JBCOptions options) {
        if (Globals.useAssertions) {
            assert(!options.dontExpandTypeTree() || !this.className.equals(Important.JAVA_LANG_OBJECT.getClassName()) || !this.isAbstract)
                : "expanding jlO even though dontExpandTypeTree flag is set";
        }
        if (this.typeExpansion == null) {
            final Set<TypeTree> result = new LinkedHashSet<TypeTree>();
            this.expand(result);
            this.typeExpansion = result;
        }
        return this.typeExpansion;
    }

    /**
     * This does not include implicit connections: Object/Serializable/Cloneable
     * to arrays
     * @param result add the type expansion here, that is, all successors in the
     * type tree
     */
    private void expand(final Set<TypeTree> result) {
        result.add(this);
        for (final TypeTree t : this.subTypes) {
            t.expand(result);
        }
        for (final TypeTree t : this.implementingTypes) {
            t.expand(result);
        }
    }

    /**
     * @param methodIdentifier a method identifier.
     * @return the first type that defines a method with the same name and
     * descriptor as given in the identifier when walking towards
     * java.lang.Object.
     */
    public TypeTree findMethodUpwards(final MethodIdentifier methodIdentifier) {
        if (this.hasLocalMethod(methodIdentifier)) {
            return this;
        }
        if (this.superType != null) {
            return this.superType.findMethodUpwards(methodIdentifier);
        }
        return null;
    }

    /**
     * @param methodIdentifier a method identifier.
     * @return the first interface that defines a method with the same name and
     * descriptor as given in the identifier when walking upwards through the
     * implemented interfaces
     */
    public TypeTree findMethodUpwardsInterfaces(final MethodIdentifier methodIdentifier) {
        if (this.hasLocalMethod(methodIdentifier)) {
            return this;
        }
        TypeTree result;
        for (final TypeTree implementedInterface : this.implementedInterfaces) {
            result =
                implementedInterface.findMethodUpwardsInterfaces(methodIdentifier);
            if (result != null) {
                return result;
            }
        }
        return null;
    }

    /**
     * @param methodIdentifier the method identifier
     * @return the access flags of the method iff this class/interface declares
     * a method with the name and descriptor defined in the given identifier
     */
    public Integer getMethodAccessFlags(final MethodIdentifier methodIdentifier) {
        return this.methods.get(methodIdentifier.getMethodName()
            + methodIdentifier.getDescriptor());
    }

    /**
     * @param name some class name
     * @return true iff any super type has the given name
     */
    public boolean containsSuperType(final ClassName name) {
        if (this.superType != null) {
            if (this.superType.getClassName().equals(name)) {
                return true;
            }
            return this.superType.containsSuperType(name);
        }
        return false;
    }

    /**
     * @param name some class name
     * @return true iff any super interface has the given name
     */
    public boolean containsImplementedInterface(final ClassName name) {
        boolean found = false;
        for (final TypeTree implementedInterface : this.implementedInterfaces) {
            if (implementedInterface.getClassName().equals(name)) {
                return true;
            }
            if (!found) {
                found = implementedInterface.containsImplementedInterface(name);
            }
        }
        return found;
    }

    /**
     * @param methodIdentifier the method identifier
     * @return true iff this class/interface declares a method with the name and
     * descriptor defined in the given identifier.
     */
    public boolean hasLocalMethod(final MethodIdentifier methodIdentifier) {
        return this.methods.containsKey(methodIdentifier.getMethodName()
            + methodIdentifier.getDescriptor());
    }

    /**
     * @return true if this class has the ACC_SUPER flag.
     */
    public boolean hasSuperFlag() {
        return this.superFlag;
    }

    /**
     * @return true iff this type is public
     */
    public boolean isPublic() {
        return this.isPublic;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result =
            prime * result
                + ((this.className == null) ? 0 : this.className.hashCode());
        result =
            prime
                * result
                + ((this.implementedInterfaces == null) ? 0
                    : this.implementedInterfaces.hashCode());
        result = prime * result + (this.isAbstract ? 1231 : 1237);
        result = prime * result + (this.isInterface ? 1231 : 1237);
        result = prime * result + (this.isPublic ? 1231 : 1237);
        result =
            prime * result
                + ((this.methods == null) ? 0 : this.methods.hashCode());
        result = prime * result + (this.superFlag ? 1231 : 1237);
        result =
            prime * result
                + ((this.superType == null) ? 0 : this.superType.hashCode());
        return result;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final TypeTree other = (TypeTree) obj;
        if (this.className == null) {
            if (other.className != null) {
                return false;
            }
        } else if (!this.className.equals(other.className)) {
            return false;
        }
        if (this.implementedInterfaces == null) {
            if (other.implementedInterfaces != null) {
                return false;
            }
        } else if (!this.implementedInterfaces.equals(other.implementedInterfaces)) {
            return false;
        }
        if (this.isAbstract != other.isAbstract) {
            return false;
        }
        if (this.isInterface != other.isInterface) {
            return false;
        }
        if (this.isPublic != other.isPublic) {
            return false;
        }
        if (this.methods == null) {
            if (other.methods != null) {
                return false;
            }
        } else if (!this.methods.equals(other.methods)) {
            return false;
        }
        if (this.superFlag != other.superFlag) {
            return false;
        }
        if (this.superType == null) {
            if (other.superType != null) {
                return false;
            }
        } else if (!this.superType.equals(other.superType)) {
            return false;
        }
        return true;
    }
}
