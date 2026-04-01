package aprove.verification.oldframework.Bytecode.Graphs.Reachability;

import java.util.*;

import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Utils.*;

/**
 * Label for edges connecting class instances on the heap with other objects.
 *
 * @author Marc Brockschmidt
 */
public class InstanceFieldEdge extends HeapEdge {
    /**
     * The field we use to point to some object.
     */
    private final FieldIdentifier fieldIdentifier;

    /**
     * @return the className
     */
    public ClassName getClassName() {
        return this.fieldIdentifier.getClassName();
    }

    /**
     * @return the fieldName
     */
    public String getFieldName() {
        return this.fieldIdentifier.getFieldName();
    }

    /**
     * @return the field identifier for the represented field
     */
    public FieldIdentifier getFieldIdentifier() {
        return this.fieldIdentifier;
    }

    /**
     * @param cName Classname of the class containing the field used to point
     * to another object.
     * @param fName Name of the class field used to point to another object.
     */
    public InstanceFieldEdge(final ClassName cName, final String fName) {
        this.fieldIdentifier = new FieldIdentifier(cName, fName);
    }

    /**
     * @param fieldIdentifierParam a field identifier
     */
    public InstanceFieldEdge(final FieldIdentifier fieldIdentifierParam) {
        this.fieldIdentifier = fieldIdentifierParam;
    }

    public static InstanceFieldEdge createFromDotted(String s) {
        String className = s.substring(0, s.lastIndexOf("."));
        String fieldName = s.substring(s.lastIndexOf(".") + 1);
        assert !"".equals(className) && !"".equals(fieldName);
        return new InstanceFieldEdge(new FieldIdentifier(ClassName.fromDotted(className), fieldName));
    }

    /** {@inheritDoc} */
    @Override
    public String getIdentifier() {
        return this.fieldIdentifier.getClassName().getClassName() + "." + this.fieldIdentifier.getFieldName();
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return this.getIdentifier();
    }

    public static boolean fieldsAreDeterministic(final Set<HeapEdge> fields, final ClassPath classPath) {
        final Set<ClassName> classNames = new LinkedHashSet<ClassName>();

        for (final HeapEdge field : fields) {
            if (!(field instanceof InstanceFieldEdge)) {
                return false;
            }

            final ClassName className = ((InstanceFieldEdge) field).getClassName();
            if (classNames.contains(className)) { // check for duplicates
                return false;
            }
            classNames.add(className);
        }

        for (final ClassName className : classNames) { // check for superclasses
            final Collection<TypeTree> superClasses = classPath.getTypeTree(className).getAllSuperClasses();
            for (final TypeTree superClass : superClasses) {
                if (!superClass.getClassName().equals(className) && classNames.contains(superClass.getClassName())) {
                    return false;
                }
            }
        }

        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public NonRootPosition getNonRootPosition() {
        return InstanceFieldPosition.create(null, this.fieldIdentifier);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.fieldIdentifier == null) ? 0 : this.fieldIdentifier.hashCode());
        return result;
    }

    /**
     * {@inheritDoc}
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
        final InstanceFieldEdge other = (InstanceFieldEdge) obj;
        if (this.fieldIdentifier == null) {
            if (other.fieldIdentifier != null) {
                return false;
            }
        } else if (!this.fieldIdentifier.equals(other.fieldIdentifier)) {
            return false;
        }
        return true;
    }
}
