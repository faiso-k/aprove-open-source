package aprove.verification.oldframework.Bytecode.StateRepresentation;

import java.util.*;
import java.util.Map.Entry;

import org.json.*;

import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Utils.*;

/**
 * Contains the values of static fields.
 */
public class StaticFields implements Cloneable {
    /**
     * This map gives the value of the static field, if provided with the class
     * containing the field and the name of the field.
     */
    private final Map<ClassName, Map<String, AbstractVariableReference>> staticFields;

    /**
     * Create a new instance holding static field information.
     */
    public StaticFields() {
        this.staticFields = new LinkedHashMap<>();
    }

    /**
     * @return a clone of this graph
     */
    @Override
    public StaticFields clone() {
        final StaticFields clone = new StaticFields();

        for (final Map.Entry<ClassName, Map<String, AbstractVariableReference>> e : this.staticFields.entrySet()) {
            final ClassName key = e.getKey();
            final Map<String, AbstractVariableReference> innerMap = new LinkedHashMap<>();
            clone.staticFields.put(key, innerMap);
            for (final Map.Entry<String, AbstractVariableReference> innerEntry : e.getValue().entrySet()) {
                innerMap.put(innerEntry.getKey(), innerEntry.getValue().clone());
            }

        }

        return clone;
    }

    /**
     * @return a nice string representation
     */
    @Override
    public String toString() {
        return this.toString(null, null);
    }

    /**
     * @param varUsers a map giving information about the number of places a
     * given reference is used.
     * @param state current state
     * @return String representation of this
     */
    public String toString(final Map<AbstractVariableReference, Integer> varUsers, final State state) {
        return this.toString(varUsers, state, true);
    }

    /**
     * @param varUsers a map giving information about the number of places a
     * given reference is used.
     * @param state current state
     * @param uninterestingStaticFieldUsage count how often references are
     * stored in uninteresting fields (may be null)
     * @return String representation of this
     */
    public String toString(
        final Map<AbstractVariableReference, Integer> varUsers,
        final State state,
        final boolean shortRepresentation)
    {
        final StringBuilder sb = new StringBuilder();

        for (final Map.Entry<ClassName, Map<String, AbstractVariableReference>> e : this.staticFields.entrySet()) {
            final ClassName parsedClass = e.getKey();
            for (final Map.Entry<String, AbstractVariableReference> innerEntry : e.getValue().entrySet()) {
                final FieldIdentifier fieldId = new FieldIdentifier(parsedClass, innerEntry.getKey());
                if (!state.getTerminationGraph().markedAsInterestingStaticField(fieldId)) {
                    continue;
                }
                //do not print serialVersionUID
                if (JBCOptions.HIDE_SERIAL_VERSION_UID && fieldId.getFieldName().equals("serialVersionUID"))
                    continue;
                sb
                    .append("\t")
                    .append(fieldId)
                    .append(": ")
                    .append(
                        PrettyVariablePrinter.prettyPrint(innerEntry.getValue(), varUsers, state, shortRepresentation))
                    .append("\n");
            }
        }
        return sb.toString();
    }

    /**
     * This method stores for each abstract variable reference how often the
     * corresponding variable is used inside the state.
     * @param res the map holding the result
     * @param s state to look at
     */
    public final void getReferences(final Map<AbstractVariableReference, Integer> res) {
        for (final Map.Entry<ClassName, Map<String, AbstractVariableReference>> entry : this.staticFields.entrySet()) {
            for (final Map.Entry<String, AbstractVariableReference> innerEntry : entry.getValue().entrySet()) {
                //if (s.wasAccessed(entry.getKey(), innerEntry.getKey())) {
                res.put(innerEntry.getValue(), res.get(innerEntry.getValue()) + 1);
                //}
            }
        }
    }

    /**
     * Replace oldRef by newRef
     * @param oldRef a reference
     * @param newRef another reference
     */
    public void replaceReference(final AbstractVariableReference oldRef, final AbstractVariableReference newRef) {
        for (final Map.Entry<ClassName, Map<String, AbstractVariableReference>> entry : this.staticFields.entrySet()) {
            for (final Map.Entry<String, AbstractVariableReference> innerEntry : entry.getValue().entrySet()) {
                if (innerEntry.getValue().equals(oldRef)) {
                    innerEntry.setValue(newRef);
                }
            }
        }
    }

    /**
     * @param parsedClass the class with the field
     * @param name the name of the static field
     * @return the value currently stored in the referenced static field
     */
    public AbstractVariableReference get(final ClassName className, final String name) {
        final Map<String, AbstractVariableReference> innerMap = this.staticFields.get(className);
        if (innerMap == null) {
            return null;
        }
        return innerMap.get(name);
    }

    /**
     * Store a new value in the referenced static field.
     * @param className the class with the field
     * @param name the name of the field
     * @param value the new value
     */
    public void set(final ClassName className, final String name, final AbstractVariableReference value) {
        assert (value != null);
        Map<String, AbstractVariableReference> innerMap = this.staticFields.get(className);
        if (innerMap == null) {
            innerMap = new LinkedHashMap<>();
            this.staticFields.put(className, innerMap);
        }
        innerMap.put(name, value);
    }

    /**
     * @return all classes for which we know some static field
     */
    public Collection<ClassName> getClasses() {
        return this.staticFields.keySet();
    }

    /**
     * @return all the references stored for static fields.
     */
    public Collection<AbstractVariableReference> getValues() {
        final Collection<AbstractVariableReference> result = new LinkedHashSet<>();
        for (final Map<String, AbstractVariableReference> map : this.staticFields.values()) {
            result.addAll(map.values());
        }
        return result;
    }

    /**
     * @return all the references stored for static fields.
     */
    public Set<Entry<ClassName, Map<String, AbstractVariableReference>>> getEntries() {
        return this.staticFields.entrySet();
    }

    /**
     * @param className the class that declares the fields
     * @return a set containing all names of static fields of the given class
     */
    public Set<String> getNames(final ClassName className) {
        final Map<String, AbstractVariableReference> innerMap = this.staticFields.get(className);
        assert (innerMap != null);
        return innerMap.keySet();
    }

    /**
     * Drop all information about static fields.
     * @param className some classname
     */
    public void dropInformationAbout(final ClassName className) {
        this.staticFields.remove(className);
    }

    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        for (Entry<ClassName, Map<String, AbstractVariableReference>> e1 : this.staticFields.entrySet()) {
            final ClassName cName = e1.getKey();
            for (Entry<String, AbstractVariableReference> e2 : e1.getValue().entrySet()) {
                final String fName = e2.getKey();
                final AbstractVariableReference ref = e2.getValue();
                res.put(cName.toString() + "." + fName, ref.toString());
            }
        }
        return res;
    }
}
