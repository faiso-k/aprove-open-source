package aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Data.Relation;

import java.util.*;

import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author marinag
 * Generic representation of the next value used in the class Relation
 * @param <T>
 */
public abstract class INextValue<T> {
    protected T value;

    public INextValue(final T value) {
        this.value = value;
    }

    public abstract T apply(List<Pair<String, T>> nextMap);

    public abstract INextValue<T> createNextValue(String name);

    public T getValue() {
        return this.value;
    }

    public boolean isIdentity(final String name) {
        return this.getValue().equals(this.createNextValue(name).getValue());
    }

    @Override
    public String toString() {
        if (this.value == null) {
            return "{?}";
        }

        return this.value.toString();
    }

    public abstract Set<String> getVariables();

    public abstract INextValue<T> rename(Map<String, String> renaming);
}
