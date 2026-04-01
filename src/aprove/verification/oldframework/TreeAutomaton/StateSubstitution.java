package aprove.verification.oldframework.TreeAutomaton;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import immutables.*;

/**
 * A state substitution maps a variable to a state.
 * @author Marcel Klinzing
 * @param <Z> The type of a state.
 */
public class StateSubstitution<Z> {
    private final ImmutableMap<TRSVariable, Z> map;

    // computed values
    private final int hash;

    private StateSubstitution(ImmutableMap<TRSVariable, Z> Map) {
        this.map = Map;

        int hash = 0;
        for (Map.Entry<TRSVariable, Z> entry : this.map.entrySet()) {
            hash += 34727 * entry.getKey().hashCode();
            hash += 893459 * entry.getValue().hashCode();
        }
        this.hash = hash;
    }

    public static <Z> StateSubstitution<Z> create(Map<TRSVariable, Z> Map) {
        ImmutableMap<TRSVariable, Z> iMap = ImmutableCreator.create(Map);
        return new StateSubstitution<Z>(iMap);
    }

    public ImmutableMap<TRSVariable, Z> getMap() {
        return this.map;
    }

    public static <Z> StateSubstitution<Z> createEmpty() {
        Map<TRSVariable, Z> map = new LinkedHashMap<TRSVariable, Z>();
        return StateSubstitution.create(map);
    }


    @Override
    public int hashCode() {
        return this.hash;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        StateSubstitution<Object> other = (StateSubstitution<Object>) obj;
        if (this.map == null) {
            if (other.map != null) {
                return false;
            }
        } else {

            if (this.map.size() != other.map.size()) {
                return false;
            }

            for (Map.Entry<TRSVariable, Z> entry : this.map.entrySet()) {
                Object otherValue = other.map.get(entry.getKey());

                if (!entry.getValue().equals(otherValue)) {
                    return false;
                }
            }
        }
        return true;
    }

    @Override
    public String toString() {
        return "StateSubstitution [Map=" + this.map + "]";
    }

}
