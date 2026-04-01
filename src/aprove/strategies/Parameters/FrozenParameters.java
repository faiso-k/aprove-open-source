package aprove.strategies.Parameters;

import java.util.*;

import aprove.strategies.UserStrategies.*;
import immutables.*;

public class FrozenParameters {
    public static final FrozenParameters EMPTY = new FrozenParameters(Collections.<String, ParamValue>emptyMap(), null);

    private final ImmutableMap<String, ParamValue> map;

    private final ImmutableMap<String, ParamValue> ucaseMap;

    private final ImmutableList<UserStrategy> subStrategies;

    public FrozenParameters(Map<String, ParamValue> paramMap, List<UserStrategy> subStrategies) {
        Map<String, ParamValue> ucase = new LinkedHashMap<String, ParamValue>();
        for(Map.Entry<String, ParamValue> e: paramMap.entrySet()) {
            ucase.put(e.getKey().toUpperCase(), e.getValue());
        }
        this.map = ImmutableCreator.create(paramMap);
        this.ucaseMap = ImmutableCreator.create(ucase);
        if (subStrategies == null) {
            this.subStrategies = null;
        } else {
            this.subStrategies = ImmutableCreator.create(subStrategies);
        }
    }

    public FrozenParameters(Map<String, ParamValue> paramMap) {
        this(paramMap, null);
    }

    public Set<Map.Entry<String, ParamValue>> entries() {
        return this.map.entrySet();
    }

    public boolean containsKey(String key) {
        return this.ucaseMap.containsKey(key.toUpperCase());
    }

    public ParamValue get(String key) {
        return this.ucaseMap.get(key.toUpperCase());
    }

    public boolean isEmpty() {
        return this.map.isEmpty() && !this.hasSubStrategies();
    }

    public boolean hasSubStrategies() {
        return this.subStrategies != null;
    }

    public ImmutableList<UserStrategy> getSubStrategies() {
        return this.subStrategies;
    }

    @Override
    public String toString() {
        StringBuilder result = new StringBuilder();
        boolean mid = false;
        result.append("[");
        for(Map.Entry<String, ParamValue> e: this.map.entrySet()) {
            if (mid) {
                result.append(", ");
            }
            mid = true;
            result.append(e);
        }
        result.append("]");
        if (this.hasSubStrategies()) {
            mid = false;
            result.append("(");
            for(UserStrategy sub: this.subStrategies) {
                if (mid) {
                    result.append(", ");
                }
                mid=true;
                result.append(sub);
            }
            result.append(")");
        }
        return result.toString();
    }
}
