package aprove.verification.oldframework.Bytecode.Utils.MethodSummary;

import org.json.JSONArray;
import org.json.JSONObject;

import aprove.verification.oldframework.Algebra.Polynomials.*;

import static aprove.verification.oldframework.Utility.Collection_Util.*;

import java.util.*;

public class SizeBounds {

    private final Map<String, SimplePolynomial> upperBounds = new LinkedHashMap<>();
    private final Map<String, SimplePolynomial> lowerBounds = new LinkedHashMap<>();

    public void addLowerBound(String key, SimplePolynomial bound) {
        assert !lowerBounds.containsKey(key);
        assert bound != null;
        lowerBounds.put(key, bound);
    }

    public void addUpperBound(String key, SimplePolynomial bound) {
        assert !upperBounds.containsKey(key);
        assert bound != null;
        upperBounds.put(key, bound);
    }

    public Optional<SimplePolynomial> getLowerBound(String key) {
        if (lowerBounds.containsKey(key)) {
            return Optional.of(lowerBounds.get(key));
        } else {
            return Optional.empty();
        }
    }

    public Optional<SimplePolynomial> getUpperBound(String key) {
        if (upperBounds.containsKey(key)) {
            return Optional.of(upperBounds.get(key));
        } else {
            return Optional.empty();
        }
    }

    public Set<String> getVariables() {
        Set<String> res = new LinkedHashSet<>();
        res.addAll(upperBounds.keySet());
        res.addAll(lowerBounds.keySet());
        upperBounds.values().forEach(x -> res.addAll(x.getVariables()));
        lowerBounds.values().forEach(x -> res.addAll(x.getVariables()));
        return res;
    }

    private static JSONArray boundsToJSON(Map<String, SimplePolynomial> bounds) {
        JSONArray res = new JSONArray();
        for (Map.Entry<String, SimplePolynomial> entry : bounds.entrySet()) {
            res.put(new JSONObject()
                            .put(JSONKeys.Pos.toString(), entry.getKey())
                            .put(JSONKeys.Bound.toString(), entry.getValue().toString())
            );
        }
        return res;
    }

    public JSONArray upperToJSON() {
        return boundsToJSON(upperBounds);
    }

    public JSONArray lowerToJSON() {
        return boundsToJSON(lowerBounds);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((lowerBounds == null) ? 0 : lowerBounds.hashCode());
        result = prime * result + ((upperBounds == null) ? 0 : upperBounds.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        SizeBounds other = (SizeBounds) obj;
        if (lowerBounds == null) {
            if (other.lowerBounds != null)
                return false;
        } else if (!lowerBounds.equals(other.lowerBounds))
            return false;
        if (upperBounds == null) {
            if (other.upperBounds != null)
                return false;
        } else if (!upperBounds.equals(other.upperBounds))
            return false;
        return true;
    }

    public boolean equals(SizeBounds other, PolyComperator comperator) {
        if (this == other)
            return true;
        if (other == null)
            return false;
        if (lowerBounds == null) {
            if (other.lowerBounds != null)
                return false;
        }
        if (lowerBounds.size() != other.lowerBounds.size())
            return false;
        for (Map.Entry<String, SimplePolynomial> entry : lowerBounds.entrySet()) {
            SimplePolynomial otherPoly = other.lowerBounds.get(entry.getKey());
            if (otherPoly == null)
                return false;
            if (!comperator.equal(entry.getValue(), otherPoly))
                return false;
        }

        if (upperBounds == null) {
            if (other.upperBounds != null)
                return false;
        }
        if (upperBounds.size() != other.upperBounds.size())
            return false;
        for (Map.Entry<String, SimplePolynomial> entry : upperBounds.entrySet()) {
            SimplePolynomial otherPoly = other.upperBounds.get(entry.getKey());
            if (otherPoly == null)
                return false;
            if (!comperator.equal(entry.getValue(), otherPoly))
                return false;
        }
        return true;
    }

    public Set<String> geKeys() {
        return union(lowerBounds.keySet(), upperBounds.keySet());
    }
}
