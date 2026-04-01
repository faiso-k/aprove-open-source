package aprove.verification.oldframework.Bytecode.Utils.MethodSummary;

import org.json.JSONArray;
import org.json.JSONObject;

import aprove.verification.oldframework.Algebra.Polynomials.*;

import java.util.*;

public class ComplexitySummary {

    public final SimplePolynomial lowerTime, upperTime, lowerSpace, upperSpace;

    public final SizeBounds sizeBounds;
    public final Set<String> modifies;

    public final Set<String> throwsSet;
    public final boolean alwaysThrows;

    public final Predicate predicate;

    public final AnnotationCollection resulting;
    public final AnnotationCollection removed;

    public final boolean terminates;

    public ComplexitySummary(SimplePolynomial lowerTime,
                             SimplePolynomial upperTime,
                             SimplePolynomial lowerSpace,
                             SimplePolynomial upperSpace,
                             SizeBounds sizeBounds,
                             Set<String> modifies) {
        this(lowerTime,
             upperTime,
             lowerSpace,
             upperSpace,
             sizeBounds,
             modifies,
             new LinkedHashSet<>(),
             false,
             null,
             true,
             new AnnotationCollection(),
             new AnnotationCollection());
    }

    public ComplexitySummary(SimplePolynomial lowerTime,
                             SimplePolynomial upperTime,
                             SimplePolynomial lowerSpace,
                             SimplePolynomial upperSpace,
                             SizeBounds sizeBounds,
                             Set<String> modifies,
                             Set<String> throwsSet,
                             boolean alwaysThrows,
                             Predicate predicate,
                             boolean terminates,
                             AnnotationCollection resulting,
                             AnnotationCollection removed) {
        this.lowerTime = lowerTime;
        this.upperTime = upperTime;
        this.lowerSpace = lowerSpace;
        this.upperSpace = upperSpace;
        this.sizeBounds = sizeBounds;
        this.modifies = modifies;
        this.throwsSet = throwsSet;
        this.alwaysThrows = alwaysThrows;
        this.predicate = predicate;
        this.terminates = terminates;
        this.resulting = resulting;
        this.removed = removed;
    }

    public Set<String> getVariables() {
        Set<String> res = new LinkedHashSet<>();
        res.addAll(lowerTime.getVariables());
        res.addAll(upperTime.getVariables());
        res.addAll(lowerSpace.getVariables());
        res.addAll(upperSpace.getVariables());
        return res;
    }

    public JSONObject toJSON() {
        JSONObject complexity = new JSONObject()
                .put(JSONKeys.LowerTime.toString(), lowerTime.toString())
                .put(JSONKeys.UpperTime.toString(), upperTime.toString())
                .put(JSONKeys.LowerSpace.toString(), lowerSpace.toString())
                .put(JSONKeys.UpperSpace.toString(), upperSpace.toString());
        JSONObject res = new JSONObject()
                .put(JSONKeys.Complexity.toString(), complexity)
                .put(JSONKeys.LowerSize.toString(), sizeBounds.lowerToJSON())
                .put(JSONKeys.UpperSize.toString(), sizeBounds.upperToJSON())
                .put(JSONKeys.Modifies.toString(), new JSONArray(modifies.toArray()))
                .put(JSONKeys.AlwaysThrows.toString(), alwaysThrows);
        if (!throwsSet.isEmpty()) {
            res.put(JSONKeys.Throws.toString(), new JSONArray(throwsSet.toArray()));
        }
        if (predicate != null) {
            res.put(JSONKeys.Predicate.toString(), predicate.toJSON());
        }
        return res;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((lowerSpace == null) ? 0 : lowerSpace.hashCode());
        result = prime * result + ((lowerTime == null) ? 0 : lowerTime.hashCode());
        result = prime * result + ((upperSpace == null) ? 0 : upperSpace.hashCode());
        result = prime * result + ((upperTime == null) ? 0 : upperTime.hashCode());
        result = prime * result + ((sizeBounds == null) ? 0 : sizeBounds.hashCode());
        result = prime * result + ((modifies == null) ? 0 : modifies.hashCode());
        result = prime * result + ((predicate == null) ? 0 : predicate.hashCode());
        result = prime * result + (alwaysThrows ? 1 : 0);
        result = prime * result + ((throwsSet == null) ? 0 : throwsSet.hashCode());
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
        ComplexitySummary other = (ComplexitySummary) obj;
        if (lowerSpace == null) {
            if (other.lowerSpace != null)
                return false;
        } else if (!lowerSpace.equals(other.lowerSpace))
            return false;
        if (lowerTime == null) {
            if (other.lowerTime != null)
                return false;
        } else if (!lowerTime.equals(other.lowerTime))
            return false;
        if (upperSpace == null) {
            if (other.upperSpace != null)
                return false;
        } else if (!upperSpace.equals(other.upperSpace))
            return false;
        if (upperTime == null) {
            if (other.upperTime != null)
                return false;
        } else if (!upperTime.equals(other.upperTime))
            return false;
        if (sizeBounds == null) {
            if (other.sizeBounds != null)
                return false;
        } else if (!sizeBounds.equals(other.sizeBounds))
            return false;
        if (modifies == null) {
            if (other.modifies != null)
                return false;
        } else if (!modifies.equals(other.modifies))
            return false;
        if (predicate == null) {
            if (other.predicate != null)
                return false;
        } else if (!predicate.equals(other.predicate))
            return false;
        if (alwaysThrows != other.alwaysThrows) {
            return false;
        }
        if (throwsSet == null) {
            if (other.throwsSet != null)
                return false;
        } else if (!throwsSet.equals(other.throwsSet))
            return false;
        return true;
    }

    public boolean equals(ComplexitySummary other, PolyComperator comperator) {
        if (this == other)
            return true;
        if (other == null)
            return false;
        if (lowerSpace == null) {
            if (other.lowerSpace != null)
                return false;
        } else if (!comperator.equal(lowerSpace, other.lowerSpace))
            return false;
        if (lowerTime == null) {
            if (other.lowerTime != null)
                return false;
        } else if (!comperator.equal(lowerTime, other.lowerTime))
            return false;
        if (upperSpace == null) {
            if (other.upperSpace != null)
                return false;
        } else if (!comperator.equal(upperSpace, other.upperSpace))
            return false;
        if (upperTime == null) {
            if (other.upperTime != null)
                return false;
        } else if (!comperator.equal(upperTime, other.upperTime))
            return false;
        if (sizeBounds == null) {
            if (other.sizeBounds != null)
                return false;
        } else if (!sizeBounds.equals(other.sizeBounds))
            return false;
        if (modifies == null) {
            if (other.modifies != null)
                return false;
        } else if (!modifies.equals(other.modifies))
            return false;
        if (predicate == null) {
            if (other.predicate != null)
                return false;
        } else if (!predicate.equals(other.predicate))
            return false;
        if (alwaysThrows != other.alwaysThrows) {
            return false;
        }
        if (throwsSet == null) {
            if (other.throwsSet != null)
                return false;
        } else if (!throwsSet.equals(other.throwsSet))
            return false;
        return true;
    }

    public boolean validate(Set<String> vars) {
        boolean valid = vars.containsAll(getVariables());
        assert valid :
                "complexity bounds of method summary contain the forbidden variables "
                + getVariables()
                + ", but only "
                + vars
                + " are allowed";
        valid &= vars.containsAll(modifies);
        assert valid :
                "modifies-set of method summary is " + modifies + ", but only subsets of " + vars + " are allowed";
        Set<String> allVars = new LinkedHashSet<>(vars);
        allVars.add("ret");
        valid &= allVars.containsAll(sizeBounds.getVariables());
        assert valid :
                "size bounds of method summary contain the variables "
                + sizeBounds.getVariables()
                + ", but only "
                + allVars
                + " are allowed";
        Set<String> hasSizeBound = sizeBounds.geKeys();
        hasSizeBound.remove("ret");
        hasSizeBound.remove("static");
        hasSizeBound.remove("env");
        valid &= modifies.containsAll(hasSizeBound);
        assert valid :
                "summary for specifies sizebounds for arguments that aren't modified";

        return valid;
    }

    public static ComplexitySummary parseFromJSONObject(JSONObject complexityCase) {
        SimplePolynomial lowerTime, upperTime, lowerSpace, upperSpace;
        boolean terminates = true;
        if (complexityCase.has(JSONKeys.Complexity.toString())) {
            JSONObject complexity = complexityCase.getJSONObject(JSONKeys.Complexity.toString());
            if (complexity.has(JSONKeys.LowerTime.toString())) {
                lowerTime = SimplePolynomial.parse(complexity.getString(JSONKeys.LowerTime.toString()));
            } else {
                lowerTime = SimplePolynomial.ZERO;
            }
            if (complexity.has(JSONKeys.UpperTime.toString())) {
                if ("inf".equalsIgnoreCase(complexity.getString(JSONKeys.UpperTime.toString()))) {
                    terminates = false;
                    upperTime = SimplePolynomial.ONE;
                } else {
                    upperTime = SimplePolynomial.parse(complexity.getString(JSONKeys.UpperTime.toString()));
                }
            } else {
                upperTime = SimplePolynomial.ONE;
            }
            if (complexity.has(JSONKeys.LowerSpace.toString())) {
                lowerSpace = SimplePolynomial.parse(complexity.getString(JSONKeys.LowerSpace.toString()));
            } else {
                lowerSpace = SimplePolynomial.ZERO;
            }
            if (complexity.has(JSONKeys.UpperSpace.toString())) {
                upperSpace = SimplePolynomial.parse(complexity.getString(JSONKeys.UpperSpace.toString()));
            } else {
                upperSpace = SimplePolynomial.ZERO;
            }
        } else {
            lowerTime = SimplePolynomial.ONE;
            upperTime = SimplePolynomial.ONE;
            lowerSpace = SimplePolynomial.ZERO;
            upperSpace = SimplePolynomial.ZERO;
        }

        Predicate predicate = null;
        if (complexityCase.has(JSONKeys.Predicate.toString())) {
            JSONObject predicateObj = complexityCase.getJSONObject(JSONKeys.Predicate.toString());
            PredicateType predicateType = PredicateType.getByString(predicateObj.getString(JSONKeys.Type.toString()));
            String
                    var0 =
                    predicateObj.has(JSONKeys.Var0.toString()) ?
                    predicateObj.getString(JSONKeys.Var0.toString()) :
                    null;
            String
                    var1 =
                    predicateObj.has(JSONKeys.Var1.toString()) ?
                    predicateObj.getString(JSONKeys.Var1.toString()) :
                    null;
            if (predicateType != null) {
                predicate = new Predicate(predicateType, var0, var1);
            }
        }

        SizeBounds sizeBounds = new SizeBounds();
        if (complexityCase.has(JSONKeys.LowerSize.toString())) {
            JSONArray lowerSizes = complexityCase.getJSONArray(JSONKeys.LowerSize.toString());
            for (Object oo : lowerSizes) {
                JSONObject ls = (JSONObject) oo;
                String key = ls.getString(JSONKeys.Pos.toString());
                SimplePolynomial bound = SimplePolynomial.parse(ls.getString(JSONKeys.Bound.toString()));
                sizeBounds.addLowerBound(key, bound);
            }
        }
        if (complexityCase.has(JSONKeys.UpperSize.toString())) {
            JSONArray upperSizes = complexityCase.getJSONArray(JSONKeys.UpperSize.toString());
            for (Object oo : upperSizes) {
                JSONObject us = (JSONObject) oo;
                String key = us.getString(JSONKeys.Pos.toString());
                SimplePolynomial bound = SimplePolynomial.parse(us.getString(JSONKeys.Bound.toString()));
                sizeBounds.addUpperBound(key, bound);
            }
        }

        Set<String> modifies = new LinkedHashSet<>();
        if (complexityCase.has(JSONKeys.Modifies.toString())) {
            JSONArray jsonModifies = complexityCase.getJSONArray(JSONKeys.Modifies.toString());
            for (Object oo : jsonModifies) {
                modifies.add((String) oo);
            }
        }

        Set<String> maybeThrows = new LinkedHashSet<>();
        if (complexityCase.has(JSONKeys.Throws.toString())) {
            Object maybeThrowsJson = complexityCase.get(JSONKeys.Throws.toString());
            if (maybeThrowsJson instanceof String) {
                maybeThrows.add((String) maybeThrowsJson);
            } else if (maybeThrowsJson instanceof JSONArray) {
                for (Object oo : (JSONArray) maybeThrowsJson) {
                    maybeThrows.add((String) oo);
                }
            } else {
                throw new IllegalArgumentException("Illegal JSON schema");
            }
        }


        AnnotationCollection resulting = complexityCase.has(JSONKeys.ResultingPredicates.toString())
                ? AnnotationCollection.parseFromJSONObject(complexityCase.getJSONObject(JSONKeys.ResultingPredicates.toString()))
                : new AnnotationCollection();

        AnnotationCollection removed = complexityCase.has(JSONKeys.RemovedPredicates.toString())
                                         ? AnnotationCollection.parseFromJSONObject(complexityCase.getJSONObject(JSONKeys.RemovedPredicates.toString()))
                                         : new AnnotationCollection();

        boolean alwaysThrows = complexityCase.has(JSONKeys.AlwaysThrows.toString())
                               && complexityCase.getBoolean(JSONKeys.AlwaysThrows.toString());
        return new ComplexitySummary(lowerTime,
                                     upperTime,
                                     lowerSpace,
                                     upperSpace,
                                     sizeBounds,
                                     modifies,
                                     maybeThrows,
                                     alwaysThrows,
                                     predicate,
                                     terminates,
                                     resulting,
                                     removed);
    }
}
