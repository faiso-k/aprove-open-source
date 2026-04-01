package aprove.verification.oldframework.IntegerReasoning.octagondomain;

import java.math.*;
import java.util.*;

import org.json.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.IntegerReasoning.octagondomain.dbm.*;
import aprove.verification.oldframework.IntegerReasoning.utils.additionboundinference.*;
import aprove.verification.oldframework.IntegerReasoning.utils.intervals.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.JSON.*;

public class OctagonInterface implements IntegerState {

    /**
     * @param relation Some integer relation.
     * @return A triple (x,y,z) encoding x <= y <= z for two constants x and z and a variable y if the specified
     *         relation implies this (one of the constants may be null and then the corresponding constant is replaced
     *         by (-)infinity). Null if the relation does not imply such a constellation.
     */
    public static BoundInfo toBoundInfo(IntegerRelation relation) {
        // TODO Auto-generated method stub
        return null;
    }

    private final DifferenceBoundMatrix dbm;

    public OctagonInterface() {
        this.dbm = new DifferenceBoundMatrix();
    }

    public OctagonInterface(OctagonInterface other) {
        this.dbm = new DifferenceBoundMatrix(other.dbm);
    }

    @Override
    public IntegerState addRelation(IntegerRelation relation, Abortion aborter) {
        final OctagonInterface returnValue = new OctagonInterface(this);
        returnValue.addRelationMutate(relation);
        return returnValue;
    }

    @Override
    public IntegerState addRelationSet(Iterable<? extends IntegerRelation> relations, Abortion aborter) {
        final OctagonInterface returnValue = new OctagonInterface(this);
        for (IntegerRelation relation : relations) {
            returnValue.addRelationMutate(relation);
        }
        return returnValue;
    }

    @Override
    public Pair<Boolean, ? extends IntegerState> checkRelation(IntegerRelation relation, Abortion aborter) {
        BoundInfo info = OctagonInterface.toBoundInfo(relation);
        if (info != null) {
            final IntegerVariable reference = info.y;
            final IntegerInterval interval = IntegerInterval.create(info.x, info.z);
            final YNM evaluationResult = this.checkVariableEvaluation(reference, interval);
            if (!evaluationResult.equals(YNM.MAYBE)) {
                return new Pair<Boolean, IntegerState>(evaluationResult == YNM.YES, this);
            }
            // We could not infer the given evaluation, close the dbm and try again
            final DBMPosition lhsPos = this.dbm.getVariablePosition(reference);
            final DBMPosition rhsPos = this.dbm.getNegativeVariablePosition(reference);
            this.dbm.ensureClosure(lhsPos, rhsPos);
            return new Pair<Boolean, IntegerState>(this.checkVariableEvaluation(reference, interval) == YNM.YES, this);
        }
        final Collection<UnitAdditionBound> unitAdditionBounds =
            UnitAdditionBoundInference.inferUnitAdditionBounds(relation);
        if (unitAdditionBounds != null) {
            final YNM additionBoundResult = this.checkAdditionBounds(unitAdditionBounds);
            if (!additionBoundResult.equals(YNM.MAYBE)) {
                return new Pair<Boolean, IntegerState>(additionBoundResult == YNM.YES, this);
            }
            // We could not infer or refute the given unit addition bounds, close the dbm and try again
            for (UnitAdditionBound bound : unitAdditionBounds) {
                final DBMPosition lhsPos =
                    bound.isLhsVariableNegated()
                        ? this.dbm.getNegativeVariablePosition(bound.getLhsVariable())
                            : this.dbm.getVariablePosition(bound.getLhsVariable());
                final DBMPosition rhsPos =
                    bound.isRhsVariableNegated()
                        ? this.dbm.getNegativeVariablePosition(bound.getRhsVariable())
                            : this.dbm.getVariablePosition(bound.getRhsVariable());
                this.dbm.ensureClosure(lhsPos, rhsPos);
            }
            return new Pair<Boolean, IntegerState>(this.checkAdditionBounds(unitAdditionBounds) == YNM.YES, this);
        }
        return new Pair<Boolean, IntegerState>(false, this);
    }

//    @Override
//    public LLVMHeuristicVariable findReference(LLVMHeuristicTerm expression) {
//        if (expression == null) {
//            return null;
//        }
//        this.dbm.ensureClosure();
//        for (IntegerVariable variable : this.dbm.getVariables()) {
//            final IntegerRelation equalRelation = new IntegerRelation(LLVMHeuristicRelationType.EQ, variable, expression);
//            if (this.checkRelation(equalRelation) == YNM.YES) {
//                return variable;
//            }
//        }
//        return null;
//    }

    @Override
    public String toDOTString() {
        return this.toString();
    }

    @Override
    public Object toJSON() {
        JSONObject res = new JSONObject();
        res.put("type", this.getClass().getSimpleName());
        res.put("dbm", JSONExportUtil.toJSON(this.dbm));
        return res;
    }

    @Override
    public IntegerRelationSet toRelationSet() {
        return this.dbm.toRelationSet();
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        sb.append(this.getClass().getSimpleName());
        sb.append(": ");
        final Iterator<IntegerRelation> it = this.toRelationSet().iterator();
        while (it.hasNext()) {
            final IntegerRelation relation = it.next();
            sb.append(relation.toString());
            if (it.hasNext()) {
                sb.append(", ");
            }
        }
        return sb.toString();
    }

    boolean canInferAdditionBound(UnitAdditionBound unitAdditionBound) {
        final BigInteger queriedBound = unitAdditionBound.getBound();
        final DBMPosition lhsPosition;
        if (!unitAdditionBound.isLhsVariableNegated()) {
            lhsPosition = this.dbm.getVariablePosition(unitAdditionBound.getLhsVariable());
        } else {
            lhsPosition = this.dbm.getNegativeVariablePosition(unitAdditionBound.getLhsVariable());
        }
        final DBMPosition rhsPosition;
        if (unitAdditionBound.isRhsVariableNegated()) {
            rhsPosition = this.dbm.getVariablePosition(unitAdditionBound.getRhsVariable());
        } else {
            rhsPosition = this.dbm.getNegativeVariablePosition(unitAdditionBound.getRhsVariable());
        }
        final BigInteger knownBound = this.dbm.getDifferenceUpperBound(lhsPosition, rhsPosition);
        if (knownBound != null) {
            return knownBound.compareTo(queriedBound) <= 0;
        } else {
            return false;
        }
    }

    boolean canInferVariableEvaluation(IntegerVariable variable, IntegerInterval interval) {
        final BigInteger queriedLowerBound = interval.getLowerBoundIfFinite();
        if (queriedLowerBound != null) {
            final DBMPosition negatedPosition = this.dbm.getNegativeVariablePosition(variable);
            final BigInteger knownLowerBound = this.dbm.getUpperBound(negatedPosition);
            if (knownLowerBound == null || knownLowerBound.negate().compareTo(queriedLowerBound) < 0) {
                return false;
            } else {
                // We know that the lower bound of the variable is in the
                // queried interval, but we still have to check the upper bound
            }
        }
        final BigInteger queriedUpperBound = interval.getUpperBoundIfFinite();
        if (queriedUpperBound != null) {
            final DBMPosition position = this.dbm.getVariablePosition(variable);
            final BigInteger knownUpperBound = this.dbm.getUpperBound(position);
            if (knownUpperBound == null || knownUpperBound.compareTo(queriedUpperBound) > 0) {
                return false;
            } else {
                // We know that the queried variable is in the queried interval,
                // fall through to return true;
            }
        }
        return true;
    }

    boolean canRefuteAdditionBound(UnitAdditionBound unitAdditionBound) {
        final BigInteger queriedBound = unitAdditionBound.getBound();
        final DBMPosition lhsPosition;
        if (unitAdditionBound.isLhsVariableNegated()) {
            lhsPosition = this.dbm.getVariablePosition(unitAdditionBound.getLhsVariable());
        } else {
            lhsPosition = this.dbm.getNegativeVariablePosition(unitAdditionBound.getLhsVariable());
        }
        final DBMPosition rhsPosition;
        if (!unitAdditionBound.isRhsVariableNegated()) {
            rhsPosition = this.dbm.getVariablePosition(unitAdditionBound.getRhsVariable());
        } else {
            rhsPosition = this.dbm.getNegativeVariablePosition(unitAdditionBound.getRhsVariable());
        }
        final BigInteger knownBound = this.dbm.getDifferenceUpperBound(lhsPosition, rhsPosition);
        if (knownBound != null) {
            return knownBound.compareTo(queriedBound.negate()) < 0;
        } else {
            return false;
        }
    }

    boolean canRefuteVariableEvaluation(IntegerVariable variable, IntegerInterval interval) {
        final BigInteger queriedLowerBound = interval.getLowerBoundIfFinite();
        if (queriedLowerBound != null) {
            final DBMPosition position = this.dbm.getVariablePosition(variable);
            final BigInteger knownUpperBound = this.dbm.getUpperBound(position);
            if (knownUpperBound != null && knownUpperBound.compareTo(queriedLowerBound) < 0) {
                return true;
            } else {
                // Fall through to checking queried upper bound against known lower bound
            }
        }
        final BigInteger queriedUpperBound = interval.getUpperBoundIfFinite();
        if (queriedUpperBound != null) {
            final DBMPosition negatedPosition = this.dbm.getNegativeVariablePosition(variable);
            final BigInteger knownLowerBound = this.dbm.getUpperBound(negatedPosition);
            if (knownLowerBound != null && knownLowerBound.negate().compareTo(queriedUpperBound) > 0) {
                return true;
            } else {
                // We cannot infer that the given variable is not in the given interval,
                // so fall through to return false
            }
        }
        return false;
    }

    private void addRelationMutate(IntegerRelation relation) {
        final IntervalEvaluation inferredEvaluation = this.getImpliedIntervalEvaluation(relation);
        this.storeIntervalEvaluation(inferredEvaluation);
        final Collection<UnitAdditionBound> unitAdditionBounds = this.getImpliedUnitAdditionBounds(relation);
        if (unitAdditionBounds != null) {
            this.storeUnitAdditionBounds(unitAdditionBounds);
        }
    }

    private YNM checkAdditionBounds(Collection<UnitAdditionBound> unitAdditionBounds) {
        boolean canInfer = true;
        for (UnitAdditionBound bound : unitAdditionBounds) {
            if (canInfer && !this.canInferAdditionBound(bound)) {
                canInfer = false;
            }
            if (this.canRefuteAdditionBound(bound)) {
                return YNM.NO;
            }
        }
        if (canInfer) {
            return YNM.YES;
        } else {
            return YNM.MAYBE;
        }
    }

    private YNM checkVariableEvaluation(IntegerVariable reference, IntegerInterval interval) {
        if (this.canInferVariableEvaluation(reference, interval)) {
            return YNM.YES;
        } else if (this.canRefuteVariableEvaluation(reference, interval)) {
            return YNM.NO;
        } else {
            return YNM.MAYBE;
        }
    }

    private DBMPosition getDbmPosition(IntegerVariable unitVariable, boolean negated) {
        if (negated) {
            return this.dbm.getNegativeVariablePosition(unitVariable);
        } else {
            return this.dbm.getVariablePosition(unitVariable);
        }
    }

    private IntervalEvaluation getImpliedIntervalEvaluation(IntegerRelation relation) {
        final IntervalEvaluation returnValue = new IntervalEvaluation();
        BoundInfo info = OctagonInterface.toBoundInfo(relation);
        if (info != null) {
            returnValue.setInterval(info.y, IntegerInterval.create(info.x, info.z));
        }
        return returnValue;
    }

    /**
     * @param relation Some relation
     * @return A set of UnitAdditionBounds, all of which are implied by the relation.
     * May be empty, but is never null.
     */
    private Collection<UnitAdditionBound> getImpliedUnitAdditionBounds(IntegerRelation relation) {
        return UnitAdditionBoundInference.inferUnitAdditionBounds(relation);
    }

    private void storeIntervalEvaluation(IntervalEvaluation inferredEvaluation) {
        for (Map.Entry<IntegerVariable, IntegerInterval> variableEvaluation : inferredEvaluation.entrySet()) {
            this.storeVariableEvaluation(variableEvaluation.getKey(), variableEvaluation.getValue());
        }
    }

    private void storeSingleUnitAdditionBound(UnitAdditionBound unitAdditionBound) {
        final DBMPosition firstPosition =
            this.getDbmPosition(unitAdditionBound.getLhsVariable(), unitAdditionBound.isLhsVariableNegated());
        /* Since we only store x - y rel c, but have a relation of the form
         * x + y rel c, we instead check for x - (-y) rel c and get (-y) for that */
        final DBMPosition secondPosition =
            this.getDbmPosition(unitAdditionBound.getRhsVariable(), !unitAdditionBound.isRhsVariableNegated());
        this.dbm.tightenDifferenceUpperBound(firstPosition, secondPosition, unitAdditionBound.getBound());
    }

    private void storeUnitAdditionBounds(Collection<UnitAdditionBound> unitAdditionBounds) {
        for (UnitAdditionBound unitAdditionBound : unitAdditionBounds) {
            this.storeSingleUnitAdditionBound(unitAdditionBound);
        }
    }

    private void storeVariableEvaluation(IntegerVariable variable, IntegerInterval evaluation) {
        final DBMPosition positivePosition = this.dbm.getVariablePosition(variable);
        final DBMPosition negativePosition = this.dbm.getNegativeVariablePosition(variable);
        final BigInteger lowerBound = evaluation.getLowerBoundIfFinite();
        if (lowerBound != null) {
            this.dbm.tightenUpperBound(negativePosition, lowerBound.negate());
        }
        final BigInteger upperBound = evaluation.getUpperBoundIfFinite();
        if (upperBound != null) {
            this.dbm.tightenUpperBound(positivePosition, upperBound);
        }
    }

}
