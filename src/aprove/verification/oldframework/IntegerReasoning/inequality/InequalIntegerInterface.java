package aprove.verification.oldframework.IntegerReasoning.inequality;

import java.util.*;

import org.json.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.JSON.*;

public class InequalIntegerInterface implements IntegerState {

    private final Map<IntegerVariable, Set<IntegerVariable>> inequalitySets;

    public InequalIntegerInterface() {
        this.inequalitySets = new HashMap<>();
    }

    private InequalIntegerInterface(final InequalIntegerInterface other) {
        this.inequalitySets = new HashMap<>(other.inequalitySets);
    }

    private InequalIntegerInterface(final Map<IntegerVariable, Set<IntegerVariable>> inequalitySets) {
        this.inequalitySets = inequalitySets;
    }

    @Override
    public IntegerState addRelation(final IntegerRelation relation, Abortion aborter) {
        final Pair<IntegerVariable, IntegerVariable> inequality = this.getInequality(relation);
        if (inequality != null) {
            final InequalIntegerInterface returnValue = new InequalIntegerInterface(this);
            returnValue.addInequalityMutate(inequality.x, inequality.y);
            return returnValue;
        } else {
            return this;
        }
    }

    @Override
    public IntegerState addRelationSet(final Iterable<? extends IntegerRelation> relations, Abortion aborter) {
        final InequalIntegerInterface returnValue = new InequalIntegerInterface(this);
        for (final IntegerRelation relation : relations) {
            final Pair<IntegerVariable, IntegerVariable> inequality = this.getInequality(relation);
            if (inequality != null) {
                returnValue.addInequalityMutate(inequality.x, inequality.y);
            }
        }
        return returnValue;
    }

    @Override
    public Pair<Boolean, ? extends IntegerState> checkRelation(final IntegerRelation relation, Abortion aborter) {
        if (
            relation.getRelationType().equals(IntegerRelationType.LE)
            || relation.getRelationType().equals(IntegerRelationType.GE)
        ) {
            return new Pair<Boolean, IntegerState>(false, this);
        }
        final IntegerVariable lhsVarRef, rhsVarRef;
        if (relation.getLhs() instanceof IntegerVariable) {
            lhsVarRef = (IntegerVariable)relation.getLhs();
        } else {
            return new Pair<Boolean, IntegerState>(false, this);
        }
        if (relation.getRhs() instanceof IntegerVariable) {
            rhsVarRef = (IntegerVariable)relation.getRhs();
        } else {
            return new Pair<Boolean, IntegerState>(false, this);
        }
        final boolean knownToBeUnequal =
            this.inequalitySets.containsKey(lhsVarRef) && this.inequalitySets.get(lhsVarRef).contains(rhsVarRef);
        if (
            relation.getRelationType().equals(IntegerRelationType.LT)
            || relation.getRelationType().equals(IntegerRelationType.GT)
            || relation.getRelationType().equals(IntegerRelationType.NE)
        ) {
            if (knownToBeUnequal) {
                return new Pair<Boolean, IntegerState>(true, this);
            }
        }
        return new Pair<Boolean, IntegerState>(false, this);
    }

    @Override
    public String toDOTString() {
        return "InequalityIntegerInterface: " + this.inequalitySets.toString();
    }

    @Override
    public Object toJSON() {
        JSONObject res = new JSONObject();
        res.put("type", this.getClass().getSimpleName());
        res.put("inequalities", JSONExportUtil.toJSON(this.inequalitySets));
        return res;
    }

//    @Override
//    public LLVMHeuristicVariable findReference(final FunctionalIntegerExpression expression) {
//        return null;
//    }

    @Override
    public IntegerRelationSet toRelationSet() {
        final IntegerRelationSet returnValue = new IntegerRelationSet();
        for (final Map.Entry<IntegerVariable, Set<IntegerVariable>> entry : this.inequalitySets.entrySet()) {
            for (final IntegerVariable inequalReference : entry.getValue()) {
                returnValue.add(new PlainIntegerRelation(IntegerRelationType.NE, entry.getKey(), inequalReference));
            }
        }
        return returnValue;
    }

    private void addInequalityMutate(final IntegerVariable varOne, final IntegerVariable varTwo) {
        this.assertExistenceAndGetInequalVars(varOne).add(varTwo);
        this.assertExistenceAndGetInequalVars(varTwo).add(varOne);
    }

    private Set<IntegerVariable> assertExistenceAndGetInequalVars(final IntegerVariable variable) {
        if (!this.inequalitySets.containsKey(variable)) {
            this.inequalitySets.put(variable, new HashSet<IntegerVariable>());
        }
        return this.inequalitySets.get(variable);
    }

    private Pair<IntegerVariable, IntegerVariable> getInequality(final IntegerRelation relation) {
        if (
            !(
                relation.getRelationType().equals(IntegerRelationType.LT)
                || relation.getRelationType().equals(IntegerRelationType.GT)
                || relation.getRelationType().equals(IntegerRelationType.NE)
            )
        ) {
            return null;
        }
        if (!(relation.getLhs() instanceof IntegerVariable)) {
            return null;
        }
        if (!(relation.getRhs() instanceof IntegerVariable)) {
            return null;
        }
        final IntegerVariable varOne = (IntegerVariable) relation.getLhs();
        final IntegerVariable varTwo = (IntegerVariable) relation.getRhs();
        return new Pair<>(varOne, varTwo);
    }

//    @Override
//    public Merger<IntegerState, LLVMHeuristicVariable> getMerger() {
//        return new Merger<IntegerState, LLVMHeuristicVariable>() {
//
//            @Override
//            public IntegerState merge(
//                final IntegerState lhsState,
//                final IntegerState rhsState,
//                final EquivalenceClassMapping<LLVMHeuristicVariable> equivalenceClassMapping)
//            {
//                if (!(lhsState instanceof InequalIntegerInterface)) {
//                    throw new IllegalArgumentException("lhsState must be of type InequalIntegerInterface");
//                }
//                if (!(rhsState instanceof InequalIntegerInterface)) {
//                    throw new IllegalArgumentException("rhsState must be of type InequalIntegerInterface");
//                }
//                return new InequalIntegerInterface();
//            }
//        };
//    }

}
