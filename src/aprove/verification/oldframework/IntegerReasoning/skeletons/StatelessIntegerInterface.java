package aprove.verification.oldframework.IntegerReasoning.skeletons;

import org.json.*;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.IntegerReasoning.constants.*;
import aprove.verification.oldframework.IntegerReasoning.equalSides.*;

/**
 * Some inference strategies work without any knowledge other thatn the
 * relation to be checked, for example the {@link EqualSidesInterface} and the
 * {@link ConstantInterface}.
 *
 * The only interesting logic of these implementations is contained in the
 * checkRelation-method, all other methods are just stubs without any real
 * logic behind them. In order to reduce boilerplate code and clutter when
 * implementing such an interface, this abstract class implements all other
 * methods without any regard for internal state.
 *
 * @author Alexander Weinert
 */
public abstract class StatelessIntegerInterface implements IntegerState {

    @Override
    public IntegerState addRelation(final IntegerRelation relation, Abortion aborter) {
        return this;
    }

    @Override
    public IntegerState addRelationSet(final Iterable<? extends IntegerRelation> relations, Abortion aborter) {
        return this;
    }

//    @Override
//    public LLVMHeuristicVariable findReference(final LLVMHeuristicTerm expression) {
//        return null;
//    }

    @Override
    public String toDOTString() {
        return this.toString();
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
//                if (!(lhsState instanceof StatelessIntegerInterface)) {
//                    throw new IllegalArgumentException("lhsState must be a StatelessIntegerInterface");
//                }
//                if (!(rhsState instanceof StatelessIntegerInterface)) {
//                    throw new IllegalArgumentException("rhsState must be a StatelessIntegerInterface");
//                }
//                // Since we deal with stateless interfaces, it does not matter
//                // which one of lhsState or rhsState we return.
//                return lhsState;
//            }
//        };
//    }

    @Override
    public Object toJSON() {
        JSONObject res = new JSONObject();
        res.put("type", this.getClass().getSimpleName());
        return res;
    }

    @Override
    public IntegerRelationSet toRelationSet() {
        return new IntegerRelationSet();
    }

    @Override
    public String toString() {
        return this.getClass().getSimpleName() + ": Stateless";
    }

}
