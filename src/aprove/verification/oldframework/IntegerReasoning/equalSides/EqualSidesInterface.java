package aprove.verification.oldframework.IntegerReasoning.equalSides;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.IntegerReasoning.skeletons.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Stateless IntegerInterface that only checks if the lhs and rhs of a given
 * relation are equal and returns the correct result in that case.
 * @author Alexander Weinert
 */
public class EqualSidesInterface extends StatelessIntegerInterface {

    @Override
    public Pair<Boolean, ? extends IntegerState> checkRelation(final IntegerRelation relation, Abortion aborter) {
        if (!relation.getLhs().equals(relation.getRhs())) {
            return new Pair<Boolean, IntegerState>(false, this);
        }
        switch (relation.getRelationType()) {
            case EQ:
            case LE:
            case GE:
                return new Pair<Boolean, IntegerState>(true, this);
            case LT:
            case GT:
            case NE:
                return new Pair<Boolean, IntegerState>(false, this);
            default:
                throw new IllegalStateException("Someone found a new way to relate integers");
        }
    }

}
