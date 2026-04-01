package aprove.verification.oldframework.IntegerReasoning.constants;

import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.IntegerReasoning.skeletons.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Does not store any relations, but only decides relations on constants. This is a very weak decision procedure, but
 * very useful to have in one central place instead of having to use it in every other implementation of
 * {@link IntegerState}.
 * @author Alexander Weinert
 */
public class ConstantInterface extends StatelessIntegerInterface {

    /**
     * Used to delegate the decision whether a relation contains only constants and decide its truth-value if this is
     * the case.
     */
    final ConstantRelationAnalyzer analyzer = new ConstantRelationAnalyzer();

    @Override
    public Pair<Boolean, ? extends IntegerState> checkRelation(final IntegerRelation relation, Abortion aborter) {
        return new Pair<Boolean, IntegerState>(this.analyzer.decide(relation), this);
    }

}
