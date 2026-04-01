package aprove.verification.oldframework.IntegerReasoning;

import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.JSON.*;
import immutables.*;

/**
 * Abstracts decision procedures for sets of relations. For the big-picture-view
 * on this interface, refer to
 * http://aprove.informatik.rwth-aachen.de/devel/mediawiki/index.php/IntegerInterface.
 * @author Alexander Weinert, cryingshadow
 */
public interface IntegerState extends Immutable, JSONExport, DOTStringAble {

    /**
     * Note that depending on the implementation, not all information given by the relation may be stored. For example,
     * if the implementation only stores relations of the form x op y, then the relation x = y + 3 will only be stored
     * as y < x.
     * @param relation The relation to be added to the current integer state.
     * @param aborter For abortions.
     * @return A new integer state that contains as much of the given relation in addition to the already known
     *         relations as possible.
     * @throws InconsistentStateException If the new relation would lead to an inconsistent, i.e., unsatisfiable
     *         integer state.
     */
    IntegerState addRelation(IntegerRelation relation, Abortion aborter);

    /**
     * Adds a set of relations to this integer state. The same notes as for
     * {@link IntegerState#addRelation(LLVMRelation)} apply.
     * @param relations The set of relations to be added to the integer state.
     * @param aborter For abortions.
     * @return A new integer state that contains as much of all the given relations in addition to the already known
     *         relations as possible.
     * @throws InconsistentStateException If one of the new relations would lead to an inconsistent, i.e.,
     *                                    unsatisfiable integer state.
     */
    IntegerState addRelationSet(Iterable<? extends IntegerRelation> relations, Abortion aborter);

    /**
     * @return A representation of this integer state as a set (conjunction) of relations.
     */
    IntegerRelationSet toRelationSet();

    /**
     * Checks whether the current knowledge implies the given relation.
     * @param relation The relation to be checked for truth.
     * @param aborter For abortions.
     * @return A boolean flag and an integer state. The flag is true if the relation is known to hold given the current
     *         knowledge and false otherwise. The state is the current state possibly updated during the check.
     */
    Pair<Boolean, ? extends IntegerState> checkRelation(IntegerRelation relation, Abortion aborter);

}
