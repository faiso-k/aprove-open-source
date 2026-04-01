package aprove.verification.oldframework.Bytecode.Processors.ToSCC;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;

/**
 * Searches for possible marker fields used in a scc.
 *
 * @author Marc Brockschmidt
 */
public class MarkerFieldAnalysis extends SCCAnalysis {
    /**
     * The field relations which we believe to be markers and the corresponding
     * chosen variable names.
     */
    private final Map<FieldRelation, AbstractVariableReference> markerVarNames;

    /**
     * Contains all relations for which we had an increase at some point.
     */
    private final Set<FieldRelation> wasIncreased;

    /**
     * @param scc the SCC to be annotated
     */
    public MarkerFieldAnalysis(final JBCGraph scc) {
        /*
         * Find fields for which a certain relation needs to hold to stay in the
         * SCC (i.e., the relation is a requirement on all paths)
         */
        final Set<FieldRelation> markerFields = MarkerFieldAnalysis.findFieldRelations(scc);

        //Associate a reference name to each relation:
        this.markerVarNames =
                new LinkedHashMap<FieldRelation, AbstractVariableReference>();
        for (final FieldRelation fR : markerFields) {
            this.markerVarNames.put(
                    fR,
                    new AbstractVariableReference(
                            UIDGenerator.getIntUIDGenerator().next(),
                            OperandType.INTEGER));
        }
        this.wasIncreased = new LinkedHashSet<FieldRelation>();
    }

    /**
     * @return the map from field relations that are used as markers to their
     *  respective counters
     */
    public Map<FieldRelation, AbstractVariableReference> getMarkerVarNames() {
        return this.markerVarNames;
    }

    /**
     * @param scc some method graph
     * @return set of fields that are checked against a fixed value on all
     *  paths
     */
    public static Set<FieldRelation> findFieldRelations(
            final JBCGraph scc) {
        final Node someNode = scc.getNodes().iterator().next();

        // (1) Get all paths
        final Set<List<Edge>> paths =
            JBCGraph.getAllPathsBetween(someNode, someNode);

        /*
         * (2) Check for each path what fields are compared to what integers,
         *     then intersect:
         */
        Set<FieldRelation> checkedEverywhere = null;
        boolean isFirstPath = true;
        for (final List<Edge> path : paths) {
            final Set<FieldRelation> checkedOnThisPath =
                    MarkerFieldAnalysis.collectCheckedFieldsOnPath(path);
            if (isFirstPath) {
                checkedEverywhere = checkedOnThisPath;
                isFirstPath = false;
            } else {
                checkedEverywhere.retainAll(checkedOnThisPath);
            }
        }

        return checkedEverywhere;
    }

    /**
     * @param path some sequence of fields encoding a path
     * @return the comparisons of fields with values on this path
     */
    private static Set<FieldRelation> collectCheckedFieldsOnPath(final List<Edge> path) {
        final Set<FieldRelation> checkedOnThisPath =
            new LinkedHashSet<FieldRelation>();
        for (final Edge e : path) {
            final EdgeInformation l = e.getLabel();
            for (final VariableInformation vi : l) {
                if (vi instanceof JBCIntegerRelation) {
                    final JBCIntegerRelation ir = (JBCIntegerRelation) vi;
                    final HeapPositions heap =
                            new HeapPositions(e.getStart().getState(), true);
                    checkedOnThisPath.addAll(MarkerFieldAnalysis.getCheckedFieldsInRelation(heap, ir));
                }
            }
        }
        return checkedOnThisPath;
    }

    /**
     * @param heap the complete heap position object for this state
     * @param ir some integer relation applying to this state
     * @return the comparisons of fields with values encoded in <code>ir</code>
     */
    private static Set<FieldRelation> getCheckedFieldsInRelation(
            final HeapPositions heap, final JBCIntegerRelation ir) {
        final Set<FieldRelation> checkedInThisRelation =
            new LinkedHashSet<FieldRelation>();
        if (!ir.leftIntegerIsNoRef()) {
            final AbstractVariableReference leftIntRef = ir.getLeftIntRef();
            if (!heap.containsRef(leftIntRef)) {
                return checkedInThisRelation;
            }
            final Collection<StatePosition> leftIntRefPos =
                    heap.getPositionsForRef(leftIntRef);
            for (final StatePosition pos : leftIntRefPos) {
                if (pos instanceof InstanceFieldPosition) {
                    final FieldIdentifier containingField =
                            ((InstanceFieldPosition) pos).getFieldId();
                    final FieldRelation fR;

                    final IntegerRelationType relType = ir.getRelationType();
                    if (relType != IntegerRelationType.EQ && relType != IntegerRelationType.NE) {
                        continue;
                    }

                    if (ir.rightIntegerIsNoRef()) {
                        fR =
                            new FieldRelation(containingField, relType, AbstractVariableReference.create(
                                ir.getRightInt(), OperandType.INTEGER));
                    } else {
                        fR = new FieldRelation(containingField, relType, ir.getRightIntRef());
                    }
                    checkedInThisRelation.add(fR);
                }
            }
        }
        if (!ir.rightIntegerIsNoRef()) {
            final AbstractVariableReference rightIntRef = ir.getLeftIntRef();
            if (!heap.containsRef(rightIntRef)) {
                return checkedInThisRelation;
            }
            final Collection<StatePosition> rightIntRefPos =
                    heap.getPositionsForRef(rightIntRef);
            for (final StatePosition pos : rightIntRefPos) {
                if (pos instanceof InstanceFieldPosition) {
                    final FieldIdentifier containingField =
                            ((InstanceFieldPosition) pos).getFieldId();
                    final FieldRelation fR;

                    if (ir.leftIntegerIsNoRef()) {
                        fR =
                            new FieldRelation(containingField, ir.getRelationType().mirror(),
                                AbstractVariableReference.create(ir.getLeftInt(), OperandType.INTEGER));
                    } else {
                        fR = new FieldRelation(containingField, ir.getRelationType().mirror(), ir.getLeftIntRef());
                    }
                    checkedInThisRelation.add(fR);
                }
            }
        }
        return checkedInThisRelation;
    }

    /**
     * @param o export util
     * @return textual representation of the analysis
     */
    @Override
    public String export(final Export_Util o) {
        final StringBuilder sb = new StringBuilder();

        sb.append("Marker field analysis yielded the following relations that could be markers:").append(o.linebreak());
        final List<String> relInfo = new LinkedList<String>();
        for (final Entry<FieldRelation, AbstractVariableReference> e : this.markerVarNames.entrySet()) {
            relInfo.add(e.getKey().toString() + " (Introduced counter " + e.getValue() + ")");
        }
        sb.append(o.set(relInfo, Export_Util.ITEMIZE));

        return sb.toString();
    }

    /**
     * @param fRel some field relation that did not hold at one point
     */
    public void noteIncrease(final FieldRelation fRel) {
        this.wasIncreased.add(fRel);
    }

    /**
     * @param fRel some field relation
     * @return true if the counter was ever increased.
     */
    public boolean wasEverIncreased(final FieldRelation fRel) {
        return this.wasIncreased.contains(fRel);
    }
}
