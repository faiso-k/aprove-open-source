package aprove.verification.probabilistic.Termination.ADPProblem.AST;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.probabilistic.BasicStructures.*;

/**
 * A class to encapsulate the information needed to apply the heuristics
 * when using DP transformation for AST of Narrowing, Rewriting, Instantiations, ...
 *
 * @see QTransformationInfo
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class ADP_AST_TransformationInfo {

    private final Map<Node<ProbabilisticRule>, Object[]> map; // the map from nodes to their info-array.
    // the last entry in the array is always the origin dt.
    // the previous entries are arbitrary information for the different transformations.

    private static final int NrOfTransformations = 5;
    private static final int SizeOfArray = ADP_AST_TransformationInfo.NrOfTransformations + 1; // +1 for the origin.

    private static final int ORIGIN_DUMMY = -1;
    private int origins = ADP_AST_TransformationInfo.ORIGIN_DUMMY; // the nr of original dts addressed in the map

    private static final int getIndex(final ADP_AST_Transformation transformation) {
        switch (transformation) {
            case Rewriting:
                return 1;
            case Instantiation:
                return 2;
            case ForwardInstantiation:
                return 3;
            case RuleOverlapInstantiation:
                return 4;
            default:
                break;
        }
        throw new RuntimeException("Unknown Transformation in AST_ADPTransformationInfo");
    }

    /**
     * copys an info array.
     * @param info - the array to copy
     * @return the copied array
     */
    private static Object[] getCopy(final Object[] info) {
        final Object[] res = new Object[ADP_AST_TransformationInfo.SizeOfArray];
        System.arraycopy(info, 0, res, 0, ADP_AST_TransformationInfo.SizeOfArray);
        return res;
    }

    /**
     * creates a transformation info from an initial set of DTs.
     * @param nodes - the initial set of DTs
     */
    public ADP_AST_TransformationInfo(final Set<Node<ProbabilisticRule>> nodes) {
        this.map = new LinkedHashMap<>(nodes.size());
        final Integer zero = 0;
        for (final Node<ProbabilisticRule> dp : nodes) {
            this.map.put(dp,
                new Object[] {
                    PositionTree.EMPTY_TREE, // narrowing
                    zero, // rewriting,
                    zero, // instantiation
                    zero, // forward instantiation
                    zero, // rule overlap instantiation
                    dp.getObject() });
        }
    }

    /**
     * creates a transformation info from a given one restricted to a subset of
     * the nodes in the given info.
     * @param subset - the subset of nodes
     * @param superInformation - the given transformation info
     */
    private ADP_AST_TransformationInfo(final Set<Node<ProbabilisticRule>> subset, final ADP_AST_TransformationInfo superInformation) {
        final int n = subset.size();
        this.map = new LinkedHashMap<>(n);
        for (final Node<ProbabilisticRule> dp : subset) {
            this.map.put(dp, superInformation.map.get(dp));
        }
    }

    /**
     * creates a transformation info from a given one, where the node origNode was
     * replaces by the newDPs using the transformation at the specified position.
     * @param transformation - used transformation
     * @param origNode - the node that got replaced
     * @param newDPs - the set of new DTs that replaced the origNode
     * @param p - the position
     * @param superInformation - original transformation info
     * @return
     */
    private ADP_AST_TransformationInfo(final ADP_AST_Transformation transformation,
        final Node<ProbabilisticRule> origNode,
        final Set<Node<ProbabilisticRule>> newDPs,
        final Position p,
        final ADP_AST_TransformationInfo superInformation) {
        this.map = new LinkedHashMap<>(superInformation.map);
        Object[] info = this.map.remove(origNode);
        info = ADP_AST_TransformationInfo.getCopy(info);
        final int index = ADP_AST_TransformationInfo.getIndex(transformation);

        Object o = info[index];

        Integer i = (Integer) o;
        i++;
        o = i;
        // end of special part

        info[index] = o;

        for (final Node<ProbabilisticRule> newDP : newDPs) {
            this.map.put(newDP, info);
        }
    }

    /**
     * creates a transformation info from this info, where the node oqigNode was
     * replaces by the newDPs using the transformation at the specified position.
     * Moreover, it returns the new counter for the transformed pairs. (0 if there
     * are no new pairs)
     * @param transformation - used transformation
     * @param origNode - the node that got replaced
     * @param newDPs - the set of new DTs that replaced the origNode
     * @param p - the position
     */
    public Pair<ADP_AST_TransformationInfo, Integer>
        getTransformedInfo(final ADP_AST_Transformation transformation,
            final Node<ProbabilisticRule> origNode,
            final Set<Node<ProbabilisticRule>> newDPs,
            final Position p) {
        final ADP_AST_TransformationInfo transInfo = new ADP_AST_TransformationInfo(transformation, origNode, newDPs, p, this);
        int limit;
        if (newDPs.isEmpty()) {
            limit = 0;
        } else {
            limit = transInfo.getCount(transformation, newDPs.iterator().next());
        }
        return new Pair<>(transInfo, limit);
    }

    /**
     * returns the info for a subset of the given nodes.
     * @param subset - the given subset of nodes
     * @return the info for the given subset
     */
    public ADP_AST_TransformationInfo getSubInfo(final Set<Node<ProbabilisticRule>> subset) {
        return new ADP_AST_TransformationInfo(subset, this);
    }

    /**
     * returns the nr of original dts addressed from this info.
     * @return the nr of original dts addressed from this info
     */
    public int getNrOfOrigins() {
        if (this.origins == ADP_AST_TransformationInfo.ORIGIN_DUMMY) {
            // if we have the dummy, then we must compute the result.
            final Set<ProbabilisticRule> origins = new HashSet<>(this.map.size());
            for (final Object[] elem : this.map.values()) {
                origins.add((ProbabilisticRule) elem[ADP_AST_TransformationInfo.NrOfTransformations]);
            }
            this.origins = origins.size();
        }
        return this.origins;
    }

    /**
     * returns the count stored for a specific transformation and a
     * specific node
     * @param transformation
     * @param node
     * @return the count stored for transformation and node
     */
    public int getCount(final ADP_AST_Transformation transformation, final Node<ProbabilisticRule> node) {
        final Object o = this.map.get(node)[ADP_AST_TransformationInfo.getIndex(transformation)];
        return ((Integer) o).intValue();
    }

    @Override
    public String toString() {
        final StringBuilder res = new StringBuilder("Transinfo:\n");
        for (final Map.Entry<Node<ProbabilisticRule>, Object[]> entry : this.map.entrySet()) {
            res.append("  ").append(entry.getKey().getObject()).append("  =>  ").append(Arrays.toString(entry.getValue())).append("\n");
        }
        return res.toString();
    }

    /**
     * a tree that is used to store a set of positions and
     * computes a value - the max nr of positions on a path
     * through the positions, seen as tree.
     * @author thiemann
     *
     */
    private final static class PositionTree {

        private final static Map<Integer, PositionTree> EMPTY_MAP = new HashMap<>(0);

        public final static PositionTree EMPTY_TREE = new PositionTree(0, 0, PositionTree.EMPTY_MAP);

        private final int value;
        private final int atTopPosition;
        private final Map<Integer, PositionTree> children;

        private PositionTree(final int value, final int atTopPosition, final Map<Integer, PositionTree> children) {
            this.value = value;
            this.atTopPosition = atTopPosition;
            this.children = children;
        }

        private PositionTree(final Iterator<Integer> p) {
            if (p.hasNext()) {
                this.value = 1;
                this.atTopPosition = 0;
                this.children = new HashMap<>(1);
                final Integer i = p.next();
                this.children.put(i, new PositionTree(p));
            } else {
                this.value = 1;
                this.atTopPosition = 1;
                this.children = PositionTree.EMPTY_MAP;
            }
        }

    }

}
