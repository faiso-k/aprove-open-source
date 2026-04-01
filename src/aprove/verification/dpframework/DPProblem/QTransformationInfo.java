package aprove.verification.dpframework.DPProblem;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * a class to encapsulate the information needed to apply the heuristics
 * when using DP transformation of Narrowing, Rewriting, ...
 * @author thiemann
 *
 */
public class QTransformationInfo {

    private final Map<Node<Rule>, Object[]> map; // the map from nodes to their info-array.
    // the last entry in the array is always the origin dp.
    // the previous entries are arbitrary information for the different transformations.

    private static final int NrOfTransformations = 4;
    private static final int SizeOfArray = QTransformationInfo.NrOfTransformations+1; // +1 for the origin.

    private static final int ORIGIN_DUMMY = -1;
    private int origins = QTransformationInfo.ORIGIN_DUMMY; // the nr of original dps addressed in the map


    private static final int getIndex(QDPTransformation transformation) {
        switch(transformation) {
        case Narrowing:
            return 0;
        case Rewriting:
            return 1;
        case Instantiation:
            return 2;
        case ForwardInstantiation:
            return 3;
        }
        throw new RuntimeException("Unknown Transformation in QTransformationInfo");
    }

    /**
     * copys an info array.
     * @param info
     * @return
     */
    private static Object[] getCopy(Object[] info) {
        Object[] res = new Object[QTransformationInfo.SizeOfArray];
        System.arraycopy(info, 0, res, 0, QTransformationInfo.SizeOfArray);
        return res;
    }

    /**
     * creates a transformation info from an initial set of DPs.
     * @param initialDPs
     */
    public QTransformationInfo(Set<Node<Rule>> initialDPs) {
        this.map = new LinkedHashMap<Node<Rule>, Object[]>(initialDPs.size());
        Integer zero = 0;
        for (Node<Rule> dp : initialDPs) {
            this.map.put(dp, new Object[]{
                    PositionTree.EMPTY_TREE, // narrowing
                    zero, // rewriting,
                    zero, // instantiation
                    zero, // forward instantiation
                    dp.getObject()});
        }
    }

    /**
     * creates a transformation info from a given one, by restricted to a subset of
     * the nodes in the given info.
     * @param subset
     * @param superInformation
     */
    private QTransformationInfo(Set<Node<Rule>> subset, QTransformationInfo superInformation) {
        int n = subset.size();
        this.map = new LinkedHashMap<Node<Rule>, Object[]>(n);
        for (Node<Rule> dp : subset) {
            this.map.put(dp, superInformation.map.get(dp));
        }
    }


    /**
     * creates a transformation info from a given one, where the node s_to_t was
     * replaces by the newDPs using the transformation at the specified position.
     * @param transformation
     * @param s_to_t
     * @param newDPs
     * @param p the position
     * @param superInformation
     */
    private QTransformationInfo(QDPTransformation transformation, Node<Rule> s_to_t, Set<Node<Rule>> newDPs, Position p, QTransformationInfo superInformation) {
        this.map = new LinkedHashMap<Node<Rule>, Object[]>(superInformation.map);
        Object[] info = this.map.remove(s_to_t);
        info = QTransformationInfo.getCopy(info);
        int index = QTransformationInfo.getIndex(transformation);

        Object o  = info[index];

        // this code has to be specified for each transformation
        if (transformation == QDPTransformation.Narrowing) {
            PositionTree narrowInfo = (PositionTree) o;
            o = narrowInfo.addPosition(p);

        } else {
            Integer i = (Integer) o;
            i++;
            o = i;
        }
        // end of special part

        info[index] = o;

        for (Node<Rule> newDP : newDPs) {
            this.map.put(newDP, info);
        }
    }


    /**
     * creates a transformation info from this info, where the node s_to_t was
     * replaces by the newDPs using the transformation at the specified position.
     * Moreover, it returns the new counter for the transformed pairs. (0 if there
     * are no new pairs)
     * @param transformation
     * @param s_to_t
     * @param newDPs
     * @param p the position
     */
    public Pair<QTransformationInfo, Integer> getTransformedInfo(QDPTransformation transformation, Node<Rule> s_to_t, Set<Node<Rule>> newDPs, Position p) {
        QTransformationInfo transInfo = new QTransformationInfo(transformation, s_to_t, newDPs, p, this);
        int limit;
        if (newDPs.isEmpty()) {
            limit = 0;
        } else {
            limit = transInfo.getCount(transformation, newDPs.iterator().next());
        }
        return new Pair<QTransformationInfo, Integer>(transInfo, limit);
    }

    /**
     * returns the info for a subset of the given nodes.
     * @param subset
     * @return
     */
    public QTransformationInfo getSubInfo(Set<Node<Rule>> subset) {
        return new QTransformationInfo(subset, this);
    }

    /**
     * returns the nr of original dps addressed from this info.
     * @return
     */
    public int getNrOfOrigins() {
        if (this.origins == QTransformationInfo.ORIGIN_DUMMY) {
            // if we have the dummy, then we must compute the result.
            Set<Rule> origins = new HashSet<Rule>(this.map.size());
            for (Object[] elem : this.map.values()) {
                origins.add((Rule) elem[QTransformationInfo.NrOfTransformations]);
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
     * @return
     */
    public int getCount(QDPTransformation transformation, Node<Rule> node) {
        Object o = this.map.get(node)[QTransformationInfo.getIndex(transformation)];
        if (transformation == QDPTransformation.Narrowing) {
            return ((PositionTree)o).getValue();
        } else {
            return ((Integer) o).intValue();
        }
    }

    @Override
    public String toString() {
        String res = "Transinfo:\n";
        for (Map.Entry<Node<Rule>, Object[]> entry : this.map.entrySet()) {
            res += "  "+entry.getKey().getObject() + "  =>  " + Arrays.toString(entry.getValue()) + "\n";
        }
        return res;
    }


    /**
     * a tree that is used to store a set of positions and
     * computes a value - the max nr of positions on a path
     * through the positions, seen as tree.
     * @author thiemann
     *
     */
    private final static class PositionTree {

        private final static Map<Integer,PositionTree> EMPTY_MAP = new HashMap<Integer,PositionTree>(0);

        public final static PositionTree EMPTY_TREE = new PositionTree(0, 0, PositionTree.EMPTY_MAP);

        private final int value;
        private final int atTopPosition;
        private final Map<Integer, PositionTree> children;

        private PositionTree(int value, int atTopPosition, Map<Integer, PositionTree> children) {
            this.value = value;
            this.atTopPosition = atTopPosition;
            this.children = children;
        }

        private PositionTree(Iterator<Integer> p) {
            if (p.hasNext()) {
                this.value = 1;
                this.atTopPosition = 0;
                this.children = new HashMap<Integer,PositionTree>(1);
                Integer i = p.next();
                this.children.put(i, new PositionTree(p));
            } else {
                this.value = 1;
                this.atTopPosition = 1;
                this.children = PositionTree.EMPTY_MAP;
            }
        }

        public int getValue() {
            return this.value;
        }

        public PositionTree addPosition(Position p) {
            return this.addPos(p.iterator());
        }

        private PositionTree addPos(Iterator<Integer> p) {
            if (p.hasNext()) {
                int firstPos = p.next();
                PositionTree child = this.children.get(Integer.valueOf(firstPos));
                if (child == null) {
                    child = new PositionTree(p);
                } else {
                    child = child.addPos(p);
                }
                int childrenCount = this.value - this.atTopPosition;
                if (child.value > childrenCount) {
                    childrenCount = child.value;
                }
                Map<Integer, PositionTree> newChildren = new HashMap<Integer, PositionTree>(this.children);
                newChildren.put(firstPos, child);
                return new PositionTree(this.atTopPosition + childrenCount, this.atTopPosition, newChildren);
            } else {
                return new PositionTree(this.value+1, this.atTopPosition+1, this.children);
            }
        }

    }

}
