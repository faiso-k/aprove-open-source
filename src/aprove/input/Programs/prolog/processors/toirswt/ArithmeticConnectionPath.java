package aprove.input.Programs.prolog.processors.toirswt;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.verification.oldframework.Utility.Graph.*;

class ArithmeticConnectionPath implements Iterable<Node<PrologAbstractState>> {

    /**
     * Models a fragment of an ArithmeticConnectionPath. These Paths are, by
     * definition, maximal. However, during construction of such a Path, it is
     * necessary to handle fragments, i.e., non-maximal prefixes of
     * ArithmeticConnectionPaths.
     *
     * In order to make handling of such fragments easier and more readable, we
     * use this Builder-class.
     *
     * @author Alexander Weinert
     */
    static class Builder {

        private final PrologEvaluationGraph graph;
        private final List<Node<PrologAbstractState>> pathFragment;

        /**
         * @param graph Some graph. Must not be null.
         * @param startingState The first state of the new fragment. Must not be null.
         * @return A fragment of a path in the given graph, containing only the given starting state
         */
        public static Builder create(PrologEvaluationGraph graph, Node<PrologAbstractState> startingState) {
            assert graph != null;
            assert startingState != null;

            final List<Node<PrologAbstractState>> fragment = Collections.singletonList(startingState);
            return new Builder(graph, fragment);
        }

        /**
         * The given fragment is not copied, but only stored by reference.
         * @param pathFragment The fragment to be stored in the Builder
         */
        private Builder(PrologEvaluationGraph graph, List<Node<PrologAbstractState>> pathFragment) {
            this.graph = graph;
            this.pathFragment = pathFragment;
        }

        /**
         * @return The last element of the current fragment
         */
        private Node<PrologAbstractState> getEndOfFragment() {
            return this.pathFragment.get(this.pathFragment.size() - 1);
        }

        /**
         * A fragment of an Arithmetic Connection Path can be extended if it is
         * neither a split node, nor a success node or an instance node.
         *
         * @param graph Some graph. Must not be null.
         * @return True if this path fragment can be extended. False otherwise.
         */
        public boolean canBeExtended() {
            final Node<PrologAbstractState> endOfFragment = this.getEndOfFragment();

            if(this.graph.getOut(endOfFragment).isEmpty()) {
                return false;
            }

            if(this.graph.isSplitNode(endOfFragment)) {
                return false;
            }

            if(this.graph.isParallelNode(endOfFragment)) {
                return false;
            }

            if(this.graph.isInstanceNode(endOfFragment)) {
                return false;
            }

            if(this.graph.isGeneralizationNode(endOfFragment)) {
                return false;
            }

            if(this.graph.isArithCompNode(endOfFragment)) {
                return false;
            }

            if(this.graph.isIsNode(endOfFragment)) {
                return false;
            }

            return true;
        }

        /**
         * @param graph Some graph. Must not be null.
         * @return All possible extensions of this fragment
         */
        public Collection<Builder> extend() {
            assert this.canBeExtended();

            final Collection<Builder> returnValue = new LinkedList<>();

            for(Node<PrologAbstractState> extension : this.graph.getOut(this.getEndOfFragment())) {
                final List<Node<PrologAbstractState>> extendedPathFragment = new LinkedList<>(this.pathFragment);
                extendedPathFragment.add(extension);
                returnValue.add(new Builder(this.graph, extendedPathFragment));
            }

            return returnValue;
        }

        public boolean canBeBuilt() {
            final Node<PrologAbstractState> endOfFragment = this.getEndOfFragment();

            if(this.graph.isSuccessNode(endOfFragment)) {
                return true;
            }

            if(this.graph.isSplitNode(endOfFragment)) {
                return true;
            }

            if(this.graph.isParallelNode(endOfFragment)) {
                return true;
            }

            if(this.graph.isInstanceNode(endOfFragment)) {
                return true;
            }

            if(this.graph.isGeneralizationNode(endOfFragment)) {
                return true;
            }

            if(this.graph.isArithCompNode(endOfFragment)) {
                return true;
            }

            if(this.graph.isIsNode(endOfFragment)) {
                return true;
            }

            return false;

        }

        public ArithmeticConnectionPath build() {
            assert this.canBeBuilt();
            return new ArithmeticConnectionPath(this.graph, this.pathFragment);
        }

        @Override
        public String toString() {
            final StringBuilder builder = new StringBuilder("[");
            final Iterator<Node<PrologAbstractState>> it = this.pathFragment.iterator();
            while(it.hasNext()) {
                builder.append(it.next().getNodeNumber());
                if(it.hasNext()) {
                    builder.append(",");
                }
            }
            builder.append("]");
            return builder.toString();
        }
    }

    final PrologEvaluationGraph graph;
    final List<Node<PrologAbstractState>> path;

    private ArithmeticConnectionPath(PrologEvaluationGraph graph, List<Node<PrologAbstractState>> path) {
        this.graph = graph;
        this.path = path;
    }

    /**
     * Does not return a copy of the first node, but a reference to it.
     * @return The first node of this path.
     */
    public Node<PrologAbstractState> getHead() {
        return this.path.get(0);
    }

    /**
     * Does not return a copy of the last node, but a reference to it.
     * @return The last node of this path. Is never null.
     */
    public Node<PrologAbstractState> getFinalNode() {
        return this.path.get(this.path.size() - 1);
    }

    /**
     * This method is used to pass an ArithmeticConnectionPath into legacy
     * methods that expect that paths are modeled as lists instead of their own
     * objects. In newer code, iteration over a path should take place using
     * this class itself, which implements Iterable<> for this purpose.
     *
     * @return A copy of the list of nodes this path models.
     */
    public List<Node<PrologAbstractState>> toList() {
        return new LinkedList<>(this.path);
    }

    @Override
    public Iterator<Node<PrologAbstractState>> iterator() {
        return this.path.iterator();
    }

    @Override
    public String toString() {
        final StringBuilder builder = new StringBuilder("[");
        final Iterator<Node<PrologAbstractState>> it = this.path.iterator();
        while(it.hasNext()) {
            builder.append(it.next().getNodeNumber());
            if(it.hasNext()) {
                builder.append(",");
            }
        }
        builder.append("]");
        return builder.toString();
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.graph == null) ? 0 : this.graph.hashCode());
        result = prime * result + ((this.path == null) ? 0 : this.path.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        ArithmeticConnectionPath other = (ArithmeticConnectionPath) obj;
        if (this.graph == null) {
            if (other.graph != null) {
                return false;
            }
        } else if (!this.graph.equals(other.graph)) {
            return false;
        }
        if (this.path == null) {
            if (other.path != null) {
                return false;
            }
        } else if (!this.path.equals(other.path)) {
            return false;
        }
        return true;
    }
}
