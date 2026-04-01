/**
 *
 */
package aprove.verification.complexity.AcdtProblem.Utils;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Holds a list of defined positions (of a base rule of a Cdt). Positions are in
 * lexicographic order. Dependencies of a position point to the index of the
 * next position above.
 */
public class TupleDefinedPositions implements Immutable, Iterable<TupleDefinedPositions.TupleDefinedPosition> {

    /**
     * Defined positions, in lexicographic order
     */
    private final ImmutableArrayList<Position> positions;

    /* Cached data */

    /**
     * Dependencies between positions.
     *
     * if i (and therefore positions[i]) is maximal with
     *    positions[i] < positions[j],
     * then dependencies[j] = i. If there is no such i
     * dependencies[j] = -1
     */
    private final ImmutableArrayList<Integer> dependencies;

    private final int hashcode;

    private TupleDefinedPositions(
            ImmutableArrayList<Position> positions,
            ImmutableArrayList<Integer> dependencies) {
        this.positions = positions;
        this.dependencies = dependencies;
        this.hashcode = this.computeHashCode();
    }

    public static TupleDefinedPositions createFromRule(
            Rule r, Set<FunctionSymbol> definedSymbols) {
        ArrayList<Pair<Position,Integer>> fdp = TupleDefinedPositions.findDefinedPositions(r.getRight(), definedSymbols);
        ArrayList<Position> positions = new ArrayList<Position>(fdp.size());
        ArrayList<Integer> dependencies = new ArrayList<Integer>(fdp.size());
        for (Pair<Position, Integer> pair : fdp) {
            positions.add(pair.x);
            dependencies.add(pair.y);
        }

        return new TupleDefinedPositions(
                ImmutableCreator.create(positions),
                ImmutableCreator.create(dependencies));
    }

    private static ArrayList<Pair<Position,Integer>> findDefinedPositions(TRSTerm t, Set<FunctionSymbol> definedSymbols) {
        Deque<Integer> posStack = new ArrayDeque<Integer>();
        return TupleDefinedPositions.findDefinedPositions(t, posStack, 0, -1, definedSymbols);
    }

    private static ArrayList<Pair<Position,Integer>> findDefinedPositions(TRSTerm t, Deque<Integer> posStack, int idx, int parentIdx, Set<FunctionSymbol> definedSymbols) {
        ArrayList<Pair<Position,Integer>> res = new ArrayList<Pair<Position,Integer>>();
        if (t.isVariable()) {
            return res;
        } else {
            TRSFunctionApplication fa = (TRSFunctionApplication)t;
            if (definedSymbols.contains(fa.getRootSymbol())) {
                res.add(new Pair<Position,Integer>(TupleDefinedPositions.posFromStack(posStack), parentIdx));
                parentIdx = idx;
            }
            final int arity = fa.getRootSymbol().getArity();
            for (int i=0; i < arity; i++) {
                int newIdx = idx + res.size();
                posStack.addFirst(i);
                res.addAll(TupleDefinedPositions.findDefinedPositions(fa.getArgument(i), posStack, newIdx, parentIdx, definedSymbols));
                posStack.removeFirst();
            }
            return res;
        }
    }

    private static Position posFromStack(Deque<Integer> posStack) {
        int[] posArray = new int[posStack.size()];
        Iterator<Integer> it = posStack.descendingIterator();
        int i=0;
        while(it.hasNext()) {
            posArray[i++] = it.next();
        }
        return Position.create(posArray);
    }

    /**
     * Removes the nodes with in removeIds.
     *
     * Nodes are numbered with a pre-order run.
     */
    public TupleDefinedPositions filter(BitSet removeIds) {
        int oldSize = this.positions.size();
        int newSize = this.positions.size()-removeIds.cardinality();
        ArrayList<Position> newPos = new ArrayList<Position>(newSize);
        ArrayList<Integer> newDeps = new ArrayList<Integer>(newSize);

        ArrayList<Integer> old2new = new ArrayList<Integer>(oldSize);
        for (int i=0; i < oldSize; i++) {
            if (removeIds.get(i)) {
                old2new.add(-2);
            } else {
                old2new.add(newPos.size());
                newPos.add(this.positions.get(i));
            }
        }

        /*
         * When removing a position, there might be another position depending on
         * it. So we must replace this dependency by a dependency on the parent.
         *
         * We take advantage of the fact that the positions are in lexicographic
         * and that the usual order on positions is a subset of the lexicographic
         * order: Dependencies point always to smaller indexes.
         */
        ArrayList<Integer> newDepsWithOldIdxs = new ArrayList<Integer>(oldSize);
        for (int i=0; i < oldSize; i++) {
            if (this.dependencies.get(i) == -1) {
                newDepsWithOldIdxs.add(-1);
            } else {
                int dep = this.dependencies.get(i);
                if (removeIds.get(dep)) {
                    dep = newDepsWithOldIdxs.get(dep);
                }
                newDepsWithOldIdxs.add(dep);
            }
        }

        for (int i=0; i < oldSize; i++) {
            if (removeIds.get(i)) {
                continue;
            }
            int newDep = newDepsWithOldIdxs.get(i);
            if (newDep == -1) {
                newDeps.add(newDep);
            } else {
                newDeps.add(old2new.get(newDep));
            }
        }

        return new TupleDefinedPositions(
                ImmutableCreator.create(newPos),
                ImmutableCreator.create(newDeps));
    }

    /**
     * @return a list of all maximal chains wrt the prefix order on positions
     *  (going from the smallest position in that order to the
     *  maximal/innermost position)
     */
    public List<List<Position>> getMaximalPrefixChains() {
        List<List<Position>> result = new ArrayList<>();
        List<Integer> maxPositionIndices = this.getMaximalPositionIndices();

        // from each maximal position, go all the way up through the dependencies
        for (int i : maxPositionIndices) {
            ArrayList<Position> chain = new ArrayList<>();
            chain.add(this.getPosition(i));
            while (this.getDependency(i) != -1) {
                i = this.getDependency(i);
                chain.add(this.getPosition(i));
            }
            Collections.reverse(chain); // max position goes last
            result.add(chain);
        }
        return result;
    }

    /**
     * @return the maximal positions (i.e., those positions that have no
     *  positions below them / that are not depended on by any position)
     */
    private List<Integer> getMaximalPositionIndices() {
        boolean[] hasPositionBelow = new boolean[this.size()];
        for (int d : this.dependencies) {
            if (d != -1) {
                hasPositionBelow[d] = true;
            }
        }
        List<Integer> result = new ArrayList<>();
        for (int i = 0; i < hasPositionBelow.length; ++i) {
            if (! hasPositionBelow[i]) {
                result.add(i);
            }
        }
        return result;
    }

    public Position getPosition(int i) {
        return this.positions.get(i);
    }

    public ImmutableArrayList<Position> getPositions() {
        return this.positions;
    }

    /**
     * Returns the index of the biggest position above positions[i].
     *
     * @return -1 if no such position exists.
     */
    public int getDependency(int i) {
        return this.dependencies.get(i);
    }

    public ImmutableArrayList<Integer> getDependencies() {
        return this.dependencies;
    }

    public boolean hasAncestor(int i) {
        return this.getDependency(i) != -1;
    }

    public int size() {
        return this.positions.size();
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append('[');
        final int size = this.positions.size();
        for (int i=0; i < size; i++) {
            if (i > 0) {
                sb.append("; ");
            }
            sb.append('<');
            sb.append(this.positions.get(i));
            sb.append('>');
        }
        sb.append("]@");
        sb.append(this.getDependencies());
        return sb.toString();
    }

    private int computeHashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result
                + ((this.positions == null) ? 0 : this.positions.hashCode());
        return result;
    }

    @Override
    public int hashCode() {
        return this.hashcode;
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
        TupleDefinedPositions other = (TupleDefinedPositions) obj;
        if (this.positions == null) {
            if (other.positions != null) {
                return false;
            }
        } else if (!this.positions.equals(other.positions)) {
            return false;
        }
        return true;
    }

    @Override
    public Iterator<TupleDefinedPosition> iterator() {
        return new TDPIterator(this);
    }

    public static class TupleDefinedPosition {
        public final Position position;
        public final int idx;

        public TupleDefinedPosition(Position pos, int idx) {
            this.position = pos;
            this.idx = idx;
        }
    }

    private static class TDPIterator implements Iterator<TupleDefinedPosition> {

        private final TupleDefinedPositions tdps;
        private int idx = 0;

        public TDPIterator(TupleDefinedPositions tdps) {
            this.tdps = tdps;
        }

        @Override
        public boolean hasNext() {
            return this.idx < this.tdps.size();
        }

        @Override
        public TupleDefinedPosition next() {
            TupleDefinedPosition tdp =
                new TupleDefinedPosition(this.tdps.getPosition(this.idx), this.idx);
            this.idx++;
            return tdp;
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }

    }

}