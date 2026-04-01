package aprove.verification.oldframework.IntegerReasoning.octagondomain.dbm;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Represents a Difference Bound Matrix (or DBM for short) that is always
 * strictly closed. One thing to note about this DBM is that every variable
 * exists in a positive and a negated form. This extends the set of contraints
 * that can be represented by the DBM.
 *
 * More information on DBM can be found in [OCT01], section III and [DBM01].
 * The definition of strongly closed can be found in [OCT01], section V.
 * The algorithm for tight integer closure is presented in [INT07], figure
 * 2
 *
 * [OCT01] The octagon abstract domain. Antoine Miné. In Proc. of the Workshop
 * on Analysis, Slicing, and Transformation
 * http://www.di.ens.fr/~mine/publi/article-mine-ast01.pdf
 *
 * [DBM01] A new numerical abstract domain based on difference-bound matrices.
 * Antoine Miné. In Proc. of the Second Symposium on Programs as Data Objects
 * (PADO II), volume 2053 of Lecture Notes in Computer Science (LNCS), 155-172
 * http://www.di.ens.fr/~mine/publi/article-mine-padoII.pdf
 *
 * [INT07] An Improved Tight Closure Algorithm for Integer Octagonal Constraints.
 * Roberto Bagnara, Patricia M. Hill, Enea Zaffanella, http://arxiv.org/abs/0705.4618
 *
 * @author Alexander Weinert
 */
public class DifferenceBoundMatrix {
    private final Map<IntegerVariable, Pair<DBMPosition, DBMPosition>> positionMap;
    private final List<DBMPosition> knownPositions;
    private final List<List<BigInteger>> entryMap;
    private final Map<Integer, Set<Integer>> sccs;
    private final Set<Integer> locallyClosed;

    /**
     * Creates a new, empty DBM
     */
    public DifferenceBoundMatrix() {
        this.positionMap = new HashMap<>();
        this.entryMap = new ArrayList<>();
        this.knownPositions = new ArrayList<>();
        this.sccs = new HashMap<>();
        this.locallyClosed = new HashSet<>();
    }

    /**
     * Creates a copy of the given DBM
     * @param other Some other DBM
     */
    public DifferenceBoundMatrix(final DifferenceBoundMatrix other) {
        this.positionMap = new HashMap<>(other.positionMap);
        this.entryMap = new ArrayList<>(other.entryMap);
        this.knownPositions = new ArrayList<>(other.knownPositions);
        this.sccs = new HashMap<>(other.sccs);
        this.locallyClosed = new HashSet<>();
    }

    /**
     * @param variable Some variable reference
     * @return The position that the given variable is stored at in the DBM in
     * its positive form. If this variable was not stored previously, a
     * position is created for it. Never null.
     */
    public DBMPosition getVariablePosition(final IntegerVariable variable) {
        final Pair<DBMPosition, DBMPosition> referenceNumber = this.assertAndGetPosition(variable);
        return referenceNumber.x;
    }

    /**
     * @param variable Some variable reference
     * @return The position that the given variable is stored at in the DBM in
     * its negative form. If this variable was not stored previously, a
     * position is created for it. Never null.
     */
    public DBMPosition getNegativeVariablePosition(final IntegerVariable variable) {
        final Pair<DBMPosition, DBMPosition> referenceNumber = this.assertAndGetPosition(variable);
        return referenceNumber.y;
    }

    /**
     * @param reference Some variable reference
     * @return The locations of the positive and negative forms of the given
     * variable. If these did not exist before, they are created.
     */
    private Pair<DBMPosition, DBMPosition> assertAndGetPosition(final IntegerVariable reference) {
        if (!this.positionMap.containsKey(reference)) {

            final DBMPosition positiveVariablePosition =
                DBMPosition.createPosition(reference, this.knownPositions.size());
            this.knownPositions.add(positiveVariablePosition);

            final DBMPosition negativeVariablePosition =
                DBMPosition.createNegatedPosition(reference, this.knownPositions.size());
            this.knownPositions.add(negativeVariablePosition);

            final Set<Integer> newScc = new HashSet<>();
            newScc.add(positiveVariablePosition.getListIndex());
            newScc.add(negativeVariablePosition.getListIndex());
            this.sccs.put(positiveVariablePosition.getListIndex(), newScc);
            this.sccs.put(negativeVariablePosition.getListIndex(), newScc);

            this.positionMap.put(reference, new Pair<>(positiveVariablePosition, negativeVariablePosition));

            for (final List<BigInteger> list : this.entryMap) {
                list.add(null);
                list.add(null);
            }

            final List<BigInteger> positiveNewList = new ArrayList<>();
            positiveNewList.addAll(Collections.nCopies(this.knownPositions.size(), (BigInteger) null));
            positiveNewList.set(positiveNewList.size() - 2, BigInteger.ZERO);
            this.entryMap.add(positiveNewList);

            final List<BigInteger> negativeNewList = new ArrayList<>();
            negativeNewList.addAll(Collections.nCopies(this.knownPositions.size(), (BigInteger) null));
            negativeNewList.set(negativeNewList.size() - 1, BigInteger.ZERO);
            this.entryMap.add(negativeNewList);
        }

        return this.positionMap.get(reference);
    }

    /**
     * We do not provide a method setLowerBound. Instead, use a negative variable
     * reference with this method to set a lowerBound
     * @param variableRef Some variable reference
     * @param upperBound The upper bound for the given variable. Must not be null.
     */
    public void tightenUpperBound(final DBMPosition variableRef, final BigInteger upperBound) {
        final DBMPosition negatedVariableRef = variableRef.getNegatedPosition();
        this.tightenDifferenceUpperBound(variableRef, negatedVariableRef, upperBound.multiply(BigInteger.valueOf(2)));
    }

    /**
     * @param variableRef Some variable reference
     * @return The upper bound for the given variable. May be null if no upper
     * bound is known
     */
    public BigInteger getUpperBound(final DBMPosition variableRef) {
        final DBMPosition negatedVariableRef = variableRef.getNegatedPosition();
        final BigInteger savedValue = this.getDifferenceUpperBound(variableRef, negatedVariableRef);

        if (savedValue != null) {
            return savedValue.divide(BigInteger.valueOf(2));
        } else {
            return null;
        }
    }

    /**
     * @param lhsVariablePos Some variable reference
     * @param rhsVariablePos Some variable reference
     * @param difference The upper bound for the result of
     * variableRefOne - variableRefTwo. Must not be null
     */
    public void tightenDifferenceUpperBound(
        final DBMPosition lhsVariablePos,
        final DBMPosition rhsVariablePos,
        final BigInteger difference)
    {
        final BigInteger knownValue = this.getEntry(lhsVariablePos, rhsVariablePos);
        if (knownValue != null) {
            if (knownValue.compareTo(difference) > 0) {
                this.setEntry(lhsVariablePos, rhsVariablePos, difference);
                this.locallyClosed.removeAll(this.sccs.get(lhsVariablePos.getListIndex()));
                this.locallyClosed.removeAll(this.sccs.get(rhsVariablePos.getListIndex()));
            } else {
                // We already know of a stricter bound
            }
        } else {
            // We do not have any bound so far
            this.setEntry(lhsVariablePos, rhsVariablePos, difference);
            this.locallyClosed.removeAll(this.sccs.get(lhsVariablePos.getListIndex()));
            this.locallyClosed.removeAll(this.sccs.get(rhsVariablePos.getListIndex()));
        }

    }

    /**
     * @param lhsVariablePos Some variable reference
     * @param rhsVariablePos Some variable reference
     * @return The upper bound for the result of
     *  (variableRefOne - variableRefTwo). May be null is no upper bound is known
     */
    public BigInteger getDifferenceUpperBound(final DBMPosition lhsVariablePos, final DBMPosition rhsVariablePos) {
        return this.getEntry(lhsVariablePos, rhsVariablePos);
    }

    /**
     * If this DBM is consistent, it is modified to be tightly closed around the
     * two given positions and true is returned. If this DBM is inconsistent,
     * false is returned and no guarantee about the state of the DBM is made.
     *
     * The notion of "tightly closed around two positions" means that tight closure
     * is only guaranteed for nodes that are at least in the SCC of one of the given nodes,
     * where the DBM is interpreted as an undirected graph.
     *
     * We use the algorithm shown in figure 2, [INT07] for this.
     *
     * @return True if the DBM is consistent, false otherwise
     */
    public boolean ensureClosure(final DBMPosition lhsPos, final DBMPosition rhsPos) {
        final Set<DBMPosition> interestingPositions = new HashSet<>();
        if (!this.locallyClosed.contains(lhsPos.getListIndex())) {
            for (final Integer lhsSccListIndex : this.sccs.get(lhsPos.getListIndex())) {
                interestingPositions.add(this.knownPositions.get(lhsSccListIndex));
            }
        }
        if (!this.locallyClosed.contains(rhsPos.getListIndex())) {
            for (final Integer rhsSccListIndex : this.sccs.get(rhsPos.getListIndex())) {
                interestingPositions.add(this.knownPositions.get(rhsSccListIndex));
            }
        }
        return new ClosureAlgorithm(this).performClosure(interestingPositions);
    }

    public boolean ensureClosure() {
        if (!this.locallyClosed.containsAll(this.knownPositions)) {
            final Set<DBMPosition> notLocallyClosed = new HashSet<>();
            for (final DBMPosition pos : this.knownPositions) {
                if (!this.locallyClosed.contains(pos.getListIndex())) {
                    notLocallyClosed.add(pos);
                    this.locallyClosed.add(pos.getListIndex());
                }
            }
            return new ClosureAlgorithm(this).performClosure(notLocallyClosed);
        } else {
            return true;
        }
    }

    BigInteger getEntry(final DBMPosition lhsOperand, final DBMPosition rhsOperand) {
        return this.entryMap.get(lhsOperand.getListIndex()).get(rhsOperand.getListIndex());
    }

    void setEntry(final DBMPosition lhsOperand, final DBMPosition rhsOperand, final BigInteger value) {
        this.entryMap.get(lhsOperand.getListIndex()).set(rhsOperand.getListIndex(), value);
        this.sccs.get(lhsOperand.getListIndex()).add(rhsOperand.getListIndex());
        this.sccs.get(rhsOperand.getListIndex()).add(lhsOperand.getListIndex());
    }

    /**
     * @return A sorted list of all positions in this DBM
     */
    public Iterable<DBMPosition> getPositions() {
        return this.knownPositions;
    }

    public IntegerRelationSet toRelationSet() {
        final IntegerRelationSet returnValue = new IntegerRelationSet();
        for (int i = 0; i < this.knownPositions.size(); ++i) {
            for (int j = 0; j < this.knownPositions.size(); ++j) {
                final BigInteger bound = this.entryMap.get(i).get(j);
                if (bound == null) {
                    continue;
                }
                final FunctionalIntegerExpression minuend = this.knownPositions.get(i).toIntegerExpression();
                final FunctionalIntegerExpression subtrahend = this.knownPositions.get(j).toIntegerExpression();
                final PlainIntegerOperation boundedExpression =
                    new PlainIntegerOperation(ArithmeticOperationType.SUB, minuend, subtrahend);
                final PlainIntegerConstant upperBound = new PlainIntegerConstant(bound);
                returnValue.add(new PlainIntegerRelation(IntegerRelationType.LE, boundedExpression, upperBound));
            }
        }
        return new IntegerRelationSet(returnValue);
    }

    @Override
    public String toString() {
        final StringBuilder stringBuilder = new StringBuilder();

        final Iterable<DBMPosition> positions = this.getPositions();

        final Iterator<DBMPosition> rowIterator = positions.iterator();
        while (rowIterator.hasNext()) {
            final DBMPosition rowPosition = rowIterator.next();
            final Iterator<DBMPosition> columnIterator = positions.iterator();

            while (columnIterator.hasNext()) {
                final DBMPosition columnPosition = columnIterator.next();
                stringBuilder.append(this.getEntry(rowPosition, columnPosition));
                if (columnIterator.hasNext()) {
                    stringBuilder.append(", ");
                }
            }
            if (rowIterator.hasNext()) {
                stringBuilder.append('\n');
            }
        }
        return stringBuilder.toString();
    }

    public Iterable<IntegerVariable> getVariables() {
        return new LinkedList<>(this.positionMap.keySet());
    }
}
