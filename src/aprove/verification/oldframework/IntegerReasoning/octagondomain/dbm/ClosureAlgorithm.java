package aprove.verification.oldframework.IntegerReasoning.octagondomain.dbm;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.IntegerReasoning.octagondomain.utils.*;

class ClosureAlgorithm {
    private final DifferenceBoundMatrix matrix;

    ClosureAlgorithm(final DifferenceBoundMatrix matrix) {
        this.matrix = matrix;
    }

    public boolean performClosure(final Set<DBMPosition> interestingPositions) {
        this.initializeDiagonals(interestingPositions);
        this.makeCoherent(interestingPositions);
        if (interestingPositions.isEmpty()) {
            return true;
        }
        this.performFloydWarshall(interestingPositions);
        if (!this.isQConsistent()) {
            return false;
        }
        this.tighten(interestingPositions);
        if (!this.isZConsistent()) {
            return false;
        }
        this.computeStrongCoherence(interestingPositions);
        return true;
    }

    /**
     * Makes sure that matrix[i;j] = matrix[-j;-i]. Does this by setting matrix[i;j]
     * to min(matrix[i;j], matrix[-j;-i])
     */
    private void makeCoherent(final Set<DBMPosition> interestingPositions) {
        for (final DBMPosition rowPosition : interestingPositions) {
            for (final DBMPosition colPosition : interestingPositions) {
                final DBMPosition negatedRowPos = rowPosition.getNegatedPosition();
                final DBMPosition negatedColPos = colPosition.getNegatedPosition();

                final BigInteger origEntry = this.matrix.getEntry(rowPosition, colPosition);
                final BigInteger corrEntry = this.matrix.getEntry(negatedColPos, negatedRowPos);

                if (origEntry == null && corrEntry == null) {
                    // Do nothing, both entries are +inf
                } else if (origEntry != null && corrEntry == null) {
                    this.matrix.setEntry(negatedColPos, negatedRowPos, origEntry);
                } else if (origEntry == null && corrEntry != null) {
                    this.matrix.setEntry(rowPosition, colPosition, corrEntry);
                } else {
                    final BigInteger min = origEntry.min(corrEntry);
                    this.matrix.setEntry(rowPosition, colPosition, min);
                    this.matrix.setEntry(negatedColPos, negatedRowPos, min);
                }
            }
        }

    }

    private void initializeDiagonals(final Set<DBMPosition> interestingPositions) {
        for (final DBMPosition currentVariable : interestingPositions) {
            this.matrix.setEntry(currentVariable, currentVariable, BigInteger.valueOf(0));
        }
    }

    private void performFloydWarshall(final Set<DBMPosition> interestingPositions) {
        for (final DBMPosition intermediate : interestingPositions) {
            this.performSingleFloydWarshallStep(intermediate, interestingPositions);
        }
    }

    private void performSingleFloydWarshallStep(
        final DBMPosition intermediate,
        final Set<DBMPosition> interestingPositions)
    {
        for (final DBMPosition source : interestingPositions) {
            for (final DBMPosition target : interestingPositions) {

                final BigInteger directCost = this.matrix.getEntry(source, target);

                final BigInteger sourceToIntermediateCost = this.matrix.getEntry(source, intermediate);
                final BigInteger intermediateToTargetCost = this.matrix.getEntry(intermediate, target);

                BigInteger viaIntermediateCost = null;
                if (sourceToIntermediateCost != null && intermediateToTargetCost != null) {
                    viaIntermediateCost = sourceToIntermediateCost.add(intermediateToTargetCost);
                }

                if (directCost == null && viaIntermediateCost != null) {
                    this.matrix.setEntry(source, target, viaIntermediateCost);
                } else if (directCost != null && viaIntermediateCost == null) {
                    this.matrix.setEntry(source, target, directCost);
                } else if (directCost != null && viaIntermediateCost != null) {
                    this.matrix.setEntry(source, target, directCost.min(viaIntermediateCost));
                }
            }
        }
    }

    private void tighten(final Set<DBMPosition> interestingPositions) {
        for (final DBMPosition currentPosition : interestingPositions) {

            final DBMPosition toggledPosition = currentPosition.getNegatedPosition();

            final BigInteger difference = this.matrix.getEntry(currentPosition, toggledPosition);
            if (difference != null) {
                // We want x - (-x) to be a multiple of 2 for all x. This command implements floor(x/2)*2.
                final BigInteger tightened = difference.divide(BigInteger.valueOf(2)).multiply(BigInteger.valueOf(2));
                this.matrix.setEntry(currentPosition, toggledPosition, tightened);
            }
        }
    }

    private void computeStrongCoherence(final Set<DBMPosition> interestingPositions) {
        for (final DBMPosition source : interestingPositions) {
            final DBMPosition negatedSource = source.getNegatedPosition();

            for (final DBMPosition target : interestingPositions) {
                final DBMPosition negatedTarget = target.getNegatedPosition();

                final BigInteger directDifference = this.matrix.getEntry(source, target);

                BigInteger sourceUpperBound = this.matrix.getEntry(source, negatedSource);
                if (sourceUpperBound != null) {
                    sourceUpperBound = sourceUpperBound.divide(BigInteger.valueOf(2));
                }

                BigInteger targetLowerBound = this.matrix.getEntry(negatedTarget, target);
                if (targetLowerBound != null) {
                    targetLowerBound = targetLowerBound.divide(BigInteger.valueOf(2));
                }

                BigInteger inferredDifference = null;
                if (sourceUpperBound != null && targetLowerBound != null) {
                    inferredDifference = sourceUpperBound.add(targetLowerBound);
                }

                if (directDifference == null && inferredDifference != null) {
                    this.matrix.setEntry(source, target, inferredDifference);
                } else if (directDifference != null && inferredDifference == null) {
                    this.matrix.setEntry(source, target, directDifference);
                } else if (directDifference != null && inferredDifference != null) {
                    this.matrix.setEntry(source, target, directDifference.min(inferredDifference));
                }
            }
        }
    }

    private boolean isQConsistent() {
        final Iterator<DBMPosition> positionIterator = this.matrix.getPositions().iterator();
        final Iterator<DBMPosition> evenPositionIterator = new SkipIterator<>(positionIterator);
        final Iterable<DBMPosition> evenPositions = new StandardIterable<>(evenPositionIterator);

        for (final DBMPosition position : evenPositions) {
            final BigInteger matrixEntry = this.matrix.getEntry(position, position);
            if (matrixEntry != null && matrixEntry.compareTo(BigInteger.ZERO) < 0) {
                return false;
            }
        }

        return true;
    }

    private boolean isZConsistent() {
        final Iterator<DBMPosition> positionIterator = this.matrix.getPositions().iterator();
        final Iterator<DBMPosition> evenPositionIterator = new SkipIterator<>(positionIterator);
        final Iterable<DBMPosition> evenPositions = new StandardIterable<>(evenPositionIterator);

        for (final DBMPosition position : evenPositions) {
            final DBMPosition negatedPosition = position.getNegatedPosition();
            final BigInteger originalEntry = this.matrix.getEntry(position, negatedPosition);
            final BigInteger negatedEntry = this.matrix.getEntry(negatedPosition, position);
            final boolean bothEntriesExist = originalEntry != null && negatedEntry != null;
            if (bothEntriesExist) {
                final BigInteger sum = originalEntry.add(negatedEntry);
                if (sum.compareTo(BigInteger.ZERO) < 0) {
                    return false;
                }
            }
        }

        return true;
    }
}
