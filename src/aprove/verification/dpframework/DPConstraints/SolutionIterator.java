package aprove.verification.dpframework.DPConstraints;

public class SolutionIterator {
    public final Object id;

    public static enum Direction {
        right {
            @Override
            public Direction inverse() {
                return left;
            }
        },
        left {
            @Override
            public Direction inverse() {
                return right;
            }
        };

        public abstract Direction inverse();
    };

    public static SolutionIterator emptySolutionIterator = new SolutionIterator(null);

    public SolutionIterator(Object id) {
        this.id = id;
    }

    /**
     * @return true if this SolutionIterator is known to be empty
     */
    public boolean isEmpty() {
        return true;
    }

    /**
     * @return true iff an overflow occurs or this SolutionIterator is empty
     */
    public boolean next() {
        return true;
    }

    /**
     * @return true iff the given solution could be extended further (solution is valid)
     */
    public boolean extendWithCurrent(Solution sol) {
        sol.setNotValid();
        return false;
    }

    /*
     * a => b *sigma        dir = right
     * a <= b *sigma        dir = left
     */
    public static SolutionIterator create(
        Direction dir,
        Constraint a,
        Constraint b,
        SolutionConstraints solcons,
        Object id)
    {
        int i = SolutionIterator.getHash(a);
        int j = SolutionIterator.getHash(b);
        if (i == j) {
            switch (i) {
            case 1:
            case 2:
                return AtomSolutionIterator.create(dir, (TermAtom) a, (TermAtom) b, solcons, id);
            case 3:
                return ImplicationSolutionIterator.create(dir, (Implication) a, (Implication) b, solcons, id);
            case 4:
                return SetSolutionIterator.create(dir, (ConstraintSet) a, (ConstraintSet) b, solcons, id);
            default:
                throw new RuntimeException();
            }
        }
        if (i == 4 && j < 3) {
            return SetSolutionIterator.create(dir, (ConstraintSet) a, ConstraintSet.flatCreate(b), solcons, id);
        }
        if (i < 3 && j == 4) {
            return SetSolutionIterator.create(dir, ConstraintSet.flatCreate(a), (ConstraintSet) b, solcons, id);
        }
        return SolutionIterator.emptySolutionIterator;
    }

    private static int getHash(Constraint o) {
        if (o.isPredicate()) {
            return 1;
        }
        if (o.isReducesTo()) {
            return 2;
        }
        if (o.isImplication()) {
            return 3;
        }
        if (o.isConstraintSet()) {
            return 4;
        }
        if (o.isPolyAtom()) {
            return 5;
        }
        if (o.isUsableAtom()) {
            return 6;
        }
        return 0;
    }

    public static boolean isCandidateAA(Direction dir, TermAtom a, TermAtom b) {
        return b.getLeft().matches(a.getLeft()) && b.getRight().matches(a.getRight());
    }

    public static boolean isCandidateII(Direction dir, Implication a, Implication b) {
        return a.getQuantor().size() == b.getQuantor().size()
            && SolutionIterator.isCandidateCC(dir.inverse(), a.getConclusion(), b.getConclusion())
            && SolutionIterator.isCandidateSS(dir, a.getConditions(), b.getConditions());
    }

    public static boolean isCandidateSS(Direction dir, ConstraintSet a, ConstraintSet b) {
        if (dir == Direction.right) {
            if (b.isEmpty()) {
                return true;
            }
            if (a.isEmpty()) {
                return false;
            }
            if ((b.reducesToCount > 0) && !(a.reducesToCount > 0)) {
                return false;
            }
            if ((b.predicateCount > 0) && !(a.predicateCount > 0)) {
                return false;
            }
            if ((b.implicationCount > 0) && !(a.implicationCount > 0)) {
                return false;
            }
        } else {
            if (a.isEmpty()) {
                return true;
            }
            if (b.isEmpty()) {
                return false;
            }
            if ((a.reducesToCount > 0) && !(b.reducesToCount > 0)) {
                return false;
            }
            if ((a.predicateCount > 0) && !(b.predicateCount > 0)) {
                return false;
            }
            if ((a.implicationCount > 0) && !(b.implicationCount > 0)) {
                return false;
            }
        }
        return true;
    }

    /*
     * returns false if (a ==> b * sigma) does not hold
     * if it returns true (a ==> b * sigma) may hold for some sigma
     */
    public static boolean isCandidateCC(Direction dir, Constraint a, Constraint b) {
        int i = SolutionIterator.getHash(a);
        int j = SolutionIterator.getHash(b);
        if (i == j) {
            switch (i) {
            case 1:
            case 2:
                return SolutionIterator.isCandidateAA(dir, (TermAtom) a, (TermAtom) b);
            case 3:
                return SolutionIterator.isCandidateII(dir, (Implication) a, (Implication) b);
            case 4:
                return SolutionIterator.isCandidateSS(dir, (ConstraintSet) a, (ConstraintSet) b);
            case 5:
                return a.equals(b);
            case 6:
                return a.equals(b);
            default:
                throw new RuntimeException();
            }
        }
        if (i == 4 && j < 3) {
            return SolutionIterator.isCandidateSS(dir, (ConstraintSet) a, ConstraintSet.flatCreate(b));
        }
        if (i < 3 && j == 4) {
            return SolutionIterator.isCandidateSS(dir, ConstraintSet.flatCreate(a), (ConstraintSet) b);
        }
        return false;
    }

    public Object getId() {
        return this.id;
    }

}
