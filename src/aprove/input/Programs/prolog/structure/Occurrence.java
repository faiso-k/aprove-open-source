package aprove.input.Programs.prolog.structure;

import java.util.*;

import immutables.*;

/**
 * An Occurrence object models a position in a PrologTerm.<br><br>
 *
 * Created: Apr 12, 2007<br>
 * Last modified: Apr 12, 2007
 *
 * @author cryingshadow
 * @version $Id$
 */
public class Occurrence implements Iterable<Integer>, Immutable {

    /**
     * Indicates that the first Occurrence is bigger than the second,
     * i.e. the second Occurrence can be expanded to the first by
     * adding more positions.
     *
     */
    public static final int BIGGER = 2;

    /**
     * Indicates that two Occurrences are equal.
     */
    public static final int EQUAL = 0;

    /**
     * Indicates that the first Occurrence is smaller than the second,
     * i.e. the first Occurrence can be expanded to the second by
     * adding more positions.
     *
     */
    public static final int SMALLER = 1;

    /**
     * Indicates that two Occurrences are uncomparable, i.e. neither
     * can the first be expanded to the second by adding more
     * positions, nor can the second be expanded to the first
     * likewise.
     */
    public static final int UNCOMPARABLE = 3;

    /**
     * The list of Integers representing the Occurrence.
     */
    private final ImmutableList<Integer> occ;

    /**
     * Creates the epsilon position.
     */
    public Occurrence() {
        this.occ = ImmutableCreator.create(new ArrayList<Integer>());
    }

    /**
     * Constructs an Occurrence object from the specified list of Integers.
     * @param occParam The list representing the position.
     */
    public Occurrence(final Collection<Integer> occParam) {
        for (final Integer i : occParam) {
            if (i < 0) {
                throw new NumberFormatException("A (part of a) position cannot be negative!");
            }
        }
        this.occ = ImmutableCreator.create(new ArrayList<Integer>(occParam));
    }

    /**
     * Constructs an Occurrence object from the specified String.
     * @param occParam The String representing the position.
     */
    public Occurrence(final String occParam) {
        this.occ = ImmutableCreator.create(Occurrence.parseString(occParam));
    }

    /**
     * Computes a set of Occurrences of subterm in term.
     * @param term The term containing the positions.
     * @param subterm The subterm to find.
     * @return A set of Occurrences of subterm in term.
     */
    public static Set<Occurrence> getOccurrences(final PrologTerm term, final PrologTerm subterm) {
        return Occurrence.findOcc(term, subterm, new ArrayList<Integer>());
    }

    /**
     * Deletes all Occurrences in the specified set where there is a
     * bigger Occurrence in the set as well.
     * @param set The set to reduce.
     */
    public static void reduceToBiggest(final Set<Occurrence> set) {
        Occurrence.reduce(set, false);
    }

    /**
     * Deletes all Occurrences in the specified set where there is a
     * smaller Occurrence in the set as well.
     * @param set The set to reduce.
     */
    public static void reduceToSmallest(final Set<Occurrence> set) {
        Occurrence.reduce(set, true);
    }

    //    public Occurrence deepCopy() {
    //        Occurrence res = new Occurrence();
    //        for (Integer i : this.occ) {
    //            res.occ.add(Integer.valueOf(i));
    //        }
    //        return res;
    //    }

    /**
     * Computes a set of Occurrences of subterm in term where occ is the path from the root symbol to the current
     * position.
     * @param term The term containing the positions.
     * @param subterm The subterm to find.
     * @param occ The path from the root of term to the current position.
     * @return A set of Occurrences of subterm in term.
     */
    private static
        Set<Occurrence>
        findOcc(final PrologTerm term, final PrologTerm subterm, final ArrayList<Integer> occ)
    {
        final Set<Occurrence> res = new LinkedHashSet<Occurrence>();
        if (term.equals(subterm)) {
            res.add(new Occurrence(occ));
        } else {
            for (int i = 0; i < term.getArity(); i++) {
                final ArrayList<Integer> newOcc = new ArrayList<Integer>(occ);
                newOcc.add(i);
                res.addAll(Occurrence.findOcc(term.getArgument(i), subterm, newOcc));
            }
        }
        return res;
    }

    /**
     * Parses a String representation of a position into a list of Integers.
     * @param occ The String representation of the position.
     * @return A list of Integers representating the same position.
     */
    private static ArrayList<Integer> parseString(final String occ) {
        final ArrayList<Integer> res = new ArrayList<Integer>();
        final String[] nums = occ.split(",");
        for (final String num : nums) {
            res.add(Integer.parseInt(num));
        }
        for (final Integer i : res) {
            if (i < 0) {
                throw new NumberFormatException("A (part of a) position cannot be negative!");
            }
        }
        return res;
    }

    /**
     * Deletes all Occurrences in the specified set where there is a
     * bigger or smaller (indicated by the flag) Occurrence in the set as well.
     * @param set The set to reduce.
     * @param toSmallest The flag whether to reduce to smallest or biggest Occurrences.
     */
    private static void reduce(final Set<Occurrence> set, final boolean toSmallest) {
        final Set<Occurrence> toDel = new LinkedHashSet<Occurrence>();
        final Queue<Occurrence> queue = new ArrayDeque<Occurrence>(set);
        while (!queue.isEmpty()) {
            final Occurrence occ1 = queue.poll();
            final Set<Occurrence> rest = new LinkedHashSet<Occurrence>(queue);
            for (final Occurrence occ2 : rest) {
                final int c = occ1.compareTo(occ2);
                switch (c) {
                case EQUAL:
                case UNCOMPARABLE:
                    break;
                case SMALLER:
                    toDel.add(toSmallest ? occ2 : occ1);
                    break;
                case BIGGER:
                    toDel.add(toSmallest ? occ1 : occ2);
                    break;
                default:
                    // should not be reachable
                    throw new IllegalStateException("Unexpected value occurred!");
                }
            }
        }
        set.removeAll(toDel);
    }

    /**
     * Creates a new Occurrence by adding the specified child number in front of the current Occurrence.
     * @param i The child number to add.
     * @return A new Occurrence emerging from the current one by adding the specified child number in front of it.
     */
    public Occurrence addChildNumberInFront(final Integer i) {
        if (i < 0) {
            throw new NumberFormatException();
        }
        final List<Integer> newList = new ArrayList<Integer>(this.occ);
        newList.add(0, i);
        return new Occurrence(newList);
    }

    /**
     * Creates a new Occurrence by appending the specified child number.
     * @param i The child number to append.
     * @return A new Occurrence emerging from the current one by appending the specified child number.
     */
    public Occurrence appendChildNumber(final Integer i) {
        if (i < 0) {
            throw new NumberFormatException();
        }
        final List<Integer> newList = new ArrayList<Integer>(this.occ);
        newList.add(i);
        return new Occurrence(newList);
    }

    /**
     * Compares the specified Occurrence to the current one.
     * @param otherOcc The Occurrence for comparison.
     * @return The corresponding constant SMALLER, BIGGER, EQUAL, or UNCOMPARABLE.
     */
    public int compareTo(final Occurrence otherOcc) {
        if (this.occ.size() < otherOcc.occ.size()) {
            for (int i = 0; i < this.occ.size(); i++) {
                if (this.occ.get(i).intValue() != otherOcc.occ.get(i).intValue()) {
                    return Occurrence.UNCOMPARABLE;
                }
            }
            return Occurrence.SMALLER;
        } else if (this.occ.size() > otherOcc.occ.size()) {
            for (int i = 0; i < otherOcc.occ.size(); i++) {
                if (this.occ.get(i).intValue() != otherOcc.occ.get(i).intValue()) {
                    return Occurrence.UNCOMPARABLE;
                }
            }
            return Occurrence.BIGGER;
        } else if (this.equals(otherOcc)) {
            return Occurrence.EQUAL;
        } else {
            return Occurrence.UNCOMPARABLE;
        }
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(final Object o) {
        if (o instanceof Occurrence) {
            final Occurrence otherOcc = (Occurrence) o;
            if (this.occ.size() == otherOcc.occ.size()) {
                boolean res = true;
                for (int i = 0; i < this.occ.size() && res; i++) {
                    res &= this.occ.get(i).intValue() == otherOcc.occ.get(i).intValue();
                }
                return res;
            }
        }
        return false;
    }

    /**
     * Gets the child number at the specified depth.
     * @param depth The depth of the child number.
     * @return The child number at the specified depth.
     */
    public Integer getChildNumber(final int depth) {
        return this.occ.get(depth);
    }

    /**
     * Returns the direct sub position below the current one.
     * @return The direct sub position below the current one.
     */
    public Occurrence getDirectSubOccurrence() {
        final List<Integer> newList = new ArrayList<Integer>();
        for (int i = 1; i < this.occ.size(); i++) {
            newList.add(this.occ.get(i));
        }
        return new Occurrence(newList);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        int res = 1;
        for (int i = 0; i < this.occ.size(); i++) {
            res += i * 3 * this.occ.get(i);
        }
        return res;
    }

    /**
     * Tests whether or not this Occurrence is the empty Occurrence.
     * @return True, if this Occurrence is empty. False otherwise.
     */
    public boolean isEpsilon() {
        return this.occ.isEmpty();
    }

    /* (non-Javadoc)
     * @see java.lang.Iterable#iterator()
     */
    @Override
    public Iterator<Integer> iterator() {
        return this.occ.iterator();
    }

    /**
     * Creates a new Occurrence where the child number at the specified depth is replaced by i.
     * @param i The value by which the child number should be replaced.
     * @param depth The depth where to replace the child number.
     * @return A new Occurrence emerging from the current one by replacing the child number at the specified depth by i.
     */
    public Occurrence replaceChildNumber(final Integer i, final int depth) {
        if (i < 0) {
            throw new NumberFormatException();
        }
        final List<Integer> newList = new ArrayList<Integer>(this.occ);
        newList.set(depth, i);
        return new Occurrence(newList);
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        if (this.isEpsilon()) {
            return "epsilon";
        } else {
            final StringBuilder res = new StringBuilder();
            res.append("[");
            for (int i = 0; i < this.occ.size() - 1; i++) {
                res.append(this.occ.get(i).toString());
                res.append(",");
            }
            res.append(this.occ.get(this.occ.size() - 1).toString());
            res.append("]");
            return res.toString();
        }
    }

}
