/*
 * Created on 12.04.2005
 */
package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * A position is a list of positionNumbers which
 * are natural numbers.
 *
 * Equality is defined by list-equality.
 *
 * @author thiemann
 * @version $Id$
 */
public final class Position implements Immutable, Iterable<Integer>,
 Exportable, XMLObligationExportable, CPFAdditional {

    /*
     * real values
     */
    private final int[] pos;

    /*
     * computed / cached values
     */
    private final int hashCode;

    /**
     * check for valid arguments of constructors
     */
    private static boolean checkValidArg(final int[] pos) {
        if (pos != null) {
            for (final int i : pos) {
                if (i < 0) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    /**
     * creates the position corresponding to
     * the given array pos.
     * This has to be non-null and all entries
     * must be natural numbers.
     *
     * Moreover, we do not make a copy of the array,
     * hence, the caller must ensure that the array pos
     * cannot be modified from the outside!!
     *
     * (constant time)
     * @param pos
     */
    private Position(final int[] pos) {
        if (Globals.useAssertions) {
            assert (Position.checkValidArg(pos));
        }
        this.pos = pos;
        this.hashCode = Arrays.hashCode(this.pos);
    }

    public static final Position EPSILON = new Position(new int[] {});

    /**
     * creates a new position
     * @return
     */
    public static Position create(final int... pos) {
        return new Position(pos);
    }

    @Override
    public boolean equals(final Object other) {
        if (this == other) {
            return true;
        }
        if (other == null || !(other instanceof Position)) {
            return false;
        }

        final Position that = (Position) other;
        return Arrays.equals(this.pos, that.pos);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    /**
     * checks whether this position is the
     * empty position epsilon = [ ].
     * @return
     */
    public boolean isEmptyPosition() {
        return this.pos.length == 0;
    }

    /**
     * computes whether this position is a prefix
     * of the other position, i.e.
     * whether this  = [i1,...,in] and
     *         other = [i1,...,in,in+1,...,im]
     *
     * @param other
     * @return
     */
    public boolean isPrefixOf(final Position other) {
        final int n = this.pos.length;
        final int m = other.pos.length;
        if (n > m) {
            return false;
        }
        for (int i = 0; i < n; i++) {
            if (this.pos[i] != other.pos[i]) {
                return false;
            }
        }
        return true;
    }

    /**
     * computes whether to two positions are
     * independent of each other, i.e. no position
     * is a prefix of the other position.
     * @param other
     * @return
     */
    public boolean isIndependent(final Position other) {
        int i = 0;
        int n = this.pos.length;
        final int m = other.pos.length;
        if (m < n) {
            n = m;
        }
        // now n is the minimum of the lengths
        while (i < n) {
            if (this.pos[i] != other.pos[i]) {
                return true;
            }
            i++;
        }
        return false;
    }

    /**
     * @param other
     * @return the longest position p such that
     *  p.isPrefixOf(this) && p.isPrefixOf(other) holds
     */
    public Position getLongestCommonPrefix(final Position other) {
        final int minLength = Math.max(this.pos.length, other.pos.length);
        int i;
        for (i = 0; i < minLength; ++i) {
            if (this.pos[i] != other.pos[i]) {
                break;
            }
        }
        final int[] res = new int[i];
        System.arraycopy(this.pos, 0, res, 0, i);
        return new Position(res);
    }

    /**
     * @param other
     * @return the shortest different prefix p such that
     *  p.isPrefixOf(this) && p.isPrefixOf(other) holds
     */
    public Position getShortestDifferentSufix(final Position other) {
        final int minLength = Math.min(this.pos.length, other.pos.length);
        int i;
        for (i = 0; i < minLength; ++i) {
            if (this.pos[i] != other.pos[i]) {
                break;
            }
        }
        final int size = this.pos.length - i;
        if (size > 0) {
            final int[] res = new int[size];
            System.arraycopy(this.pos, i, res, 0, size);
            return new Position(res);
        } else {
            return Position.create();
        }
    }

    /**
     * creates a new position where the positionNumber
     * i is prepended to the beginning of this position.
     * (linear time in this.getDepth())
     * @param i
     * @return
     */
    public Position prepend(final int i) {
        if (Globals.useAssertions) {
            assert (i >= 0);
        }
        final int n = this.pos.length;
        final int[] newPos = new int[n + 1];
        System.arraycopy(this.pos, 0, newPos, 1, n);
        newPos[0] = i;
        return new Position(newPos);
    }

    /**
     * creates a new position where the positionNumber
     * i is appended to the end of this position.
     * (linear time in this.getDepth())
     * @param i
     * @return
     */
    public Position append(final int i) {
        if (Globals.useAssertions) {
            assert (i >= 0);
        }
        final int n = this.pos.length;
        final int[] newPos = new int[n + 1];
        System.arraycopy(this.pos, 0, newPos, 0, n);
        newPos[n] = i;
        return new Position(newPos);
    }

    /**
     * creates a new position where the position
     * p is appended to the end of this position.
     * (linear time in depth)
     * @param i
     * @return
     */
    public Position append(final Position p) {
        final int n = this.pos.length;
        final int m = p.pos.length;
        final int[] newPos = new int[n + m];
        System.arraycopy(this.pos, 0, newPos, 0, n);
        System.arraycopy(p.pos, 0, newPos, n, m);
        return new Position(newPos);
    }

    public Position tail(final int n) {
        if (Globals.useAssertions) {
            assert (n >= 0);
        }
        final int l = this.pos.length;
        final int[] newPos = new int[l - n];
        System.arraycopy(this.pos, n, newPos, 0, l - n);
        return new Position(newPos);
    }

    /**
     * creates a new position where the last
     * n items are removed
     * @return
     */
    public Position shorten(final int n) {
        if (Globals.useAssertions) {
            assert (n >= 0);
        }
        final int l = this.pos.length;
        final int[] newPos = new int[l - n];
        System.arraycopy(this.pos, 0, newPos, 0, l - n);
        return new Position(newPos);
    }

    /**
     * returns the number of positionNumbers of this position
     */
    public int getDepth() {
        return this.pos.length;
    }

    /**
     * @param index - 0-based index for the position element
     * @return the index-th element in this
     */
    public int get(final int index) {
        return this.pos[index];
    }

    /**
     * returns this position as an array
     * (a copy as the internal array must not get outside,
     *  because then it may be modified)
     *
     * (linear time operation in getDepth())
     */
    public int[] toIntArray() {
        final int n = this.pos.length;
        final int[] copy = new int[n];
        System.arraycopy(this.pos, 0, copy, 0, n);
        return copy;
    }

    @Override
    public String export(final Export_Util eu) {
        final StringBuilder retStr = new StringBuilder();
        retStr.append("[");
        if (this.pos.length >= 1) {
            retStr.append(this.pos[0]);
        }
        for (int i = 1; i < this.pos.length; i++) {
            retStr.append("," + this.pos[i]);
        }
        retStr.append("]");
        return retStr.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    /**
     * returns an iterator that produces the positionNumbers
     * in normal order
     * (constant creation time, and constant access time with next/hasNext)
     */
    @Override
    public Iterator<Integer> iterator() {
        return new IntegerIterator();
    }

    /**
     * a simple iterator that iterates over
     * an int[] in standard order (from 0 to length-1).
     * It does not support the remove operation.
     *
     * @author thiemann
     */
    private class IntegerIterator implements Iterator<Integer> {

        private int i;
        private final int n;

        private IntegerIterator() {
            this.i = 0;
            this.n = Position.this.pos.length;
        }

        @Override
        public boolean hasNext() {
            return this.i != this.n;
        }

        @Override
        public Integer next() {
            if (this.i != this.n) {
                final int val = Position.this.pos[this.i];
                this.i++;
                return Integer.valueOf(val);
            } else {
                throw new NoSuchElementException();
            }
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }

    }

    public int lastIndex() {
        return this.pos[this.pos.length - 1];
    }

    public int firstIndex() {
        return this.pos[0];
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element e = XMLTag.POSITION.createElement(doc);
        for (final int p : this.pos) {
            e.appendChild(XMLTag.createInteger(doc, p + 1));
        }
        return e;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element position = CPFTag.POSITION_IN_TERM.create(doc);
        for (final int p : this.pos) {
            position.appendChild(CPFTag.POSITION.create(doc,
                    doc.createTextNode("" + (p + 1))));
        }
        return position;
    }

    /**
     * returns the TRUE Prefixes of this in INCREASING order
     *
     * @author Sebastian Weise
     */
    public LinkedHashSet<Position> getTruePrefixes() {
        final LinkedHashSet<Position> truePrefixes = new LinkedHashSet<Position>();
        if (!this.isEmptyPosition()) {
            for (int i = this.getDepth(); i >= 1; i--) {
                truePrefixes.add(this.shorten(i));
            }
        }
        return truePrefixes;
    }
}
