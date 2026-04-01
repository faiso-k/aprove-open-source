/*
 * Created on 12.04.2005
 */
package aprove.verification.idpframework.Core.BasicStructures;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * A position is a list of positionNumbers which are natural numbers. Equality
 * is defined by list-equality.
 * @author Martin Pluecker, copied from thiemann
 * @version $Id$
 */
public final class IPosition implements Immutable, Iterable<Integer>,
        Exportable,
        XmlExportable,
        XMLObligationExportable,
        CPFAdditional
{

    public static final IPosition EMPTY = IPosition.create(new int[0]);

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
     * creates the position corresponding to the given array pos. This has to be
     * non-null and all entries must be natural numbers. Moreover, we do not
     * make a copy of the array, hence, the caller must ensure that the array
     * pos cannot be modified from the outside!! (constant time)
     * @param pos
     */
    private IPosition(final int[] pos) {
        if (Globals.useAssertions) {
            assert (IPosition.checkValidArg(pos));
        }
        this.pos = pos;
        this.hashCode = Arrays.hashCode(this.pos);
    }

    /**
     * creates the empty Position
     * @return
     */
    public static IPosition create() {
        return IPosition.EMPTY;
    }

    /**
     * creates a new position
     * @return
     */
    public static IPosition create(final int[] pos) {
        return new IPosition(pos);
    }

    /**
     * creates a new position
     * @return
     */
    public static IPosition create(final List<Integer> pos) {
        final int[] p = new int[pos.size()];
        for (int i = p.length - 1; i >= 0; i--) {
            p[i] = pos.get(i);
        }
        return IPosition.create(p);
    }

    @Override
    public boolean equals(final Object other) {
        if (this == other) {
            return true;
        }
        if (other == null || !(other instanceof IPosition)) {
            return false;
        }

        final IPosition that = (IPosition) other;
        return Arrays.equals(this.pos, that.pos);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    /**
     * checks whether this position is the empty position epsilon = [ ].
     * @return
     */
    public boolean isEmptyPosition() {
        return this.pos.length == 0;
    }

    /**
     * computes whether this position is a prefix of the other position, i.e.
     * whether this = [i1,...,in] and other = [i1,...,in,in+1,...,im]
     * @param other
     * @return
     */
    public boolean isPrefixOf(final IPosition other) {
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
     * computes whether to two positions are independent of each other, i.e. no
     * position is a prefix of the other position.
     * @param other
     * @return
     */
    public boolean isIndependent(final IPosition other) {
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
     * @return the longest position p such that p.isPrefixOf(this) &&
     * p.isPrefixOf(other) holds
     */
    public IPosition getLongestCommonPrefix(final IPosition other) {
        final int minLength = Math.max(this.pos.length, other.pos.length);
        int i;
        for (i = 0; i < minLength; ++i) {
            if (this.pos[i] != other.pos[i]) {
                break;
            }
        }
        final int[] res = new int[i];
        System.arraycopy(this.pos, 0, res, 0, i);
        return new IPosition(res);
    }

    /**
     * @param other
     * @return the shortest different prefix p such that p.isPrefixOf(this) &&
     * p.isPrefixOf(other) holds
     */
    public IPosition getShortestDifferentSufix(final IPosition other) {
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
            return new IPosition(res);
        } else {
            return IPosition.create();
        }
    }

    /**
     * creates a new position where the positionNumber i is prependet to the
     * beginning of this position. (linear time in this.getDepth())
     * @param i
     * @return
     */
    public IPosition prepend(final int i) {
        if (Globals.useAssertions) {
            assert (i >= 0);
        }
        final int n = this.pos.length;
        final int[] newPos = new int[n + 1];
        System.arraycopy(this.pos, 0, newPos, 1, n);
        newPos[0] = i;
        return new IPosition(newPos);
    }

    /**
     * creates a new position where the positionNumber i is appended to the end
     * of this position. (linear time in this.getDepth())
     * @param i
     * @return
     */
    public IPosition append(final int i) {
        if (Globals.useAssertions) {
            assert (i >= 0);
        }
        final int n = this.pos.length;
        final int[] newPos = new int[n + 1];
        System.arraycopy(this.pos, 0, newPos, 0, n);
        newPos[n] = i;
        return new IPosition(newPos);
    }

    /**
     * creates a new position where the position p is appended to the end of
     * this position. (linear time in depth)
     * @param i
     * @return
     */
    public IPosition append(final IPosition p) {
        final int n = this.pos.length;
        final int m = p.pos.length;
        final int[] newPos = new int[n + m];
        System.arraycopy(this.pos, 0, newPos, 0, n);
        System.arraycopy(p.pos, 0, newPos, n, m);
        return new IPosition(newPos);
    }

    public IPosition tail(final int n) {
        if (Globals.useAssertions) {
            assert (n >= 0);
        }
        final int l = this.pos.length;
        final int[] newPos = new int[l - n];
        System.arraycopy(this.pos, n, newPos, 0, l - n);
        return new IPosition(newPos);
    }

    /**
     * creates a new position where the last n items are removed
     * @return
     */
    public IPosition shorten(final int n) {
        if (Globals.useAssertions) {
            assert (n >= 0);
        }
        final int l = this.pos.length;
        final int[] newPos = new int[l - n];
        System.arraycopy(this.pos, 0, newPos, 0, l - n);
        return new IPosition(newPos);
    }

    /**
     * returns the number of positionNumbers of this position
     */
    public int getDepth() {
        return this.pos.length;
    }

    /**
     * returns the position at a certain depth
     */
    public int getPosition(final int depth) {
        return this.pos[depth];
    }

    /**
     * returns this position as an array (a copy as the internal array must not
     * get outside, because then it may be modified) (linear time operation in
     * getDepth())
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
    public Map<String, String> getXmlAttribs(final XmlExporter xe) {
        final Map<String, String> m = new HashMap<String, String>();
        m.put("posCount", Integer.toString(this.pos.length));
        for (int i = 0; i < this.pos.length; i++) {
            m.put("pos" + i, Integer.toString(this.pos[i]));
        }
        return m;
    }

    @Override
    public XmlContentsMap getXmlContents(final XmlExporter xe) {
        return null;
    }

    @Override
    public final String toString() {
        return this.export(new PLAIN_Util());
    }

    /**
     * returns an iterator that produces the positionNumbers in normal order
     * (constant creation time, and constant access time with next/hasNext)
     */
    @Override
    public Iterator<Integer> iterator() {
        return new IntegerIterator();
    }

    /**
     * a simple iterator that iterates over an int[] in standard order (from 0
     * to length-1). It does not support the remove operation.
     * @author Martin Pluecker, copied from thiemann
     */
    private class IntegerIterator implements Iterator<Integer> {

        private int i;
        private final int n;

        private IntegerIterator() {
            this.i = 0;
            this.n = IPosition.this.pos.length;
        }

        @Override
        public boolean hasNext() {
            return this.i != this.n;
        }

        @Override
        public Integer next() {
            if (this.i != this.n) {
                final int val = IPosition.this.pos[this.i];
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
        final Element position = CPFTag.POSITION.create(doc);
        for (final int p : this.pos) {
            final Element integer = CPFTag.INTEGER.create(doc,
                    doc.createTextNode("" + (p + 1)));
            position.appendChild(integer);
        }
        return position;
    }

    /**
     * returns the TRUE Prefixes of this in INCREASING order
     */
    public LinkedHashSet<IPosition> getTruePrefixes() {
        final LinkedHashSet<IPosition> truePrefixes =
            new LinkedHashSet<IPosition>();
        if (!this.isEmptyPosition()) {
            for (int i = this.getDepth(); i >= 1; i--) {
                truePrefixes.add(this.shorten(i));
            }
        }
        return truePrefixes;
    }
}
