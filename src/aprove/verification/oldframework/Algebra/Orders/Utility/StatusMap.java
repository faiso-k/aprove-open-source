package aprove.verification.oldframework.Algebra.Orders.Utility ;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.verification.oldframework.Algebra.Terms.Visitors.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.xml.*;

/** Status map for function symbols in LPOS and RPOS, i.e. which permutation
 * should be used for which function symbol and which function symbols
 * have multiset status?
 *
 * @author      Stephan Falke
 * @version $Id$
 */

public class StatusMap<T> implements HTML_Able, XMLObligationExportable
{
    private final Map<T, Permutation> map;
    private static final Permutation mul = Permutation.create(new int[]{-100});
    private static final Permutation flat = Permutation.create(new int[]{-1000});

    /* constructors */

    private StatusMap(final Map<T, Permutation> map) {
        this.map = map;
    }

    /** Creates a new instance of <code>StatusMap</code>.
     * @param set   the set of function symbols
     */
    static public <U> StatusMap<U> create(final Collection<U> set) {
        return new StatusMap<U>(new LinkedHashMap<U, Permutation>(set.size()));
    }

    /** Returns a deep copy of this object.
     */
    public StatusMap<T> deepcopy() {
        return new StatusMap<T>(new LinkedHashMap<T, Permutation>(this.map));
    }

    /** Assigns permutation <code>perm</code> to object <code>o</code>.
     */
    public void assignPermutation(final T o, final Permutation perm) {
        this.map.put(o, perm);
    }

    /** Assign multiset status to object <code>o</code>.
     */
    public void assignMultisetStatus(final T o) {
        this.map.put(o, StatusMap.mul);
    }

    /** Assign flat status to object <code>o</code>.
     */
    public void assignFlatStatus(final T o) {
        this.map.put(o, StatusMap.flat);
    }

    /** Returns <code>o</code>'s permutation.
     */
    public Permutation getPermutation(final T o) {
        final Permutation res = this.map.get(o);
        return res == StatusMap.mul ? null : res;
    }

    public Map<T, Permutation> getMapCopy() {
        return new LinkedHashMap<T, Permutation>(this.map);
    }

    /** Returns <code>true</code> if <code>o</code> has a permutation in this
     * map, <code>false</code> otherwise.
     */
    public boolean hasPermutation(final T o) {
        final Permutation perm = this.map.get(o);
        return perm != null && perm != StatusMap.mul && perm != StatusMap.flat;
    }

    /** Returns <code>true</code> if <code>o</code> has multiset status in
     * this map, </code>false</code> otherwise.
     */
    public boolean hasMultisetStatus(final T o) {
        return this.map.get(o) == StatusMap.mul;
    }

    /** Returns <code>true</code> if <code>o</code> has flat status in
     * this map, </code>false</code> otherwise.
     */
    public boolean hasFlatStatus(final T o) {
        return this.map.get(o) == StatusMap.flat;
    }


    /** Returns <code>true</code> if <code>o</code> has a status in
     * this map, </code>false</code> otherwise.
     */
    public boolean hasEntry(final T o) {
        return this.map.containsKey(o);
    }

    /** Merges this status map with the status map <code>other</code> and
     * returns a new status map.
     * Throws <code>StatusMapException</code> if the status maps disagree on
     * some element of <code>set</code>.
     */

    /** Merges this status map with the status map <code>other</code> and
     * returns a new status map.
     * Throws <code>StatusMapException</code> if the status maps disagree on
     * some element of <code>set</code>.
     */
    public StatusMap<T> merge(final StatusMap<T> other) throws StatusMapException {
        final Map<T, Permutation> res = new LinkedHashMap<T, Permutation>(this.map.size()* 3 / 2);
        res.putAll(this.map);
        for (final Map.Entry<T, Permutation> otherEntry : other.map.entrySet()) {
            final Permutation otherPerm = otherEntry.getValue();
            final Permutation thisPerm  = res.put(otherEntry.getKey(), otherPerm);
            if (thisPerm != null && !thisPerm.equals(otherPerm)) {
                throw new StatusMapException("Disagree in merge");
            }
        }
        return new StatusMap<T>(res);
    }

    /** Intersects this status map with the status map <code>other</code>
     * and returns a new status map.
     */
    public StatusMap<T> intersect(final StatusMap<T> other) throws StatusMapException {
        final Map<T, Permutation> res = new LinkedHashMap<T, Permutation>(this.map.size());
        final Map<T, Permutation> otherPerms = other.map;
        for (final Map.Entry<T, Permutation> thisPerm : this.map.entrySet()) {
            final T key = thisPerm.getKey();
            final Permutation perm = otherPerms.get(key);
            if (perm != null) {
                if (perm.equals(thisPerm.getValue())) {
                    res.put(key, perm);
                }
            }
        }
        return new StatusMap<T>(res);
    }

    /** Returns <code>true</code> is this status map is contained in the status
     * map <code>other</code>.
     * A status map <code>M</code> is contained in a status map <code>N</code>
     * iff <code>M.hasPermutation(o)</code> implies
     * <code>M.getPermutation(o).equals(N.getPermutation(o))</code> for all
     * objects <code>o</code>.
     */
    public boolean isContainedIn(final StatusMap<T> other) throws StatusMapException {

        final Map<T, Permutation> otherPerms = other.map;
        for (final Map.Entry<T, Permutation> thisPerm : this.map.entrySet()) {
            final Permutation otherPerm = otherPerms.get(thisPerm.getKey());
            if (otherPerm == null || !otherPerm.equals(thisPerm.getValue())) {
                return false;
            }
        }
        return true;
    }

    /** Returns <code>true</code> if this object and the object
     * <code>o</code> represent the same status map, <code>false</code>
     * otherwise.
     */
    @Override
    public boolean equals(final Object o) {
        if (o == null) {
            return false;
        }
        final StatusMap other = (StatusMap)o;
        return this.map.equals(other.map);
    }

    @Override
    public int hashCode() {
        return this.map.hashCode();
    }

    public StatusMap<T> project(final Collection<T> newSet) {
        final Map<T, Permutation> res = new LinkedHashMap<T, Permutation>(this.map);
        res.keySet().retainAll(newSet);
        return new StatusMap<T>(res);
    }


    /** Returns a string representation of this object.
     */
    @Override
    public String toString() {
        final StringBuilder result = new StringBuilder();

        for (final Map.Entry<T, Permutation> entry : this.map.entrySet()) {
            result.append(entry.getKey());
            result.append(": ");
            final Permutation perm = entry.getValue();
            if(perm == StatusMap.flat) {
                result.append("flat status");
            }
            else if(perm == StatusMap.mul) {
                result.append("multiset status");
            }
            else {
                result.append(perm.toString());
            }
            result.append("\n");
        }

        return result.toString();
    }

    /** Returns a HTML representation of this object.
     */
    @Override
    public String toHTML() {
        if (this.map.isEmpty()) {
            return "<BLOCKQUOTE>trivial</BLOCKQUOTE>";
        } else {
            StringBuilder result = null;
            for (final Map.Entry<T, Permutation> entry : this.map.entrySet()) {
                if (result == null) {
                    result = new StringBuilder();
                } else {
                    result.append("<BR>");
                }
                result.append(ToHTMLVisitor.escape(entry.getKey().toString()));
                result.append(": ");
                final Permutation perm = entry.getValue();
                if(perm == StatusMap.mul) {
                    result.append("multiset");
                } else if(perm == StatusMap.flat) {
                    result.append("flat");
                } else {
                    result.append(perm);
                }
            }
            return "<BLOCKQUOTE>"+result.toString()+"</BLOCKQUOTE>";
        }
    }

    public String toLaTeX() {
        if (this.map.isEmpty()) {
            return "\\begin{center}trivial\\end{center}\n";
        } else {
            StringBuilder result = null;
            for (final Map.Entry<T, Permutation> entry : this.map.entrySet()) {
                if (result == null) {
                    result = new StringBuilder("\\begin{eqnarray*}\n");
                } else {
                    result.append("\\\\\n");
                }
                result.append("\\mathsf{"+ToLaTeXVisitor.escape(entry.getKey().toString())+"}");
                result.append(": && ");
                final Permutation perm = entry.getValue();
                if(perm == StatusMap.mul) {
                    result.append("\\text{multiset}");
                } else if (perm == StatusMap.flat) {
                    result.append("\\text{flat}");
                } else {
                    result.append(perm);
                }
            }
            result.append("\\end{eqnarray*}\n");
            return result.toString();

        }
    }

    public int getSizeMeasure() {
        return this.map.size();
    }

    public String export(final Export_Util eu) {
        if (eu instanceof PLAIN_Util) {
            return this.toString();
        } else if (eu instanceof HTML_Util) {
            return this.toHTML();
        } else if (eu instanceof LaTeX_Util) {
            return this.toLaTeX();
        } else {
            return this.toString();
        }
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {

        final Element mapTag = XMLTag.STATUS_MAP.createElement(doc);
        boolean symbolArityGreater1WithMul = false;
        final boolean symbolArityGreater1WithLex = false;
        for (final Map.Entry<T, Permutation> entry : this.map.entrySet()) {
            if (entry.getKey() instanceof FunctionSymbol) {
                final FunctionSymbol fSym = (FunctionSymbol) entry.getKey();
                final Permutation perm = entry.getValue();
                if (fSym.getArity() > 1 && (perm == StatusMap.mul)) {
                    symbolArityGreater1WithMul = true;
                    final Element multi = XMLTag.MULTISET.createElement(doc);
                    mapTag.appendChild(multi);
                }
                if (fSym.getArity() > 1 && !(perm == StatusMap.mul)) {
                    symbolArityGreater1WithMul = true;
                    final Element lexi = XMLTag.LEXICOGRAPHIC
                            .createElement(doc);
                    mapTag.appendChild(lexi);
                }
            } else {
                if (Globals.useAssertions) {
                    assert (false) : "It should be a Function Symbol that you want to export!";
                }
            }
        }
        if (Options.certifier.isCeta()) {
            assert (!(symbolArityGreater1WithLex && symbolArityGreater1WithMul));
        }
        for (final Map.Entry<T, Permutation> entry : this.map.entrySet()) {
            final Element statusTag = XMLTag.STATUS.createElement(doc);
            if (Globals.useAssertions) {
                // only this case is relevant for XML output
                // is this class ever used with other parameters, anyway?
                assert(entry.getKey() instanceof FunctionSymbol);
            }
            final FunctionSymbol fsym = (FunctionSymbol)entry.getKey();
            statusTag.appendChild(fsym.toDOM(doc, xmlMetaData));
            final Permutation perm = entry.getValue();
            if (perm == StatusMap.mul) {
                statusTag.appendChild(XMLTag.MULTISET.createElement(doc));
            } else { // lexicographic
                final Element lexTag = XMLTag.LEXICOGRAPHIC.createElement(doc);
//                if (Globals.a3pat && perm.isPermutation()) {
//                     color has no opertunity to certify permutating orders, yet
//                }
                if (perm != StatusMap.flat) {
                    for (int i = 0; i < perm.size(); i++) {
                        lexTag.appendChild(XMLTag.createInteger(doc, perm.get(i)+1));
                    }
                }
                statusTag.appendChild(lexTag);
            }
            mapTag.appendChild(statusTag);
        }
        return mapTag;
    }

}
