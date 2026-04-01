package aprove.verification.dpframework.TRSProblem.Utility.SRSNonLoop;

import java.util.*;

import org.w3c.dom.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * represents a StringPattern, which only consists of a List of
 * {@link FunctionSymbols}
 * @author Tim Enger
 */
public class StringPattern implements Immutable, CPFAdditional {

    private final ImmutableList<FunctionSymbol> funapps;
    private final int hashCode;
    private final int size;

    public StringPattern(TRSTerm term) {
        ArrayList<FunctionSymbol> tempApps = new ArrayList<FunctionSymbol>();
        ArrayList<TRSTerm> terms = new ArrayList<TRSTerm>(term.getSubTerms());
        for (int i = 0; i < term.getDepth(); i++) {
            tempApps.add(((TRSFunctionApplication) terms.get(i)).getRootSymbol());
        }

        this.funapps = ImmutableCreator.create(tempApps);
        this.hashCode = this.newHashCode();
        this.size = this.funapps.size();
    }

    public StringPattern(List<FunctionSymbol> list) {
        this.funapps = ImmutableCreator.create(new ArrayList<FunctionSymbol>(list));
        this.hashCode = this.newHashCode();
        this.size = this.funapps.size();
    }

    public int size() {
        return this.size;
    }

    /**
     * get sublist from the List of {@link FunctionSymbol},<br>
     * but Exceptions are catched
     * @param i begin
     * @param j end
     * @return Sublist from begin to end
     */
    public List<FunctionSymbol> getSublist(int i, int j) {
        try {
            return this.funapps.subList(i, j);
        } catch (Exception e) {
            return new ArrayList<FunctionSymbol>();
        }
    }

    @Override
    public boolean equals(Object o) {
        if (this.hashCode != o.hashCode()) {
            return false;
        }
        if (o instanceof StringPattern) {
            return this.funapps.equals(((StringPattern) o).getList());
        }
        return false;
    }

    /**
     * compares Sublists<br>
     * the SubList in <code>this</code> from <code>index1</code> to
     * <code>index1+length</code> <br>
     * equals<br>
     * Sublist from other from <code>index2</code> to <code>index2+length</code>
     * @param index1 start in this
     * @param other List to compare with
     * @param index2 start in list
     * @param length
     * @return see above
     */
    public boolean equalsSub(int index1,
        StringPattern other,
        int index2,
        int length) {

        if (this.size() < index1 + length || other.size() < index2 + length
            || index1 < 0 || index2 < 0) {
            return false;
        }

        for (int i = 0; i < length; i++) {
            if (!this.funapps.get(index1 + i).equals(other.getList().get(index2 + i))) {
                return false;
            }
        }
        return true;
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    public int newHashCode() {
        return this.funapps.hashCode();
    }

    public List<FunctionSymbol> getList() {
        return this.funapps;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        int i;
        for (i = 0; i < this.funapps.size() - 1; i++) {
            sb.append(this.funapps.get(i).getName());
        }
        if (this.funapps.size() > 0) {
            sb.append(this.funapps.get(i).getName());
        }
        return sb.toString();
    }

    /**
     * tests if 2 StringPattern overlap<br>
     * <br>
     * this: t_1 x t_2 <br>
     * other: x
     * @param other
     * @return a list of {@link Pair}s with each end of t1 and begin postion of
     * t2, on which this and other overlap
     */
    public List<Pair<Integer, Integer>> overlapMiddle(StringPattern other) {
        List<Pair<Integer, Integer>> list =
            new ArrayList<Pair<Integer, Integer>>();

        int sizeOther = other.size();
        int max = this.size();

        if (!(max < sizeOther)) {
            for (int i = 0; i <= max; i++) {
                if (this.equalsSub(i, other, 0, sizeOther)) {
                    list.add(new Pair<Integer, Integer>(i, i + sizeOther));
                }
            }
        }
        return list;
    }

    static Element stringToCPF(final Document doc, final XMLMetaData xmlMetaData, List<FunctionSymbol> fs) {
        Element e = CPFTag.STRING.create(doc);
        for (FunctionSymbol f : fs) {
            e.appendChild(f.toCPF(doc, xmlMetaData));
        }
        return e;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        return StringPattern.stringToCPF(doc, xmlMetaData, this.funapps);
    }

    /**
     * tests if 2 StringPattern overlap<br>
     * <br>
     * this: x t_1 <br>
     * other: t_2 x
     * @param other
     * @return list of {@link Pair}s with positions
     * <ul>
     * <li>begin of t_1 in this</li>
     * <li>end of t_2 in other</li>
     * </ul>
     */
    public List<Pair<Integer, Integer>> overlapBeginEnd(StringPattern other) {

        List<Pair<Integer, Integer>> list =
            new ArrayList<Pair<Integer, Integer>>();

        int sizeOther = other.size();
        int max = Math.min(sizeOther, this.size());

        for (int i = 1; i <= max; i++) {
            if (this.equalsSub(0, other, sizeOther - i, i)) {
                list.add(new Pair<Integer, Integer>(i, sizeOther - i));
            }
        }

        return list;
    }

}