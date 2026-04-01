package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * A TermPair is a pair of arbitrary terms (as opposed to a rule or
 * a generalized rule, where additional restrictions are imposed).
 *
 * @author fuhs
 * @version $Id$
 */
public class TermPair implements Immutable, Exportable, HasFunctionSymbols,
                    HasVariables, HasTRSTerms, Comparable<TermPair> {

    /*
     * real values
     */
    private final TRSTerm l;
    private final TRSTerm r;

    /*
     * computed values
     */
    private final TRSTerm stdL;
    private final TRSTerm stdR;

    private int hashCode;

    private static boolean checkProperLandR(TRSTerm l, TRSTerm r) {
        return l != null && r != null;
    }

    private static boolean checkProperStd(TRSTerm l, TRSTerm stdL, TRSTerm r, TRSTerm stdR) {
        if (stdL == null || stdR == null) {
            return false;
        }
        Map<TRSVariable, TRSVariable> map = new HashMap<TRSVariable, TRSVariable>();
        ImmutablePair<? extends TRSTerm, Integer> stdLAndInt = l.renumberVariables(map,
                TRSTerm.STANDARD_PREFIX, TRSTerm.STANDARD_NUMBER);
        if (!stdLAndInt.x.equals(stdL)) {
            return false;
        }
        ImmutablePair<? extends TRSTerm, Integer> stdRAndInt = r.renumberVariables(map,
                TRSTerm.STANDARD_PREFIX, stdLAndInt.y);
        return stdRAndInt.x.equals(stdR);
    }


    private TermPair(TRSTerm l, TRSTerm r, TRSTerm stdL, TRSTerm stdR) {
        this.l = l;
        this.r = r;
        if (Globals.useAssertions) {
            assert(TermPair.checkProperLandR(l, r));
            assert((stdL == null && stdR == null) || (stdL != null && stdR != null));
        }
        if (stdL == null) {
            Map<TRSVariable, TRSVariable> map = new HashMap<TRSVariable, TRSVariable>();
            ImmutablePair<? extends TRSTerm, Integer> stdLAndInt = l.renumberVariables(map,
                    TRSTerm.STANDARD_PREFIX, TRSTerm.STANDARD_NUMBER);
            ImmutablePair<? extends TRSTerm, Integer> stdRAndInt = r.renumberVariables(map,
                    TRSTerm.STANDARD_PREFIX, stdLAndInt.y);
            stdL = stdLAndInt.x;
            stdR = stdRAndInt.x;
        }
        this.stdL = stdL;
        this.stdR = stdR;
        if (Globals.useAssertions) {
            assert(TermPair.checkProperStd(this.l, this.stdL, this.r, this.stdR));
        }
        this.hashCode = 490321*stdL.hashCode() + 12812*stdR.hashCode() + 312038193;
    }

    /**
     * creates a new TermPair.
     * Restrictions:
     *   neither l nor r may be null
     * @param l - a term
     * @param r - a term
     */
    public static TermPair create(TRSTerm l, TRSTerm r) {
        return new TermPair(l, r, null, null);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    /**
     * Equality is defined modulo variable renaming.
     *
     * In the impl. this is done using a standard representation of a rule
     */
    /*
     * if you remove the final and define some other kind
     * of equality for the children class, please
     * make sure that compareTo is also updated accordingly!!
     */
    public final boolean equals(Object other) {
        if (this == other) {
            return true;
        }
        if (other instanceof TermPair) {
            TermPair that = (TermPair)other;
            return this.hashCode == that.hashCode && this.stdL.equals(that.stdL) && this.stdR.equals(that.stdR);
        }
        return false;
    }

    @Override
    public final int compareTo(TermPair other) {
        int compare = this.stdL.compareTo(other.stdL);
        if (compare == 0) {
            compare = this.stdR.compareTo(other.stdR);
        }
        return compare;
    }

    /**
     * returns the lhs
     */
    public TRSTerm getLeft() {
        return this.l;
    }

    /**
     * returns the rhs.
     */
    public TRSTerm getRight() {
        return this.r;
    }


    /**
     * returns the set of terms occurring in this, i.e., {l,r}
     */
    @Override
    public Set<TRSTerm> getTerms() {
        Set<TRSTerm> res = new LinkedHashSet<TRSTerm>(2);
        res.add(this.l);
        res.add(this.r);
        return res;
    }

    /**
     * returns the set of variables occurring in this
     */
    @Override
    public Set<TRSVariable> getVariables() {
        Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>(this.l.getVariables());
        vars.addAll(this.r.getVariables());
        return vars;
    }

    /**
     * returns the set of functionSymbols occurring in this rule.
     * the resulting set may be modified
     */
    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        Set<FunctionSymbol> fs = new LinkedHashSet<FunctionSymbol>();
        this.l.collectFunctionSymbols(fs);
        this.r.collectFunctionSymbols(fs);
        return fs;
    }

    /**
     * returns the lhs in standardRepresentation.
     * (constant time)
     */
    public TRSTerm getLhsInStandardRepresentation() {
        return this.stdL;
    }

    /**
     * returns the rhs in standardRepresentation.
     * (constant time)
     */
    public TRSTerm getRhsInStandardRepresentation() {
        return this.stdR;
    }

    /**
     * returns the standard representation of this
     * pair where l = stdL and r = stdR.
     * (constant time)
     * @see getWithRenumberedVariables
     */
    public TermPair getStandardRepresentation() {
        return new TermPair(this.stdL, this.stdR, this.stdL, this.stdR);
    }

    /**
     * Returns true if the name of every variable in this term pair starts with
     * the string prefix.
     *
     * @param prefix
     * @return
     */
    public boolean checkVariablePrefix(String prefix) {
        for (TRSVariable v : this.getVariables()) {
            if (!v.getName().startsWith(prefix)) {
                return false;
            }
        }
        return true;
    }

    /**
     * @return a new TermPair with l and r flipped
     */
    public TermPair flip() {
        return new TermPair(this.r, this.l, this.stdR, this.stdL);
    }


    @Override
    public String export(Export_Util eu) {
        return "( " + this.getLeft().export(eu) + ", " +
            this.getRight().export(eu) + ")";
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }
}
