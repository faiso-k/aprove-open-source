package aprove.verification.dpframework.Orders ;

import java.math.*;
import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.xml.*;

/**
 * Implementation of the Knuth-Bendix Order with quasi precedence.
 *  @author  Andreas Kelle-Emden
 *  @version $Id$
 */

public class QKBO implements CPFExportableAfsOrder {

    protected final Qoset<FunctionSymbol> precedence;
    protected final Map<FunctionSymbol, BigInteger> weightMap;

    protected BigInteger w0;

    public QKBO(final Qoset<FunctionSymbol> precedence, final Map<FunctionSymbol, BigInteger> weight, final BigInteger w0) {
        this.precedence = precedence;
        this.weightMap = weight;
        this.w0 = w0;
    }

    /**
     * checks whether this KBO solves the given constraint. Is limited to EQ, GE, and GR,
     * where GE is implemented as GR or EQ
     * @param c
     * @return
     */
    @Override
    public boolean solves(final Constraint<TRSTerm> c) {
        // Check if (Q)KBO is applicable
        boolean isApplicable = true;
        final Set<TRSVariable> varSet = c.y.getVariables();
        for (final TRSVariable var : varSet) {
            if (this.countvar(c.x, var) < this.countvar(c.y, var)) {
                isApplicable = false;
            }
        }
        if (!isApplicable) {
            return false;
        }
        final OrderRelation rel = c.z;
        if (rel == OrderRelation.GE) {
            return this.inRelation(c.x, c.y, false);
        }
        if (rel == OrderRelation.GR) {
            return this.inRelation(c.x, c.y, true);
        }
        if (rel == OrderRelation.EQ) {
            return c.x.equals(c.y);
        }
        throw new RuntimeException("Relation "+rel+" not supported by KBO");
    }

    /**
     * checks s =_KBO t, i.e. s = t
     * @param s
     * @param t
     */
    @Override
    public boolean areEquivalent(final TRSTerm s, final TRSTerm t) {
        return s.equals(t);
    }


    // count variable var in term t
    protected int countvar(final TRSTerm t, final TRSVariable var) {
        if (t instanceof TRSVariable) {
            if (t.equals(var)) {
                return 1;
            }
        } else {
            final FunctionSymbol sym = ((TRSFunctionApplication)t).getRootSymbol();
            final int arity = sym.getArity();
            int res = 0;
            for (int i = 0; i < arity; i++) {
                res += this.countvar(((TRSFunctionApplication)t).getArgument(i), var);
            }
            return res;
        }
        return 0;
    }

    /**
     * Calculate the weight of a given term
     */
    public BigInteger weightOf(final TRSTerm t) {
        if (t instanceof TRSVariable) {
            return this.w0;
        } else {
            final TRSFunctionApplication fa = (TRSFunctionApplication)t;
            final FunctionSymbol sym = fa.getRootSymbol();
            BigInteger sum = this.weightMap.get(sym);
            final int arity = sym.getArity();
            for (int i = 0; i < arity; i++) {
                final BigInteger cur = this.weightOf(fa.getArgument(i));
                sum = sum.add(cur);
            }
            return sum;
        }
    }

    // Recursively check if the term l is in the right form
    // for KBO2a: f1(f2(...fn(x)...))
    protected boolean checkKBO2a(final TRSTerm l, final TRSVariable x) {
        if (l instanceof TRSVariable) {
            final TRSVariable v = (TRSVariable)l;
            return v.equals(x);
        } else {
            final TRSFunctionApplication fa = (TRSFunctionApplication)l;
            final FunctionSymbol sym = fa.getRootSymbol();
            final int arity = sym.getArity();
            if (arity == 1) {
                return this.checkKBO2a(fa.getArgument(0), x);
            } else {
                return false;
            }
        }
    }

    /**
     * Checks, whether s >(=) t holds with this Knuth-Bendix order or not.
     * @param strict s > t or s >= t.
     * @return TRUE, if s >(=) t holds with this KBO, FALSE otherwise
     */
    public boolean inRelation(final TRSTerm s, final TRSTerm t, final boolean strict) {
        // get weights
        final BigInteger weights = this.weightOf(s);
        final BigInteger weightt = this.weightOf(t);

        // non-strict: s == t
        if (!strict && s.equals(t)) {
            return true;
        }

        if (s instanceof TRSVariable) {
            if (strict) {
                return false;
            }
            // Non-strict:
            if (t instanceof TRSVariable) {
                return false;
            }
            final TRSFunctionApplication fat = (TRSFunctionApplication)t;
            final FunctionSymbol symt = fat.getRootSymbol();
            final int arity = symt.getArity();
            if (arity == 0) {
                // r is a constant
                boolean isMinimal = true;
                for (final FunctionSymbol sym : this.precedence.getSet()) {
                    if (sym.getArity() == 0 && !sym.equals(symt) && !this.precedence.isGreater(sym, symt)) {
                        isMinimal = false;
                    }
                }
                return isMinimal;
            } else {
                return false;
            }
        }

        // KBO1: w(s) > w(t)
        if (weights.compareTo(weightt) > 0) {
            return true;
        }

        // not KBO1: w(s) < w(t)
        if (weights.compareTo(weightt) < 0) {
            return false;
        }

        if (t instanceof TRSVariable) {
            // KBO2a: s = f(...(f(x))...), t = x
            if (this.checkKBO2a(s, (TRSVariable)t)) {
                return true;
            }
            // Nothing else applicable
            return false;
        } else {
            final TRSFunctionApplication fas = (TRSFunctionApplication)s;
            final TRSFunctionApplication fat = (TRSFunctionApplication)t;
            final FunctionSymbol syms = fas.getRootSymbol();
            final FunctionSymbol symt = fat.getRootSymbol();

            // KBO2b: s = f(...), t = g(...) and f > g
            if (this.precedence.isGreater(syms, symt)) {
                return true;
            }

            final int aritys = syms.getArity();
            final int arityt = symt.getArity();
            final int arity = (aritys>arityt) ? arityt : aritys;

            // KBO2c: s=f(s1, ... sn), t = g(t1, ..., tm), f ~ g and ...
            if (this.precedence.areEquivalent(syms, symt)) {
                // ... s1 >= t1, ... s(i-1) >= t(i-1) and
                // si > ti for some i < n
                for (int i = 0; i < arity; i++) {
                    final TRSTerm curs = fas.getArgument(i);
                    final TRSTerm curt = fat.getArgument(i);
                    if (!this.inRelation(curs, curt, false)) {
                        return false;
                    }
                    if (this.inRelation(curs, curt, true)) {
                        return true;
                    }
                }
                // strict: si >= ti for all i <= n and n < m
                if (aritys > arityt) {
                    return true;
                }
                // non-strict: si >= ti for all i <= n
                if (!strict && aritys == arityt) {
                    return true;
                }
                return false;
            }

            return false;
        }

    }

    @Override
    public boolean inRelation(final TRSTerm s, final TRSTerm t) {
        return this.inRelation(s, t, true);
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder res = new StringBuilder();
        res.append("Knuth-Bendix order "+o.cite(Citation.QKBO)+" with quasi precedence:");
        res.append(o.export(this.precedence));
        res.append(o.cond_linebreak()+"and weight map:");
        res.append(o.linebreak());
        res.append(o.set(this.weightMap.entrySet(), Export_Util.RULES));
        res.append(o.linebreak());
        res.append("The variable weight is "+this.w0);
        return res.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    /**
     * exports this KBO into CPF
     * @param doc
     * @param xmlMetaData
     * @param fs the set of function symbols to be exported
     * @param afs an optional AFS that is used before the KBO.
     * @return
     */
    @Override
    public Element toCPF(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final Iterable<FunctionSymbol> fs,
        final Afs afs)
    {
        final Element entries = CPFTag.PRECEDENCE_WEIGHT.create(doc);
        final Map<FunctionSymbol, Integer> precedenceMap = this.precedence.getTopSortMap();
        for (final FunctionSymbol preF : fs) {
            final FunctionSymbol f = (afs == null ? preF : afs.filter(preF));
            if (f == null) {
                continue;
            }
            BigInteger w = this.weightMap.get(f);
            if (w == null) {
                w = this.w0;
            }
            final Element weight = CPFTag.WEIGHT.create(doc, w);
            Integer precedence = precedenceMap.get(f);
            if (precedence == null) {
                precedence = 0;
            }
            entries.appendChild(CPFTag.PRECEDENCE_WEIGHT_ENTRY.create(
                doc,
                preF.toCPF(doc, xmlMetaData), // take unfiltered symbol as this is registered in xmlMetaData
                CPFTag.ARITY.create(doc, preF.getArity()), // take arity of unfiltered symbol (CPF requirement)
                CPFTag.PRECEDENCE.create(doc, precedence),
                weight));
        }
        final Element kbo =
            CPFTag.KNUTH_BENDIX_ORDER.create(
                doc,
                CPFTag.WEIGHT_ZERO.create(doc, this.w0),
            entries);
        if (afs != null) {
            kbo.appendChild(afs.toCPF(doc, xmlMetaData));
        }
        return CPFTag.ORDERING_CONSTRAINT_PROOF.create(doc, CPFTag.RED_PAIR.create(doc, kbo));
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        return this.toCPF(doc, xmlMetaData, this.weightMap.keySet(), null);
    }

    @Override
    public String isCPFSupported() {
        return null;
    }

}