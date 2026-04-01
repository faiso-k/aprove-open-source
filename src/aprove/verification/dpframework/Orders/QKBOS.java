package aprove.verification.dpframework.Orders;

import java.math.*;
import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * KBO with quasi precedence and status
 *
 * @author Andreas Kelle-Emden
 *
 */
public class QKBOS extends QKBO {

    protected StatusMap<FunctionSymbol> statusMap;

    public QKBOS(Qoset<FunctionSymbol> precedence, Map<FunctionSymbol, BigInteger> weight, BigInteger w0, StatusMap<FunctionSymbol> status) {
        super(precedence, weight, w0);
        this.statusMap = status;
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder res = new StringBuilder();
        res.append("Knuth-Bendix order "+o.cite(Citation.KBO)+" with quasi precedence:");
        res.append(o.export(this.precedence));
        res.append(o.cond_linebreak()+"weight map:");
        res.append(o.linebreak());
        res.append(o.set(this.weightMap.entrySet(), Export_Util.RULES));
        res.append(o.cond_linebreak()+"and status map:");
        res.append(o.linebreak());
        res.append(o.export(this.statusMap));
        res.append(o.linebreak());
        res.append("The variable weight is "+this.w0);
        return res.toString();
    }

    /**
     * Checks, whether s >(=) t holds with this Knuth-Bendix order or not.
     * @param strict s > t or s >= t.
     * @return TRUE, if s >(=) t holds with this KBO, FALSE otherwise
     */
    @Override
    public boolean inRelation(TRSTerm s, TRSTerm t, final boolean strict) {
        // get weights
        BigInteger weights = this.weightOf(s);
        BigInteger weightt = this.weightOf(t);

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
            TRSFunctionApplication fat = (TRSFunctionApplication)t;
            FunctionSymbol symt = fat.getRootSymbol();
            int arity = symt.getArity();
            if (arity == 0) {
                // r is a constant
                boolean isMinimal = true;
                for (FunctionSymbol sym : this.precedence.getSet()) {
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
            TRSFunctionApplication fas = (TRSFunctionApplication)s;
            TRSFunctionApplication fat = (TRSFunctionApplication)t;
            FunctionSymbol syms = fas.getRootSymbol();
            FunctionSymbol symt = fat.getRootSymbol();
            Permutation perms = this.statusMap.getPermutation(syms);
            Permutation permt = this.statusMap.getPermutation(symt);

            // KBO2b: s = f(...), t = g(...) and f > g
            if (this.precedence.isGreater(syms, symt)) {
                return true;
            }

            int aritys = syms.getArity();
            int arityt = symt.getArity();
            int arity = (aritys>arityt) ? arityt : aritys;

            // KBO2c: s=f(s1, ... sn), t = g(t1, ..., tm), f ~ g and ...
            if (this.precedence.areEquivalent(syms, symt)) {
                // ... s1 >= t1, ... s(i-1) >= t(i-1) and
                // si > ti for some i < n
                for (int i = 0; i < arity; i++) {
                    TRSTerm curs = fas.getArgument(perms.get(i));
                    TRSTerm curt = fat.getArgument(permt.get(i));
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

}
