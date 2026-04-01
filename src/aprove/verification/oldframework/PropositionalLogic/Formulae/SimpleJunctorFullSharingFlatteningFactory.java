package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Works like FullSharingFlatteningFactory, but only returns
 * formulae with junctors AND, OR and NOT (XOR and IFF are
 * expressed using these junctors).
 *
 * Useful e.g. for feeding SAT solvers like satmate, which works
 * on edimacs inputs restricted to AND, OR and NOT.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class SimpleJunctorFullSharingFlatteningFactory<T> extends
        FullSharingFlatteningFactory<T> {

    private final boolean XOR_AS_OR_FORMULA = true;
    // true:  A xor B is expressed as ((A and not B) or (not A and B))
    // false: A xor B is expressed as ((A or B) and (not A or not B))

    private final boolean IFF_AS_OR_FORMULA = true;
    // true:  A iff B is expressed as ((A and B) or (not A and not B))
    // false: A iff B is expressed as ((A or not B) and (not A or B))

    @Override
    public Formula<T> buildXor(Formula<T> f1, Formula<T> f2) {
        if (f1 == f2) { // phi xor phi \equiv 0
            return this.ZERO;
        }
        else if (f1 == this.ZERO) {
            return f2;
        }
        else if (f1 == this.ONE) {
            return this.buildNot(f2);
        }
        else if (f2 == this.ZERO) {
            return f1;
        }
        else if (f2 == this.ONE) {
            return this.buildNot(f1);
        }
        else {
            Set<Formula<T>> argsSet = new LinkedHashSet<Formula<T>>(2);
            argsSet.add(f1);
            argsSet.add(f2);
            Formula<T> result = this.XORS.get(argsSet);
            if (Globals.DEBUG_FUHS) {
                if (result == null) {
                    ++this.xorMisses;
                }
                else {
                    ++this.xorHits;
                }
            }
            if (result == null) {
                Formula<T> notF1 = this.buildNot(f1);
                Formula<T> notF2 = this.buildNot(f2);
                if (this.XOR_AS_OR_FORMULA) {
                    Formula<T> leftAnd = this.buildAnd(f1, notF2);
                    Formula<T> rightAnd = this.buildAnd(notF1, f2);
                    result = this.buildOr(leftAnd, rightAnd);
                }
                else {
                    Formula<T> leftOr = this.buildOr(f1, f2);
                    Formula<T> rightOr = this.buildOr(notF1, notF2);
                    result = this.buildAnd(leftOr, rightOr);
                }
                this.XORS.put(argsSet, result);
            }
            return result;
        }
    }

    @Override
    public Formula<T> buildXor(Formula<T> f1, Formula<T> f2, Formula<T> f3) {
        // phi xor phi xor theta \equiv 0 xor theta \equiv theta
        if (f1 == f2) {
            return f3;
        }
        else if (f1 == f3) {
            return f2;
        }
        else if (f2 == f3) {
            return f1;
        }
        else if (f1 == this.ZERO) {
            return this.buildXor(f2, f3);
        }
        else if (f1 == this.ONE) {
            return this.buildXor(this.buildNot(f2), f3);
        }
        else if (f2 == this.ZERO) {
            return this.buildXor(f1, f3);
        }
        else if (f2 == this.ONE) {
            return this.buildXor(this.buildNot(f1), f3);
        }
        else if (f3 == this.ZERO) {
            return this.buildXor(f1, f2);
        }
        else if (f3 == this.ONE) {
            return this.buildXor(this.buildNot(f1), f2);
        }
        else {
            // build a comb, using the cache
            // ((f1 xor f2) xor f3)
            Set<Formula<T>> argsSet = new LinkedHashSet<Formula<T>>(3);
            argsSet.add(f1);
            argsSet.add(f2);
            argsSet.add(f3);
            Formula<T> result = this.XORS.get(argsSet);
            if (Globals.DEBUG_FUHS) {
                if (result == null) {
                    ++this.xorMisses;
                }
                else {
                    ++this.xorHits;
                }
            }
            if (result == null) {
                // just use buildXor(Formula, Formula)
                Formula<T> f1XorF2 = this.buildXor(f1, f2);
                result = this.buildXor(f1XorF2, f3);
                this.XORS.put(argsSet, result);
            }
            return result;
        }
    }

    @Override
    public Formula<T> buildXor(List<Formula<T>> fmlae) {
        int size = fmlae.size();
        switch (size) {
        case 0:
            return this.ZERO;
        case 1:
            return fmlae.get(0);
        // reduce to buildXor(Formula^2) or buildXor(Formula^3)
        // where reasonably applicable
        case 2:
            return this.buildXor(fmlae.get(0), fmlae.get(1));
        case 3:
            return this.buildXor(fmlae.get(0), fmlae.get(1), fmlae.get(2));
        default:
            // at least 4 fmlae; unlikely to happen, at least with the POLO encoding.
            // TODO!
            if (true) {
                throw new RuntimeException("Xor of >= 4 formulae via And, Or, Not is not supported by SimpleJunctorFullSharingFlatteningFactory.");
            }
            return null;
            // perhaps just build a comb by repeated buildXor(Formula^3).

            /*
            // first of all, get rid of those nasty constants
            Set<Formula> argsSet = new LinkedHashSet<Formula>(size);
            boolean even = true; // seen an even number of ONEs
            for (Formula f : fmlae) {
                if (f == this.ONE) {
                    even = ! even;
                }
                else if (f != this.ZERO) {
                    boolean newlyAdded = argsSet.add(f);
                    if (! newlyAdded) {
                        // two occurences of f "cancel each other out", i.e.,
                        //        phi xor phi xor theta
                        // \equiv ZERO xor theta
                        // \equiv theta
                        argsSet.remove(f);
                    }
                }
            }
            int argsSize = argsSet.size();
            if (argsSize == 0) {
                return even ? this.ZERO : this.ONE;
            }

            List<Formula> args = new ArrayList<Formula>(argsSet);
            if (! even) {
                Formula notArg0 = buildNot(args.get(0));
                args.set(0, notArg0);
            }

            // now just build the formula without caching it and return it
            switch (argsSize) {
            case 1:
                return args.get(0);
            case 2:
                return new XorFormula(args);
            default:
                // xor combs are preferrable to flattened XorFormulae
                // because of the way Tseitin's algorithm works on XOR
                return buildXorComb(args);
            }
            */
        }
    }



    @Override
    public Formula<T> buildIff(Formula<T> left, Formula<T> right) {
        if (left == this.ZERO) {
            return this.buildNot(right);
        }
        if (left == this.ONE) {
            return right;
        }
        if (right == this.ZERO) {
            return this.buildNot(left);
        }
        if (right == this.ONE) {
            return left;
        }
        if (left == right) {
            return this.ONE;
        }
        Pair<Formula<T>, Formula<T>> lr = new Pair<Formula<T>, Formula<T>>(left, right);
        Formula<T> res = this.IFFS.get(lr);

        if (Globals.DEBUG_FUHS) {
            if (res == null) {
                ++this.iffMisses;
            }
            else {
                ++this.iffHits;
            }
        }

        if (res == null) {
            Formula<T> notLeft = this.buildNot(left);
            Formula<T> notRight = this.buildNot(right);

            if (this.IFF_AS_OR_FORMULA) {
                Formula<T> leftAnd = this.buildAnd(left, right);
                Formula<T> rightAnd = this.buildAnd(notLeft, notRight);
                res = this.buildOr(leftAnd, rightAnd);
            }
            else {
                Formula<T> leftOr = this.buildOr(left, notRight);
                Formula<T> rightOr = this.buildOr(notLeft, right);
                res = this.buildAnd(leftOr, rightOr);
            }

            this.IFFS.put(lr, res);

            // left <-> right
            // is equivalent to
            // right <-> left
            Pair<Formula<T>, Formula<T>> rl = new Pair<Formula<T>, Formula<T>>(right, left);
            this.IFFS.put(rl, res);
        }
        return res;
    }

    @Override
    public Formula<T> buildIte(Formula<T> condition, Formula<T> thenFormula, Formula<T> elseFormula) {
        if (condition == this.ZERO) {
            return elseFormula;
        }
        if (condition == this.ONE || thenFormula == elseFormula) {
            return thenFormula;
        }

        Triple<Formula<T>, Formula<T>, Formula<T>> lr = new Triple<Formula<T>, Formula<T>, Formula<T>>(condition,
                thenFormula, elseFormula);
        Formula<T> res = this.ITES.get(lr);

        if (res == null) {
            // (cond and thenFormula) or (! cond and elseFormula)
            Formula<T> d1, d2;
            d1 = this.buildAnd(condition, thenFormula);
            d2 = this.buildAnd(this.buildNot(condition), elseFormula);
            res = this.buildOr(d1, d2);
            this.ITES.put(lr, res);
        }
        return res;
    }

    @Override
    public <U> FormulaFactory<U> toTheory() {
        return new SimpleJunctorFullSharingFlatteningFactory<U>();
    }
}
