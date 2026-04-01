package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * Special version of FullSharingFactory which also caches higher-arity XORs
 * and does NOT build combs.
 *
 * @author Peter Schneider-Kamp, Carsten Fuhs
 * @version $Id$
 */
public class FullSharingXorFactory<T> extends FullSharingFactory<T> {

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
            Set<Formula<T>> argsSet = new LinkedHashSet<Formula<T>>(3);
            argsSet.add(f1);
            argsSet.add(f2);
            argsSet.add(f3);
            Formula<T> res = this.XORS.get(argsSet);
            if (Globals.DEBUG_FUHS) {
                if (res == null) {
                    ++this.xorMisses;
                }
                else {
                    ++this.xorHits;
                }
            }
            if (res == null) {
                List<Formula<T>> args = new ArrayList<Formula<T>>(argsSet);
                res = new XorFormula<T>(args);
                this.XORS.put(argsSet, res);
            }
            return res;
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
            // first of all, get rid of those nasty constants
            Set<Formula<T>> argsSet = new LinkedHashSet<Formula<T>>(size);
            boolean even = true; // seen an even number of ONEs
            for (Formula<T> f : fmlae) {
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

            List<Formula<T>> args = new ArrayList<Formula<T>>(argsSet);
            if (! even) {
                Formula<T> notArg0 = this.buildNot(args.get(0));
                args.set(0, notArg0);
            }

            // now just build the formula with caching it and return it
            switch (argsSize) {
            case 1:
                return args.get(0);
            case 2:
                return this.buildXor(args.get(0), args.get(1));
            default:
                Formula<T> res = this.XORS.get(argsSet);
                if (Globals.DEBUG_FUHS) {
                    if (res == null) {
                        ++this.xorMisses;
                    }
                    else {
                        ++this.xorHits;
                    }
                }
                if (res == null) {
                    res = new XorFormula<T>(args);
                    this.XORS.put(argsSet, res);
                }
                return res;
            }
        }
    }

}
