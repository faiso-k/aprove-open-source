package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * Special version of FullSharingFlatteningFactory which also caches higher-arity XORs
 * and does NOT build combs.
 *
 * @author Peter Schneider-Kamp, Carsten Fuhs
 * @version $Id$
 */
public class FullSharingFlatteningXorFactory<T> extends FullSharingFlatteningFactory<T> {

    @Override
    public Formula<T> buildXor(Formula<T> f1, Formula<T> f2) {
        List<Formula<T>> args = new ArrayList<Formula<T>>(2);
        args.add(f1);
        args.add(f2);
        return this.buildXor(args);
    }

    @Override
    public Formula<T> buildXor(Formula<T> f1, Formula<T> f2, Formula<T> f3) {
        List<Formula<T>> args = new ArrayList<Formula<T>>(3);
        args.add(f1);
        args.add(f2);
        args.add(f3);
        return this.buildXor(args);
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
        default:
            // first of all, get rid of those nasty constants
            Set<Formula<T>> argsSet = new LinkedHashSet<Formula<T>>(size);
            boolean even = true; // seen an even number of ONEs
            for (Formula<T> f : fmlae) {
                if (f == this.ONE) {
                    even = ! even;
                } else if (f == this.ZERO) {
                    // can safely be ignored
                    continue;
                } else if (f instanceof XorFormula) {
                    XorFormula<T> xf = (XorFormula<T>)f;
                    for (Formula<T> g : xf.args) {
                        boolean newlyAdded = argsSet.add(g);
                        if (!newlyAdded) {
                            // two occurences of g "cancel each other out", i.e.,
                            //        phi xor phi xor theta
                            // \equiv ZERO xor theta
                            // \equiv theta
                            argsSet.remove(g);
                        }
                    }
                } else {
                    boolean newlyAdded = argsSet.add(f);
                    if (!newlyAdded) {
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
