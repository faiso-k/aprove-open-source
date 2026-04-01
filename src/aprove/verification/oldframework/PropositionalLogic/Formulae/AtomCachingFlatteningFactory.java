package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * Builds flattened Formulae. That is, no FooFormula is an argument of
 * another FooFormula. The only exception are cardinality formulae and
 * also XorFormulae because they are best stored in combs (every Xor
 * only gets two arguments, one of which may be another Xor) because
 * of the way Tseitin's algorithm works.
 *
 * @author Peter Schneider-Kamp, Carsten Fuhs
 * @version $Id$
 */
public class AtomCachingFlatteningFactory<T> extends AbstractFormulaFactory<T> {

    @Override
    public Formula<T> buildAnd(List<? extends Formula<T>> fmlae) {
        switch (fmlae.size()) {
        case 0:
            return this.ONE;
        case 1:
            return fmlae.get(0);
        default:
            // only necessary to check the elements of fmlae since
            // AndFormula.args.get(k) instanceof AndFormula cannot occur
            Set<Formula<T>> argsSet = new LinkedHashSet<Formula<T>>((fmlae.size()*11)/10);
            for (Formula<T> formula : fmlae) {
                if (formula == this.ZERO) {
                    return formula;
                }
                if (formula == this.ONE) {
                    continue;
                }
                if (formula instanceof AndFormula) {
                    AndFormula<T> andFormula = (AndFormula<T>) formula;
                    argsSet.addAll(andFormula.args);
                } else {
                    argsSet.add(formula);
                }
            }
            List<Formula<T>> args = new ArrayList<Formula<T>>(argsSet);
            switch (args.size()) {
            case 0:
                return this.ONE;
            case 1:
                return args.get(0);
            default:
                return new AndFormula<T>(args);
            }
        }
    }


    @Override
    public <U> FormulaFactory<U> toTheory() {
        return new AtomCachingFlatteningFactory<U>();
    }

    @Override
    public Formula<T> buildOr(List<Formula<T>> fmlae) {
        switch (fmlae.size()) {
        case 0:
            return this.ZERO;
        case 1:
            return fmlae.get(0);
        default:
            // only necessary to check the elements of fmlae since
            // OrFormula.args.get(k) instanceof OrFormula cannot occur
            Set<Formula<T>> argsSet = new LinkedHashSet<Formula<T>>((fmlae.size()*11)/10);
            for (Formula<T> formula : fmlae) {
                if (formula == this.ZERO) {
                    continue;
                }
                if (formula == this.ONE) {
                    return formula;
                }
                if (formula instanceof OrFormula) {
                    OrFormula<T> orFormula = (OrFormula<T>) formula;
                    argsSet.addAll(orFormula.args);
                } else {
                    argsSet.add(formula);
                }
            }
            List<Formula<T>> args = new ArrayList<Formula<T>>(argsSet);
            switch (args.size()) {
            case 0:
                return this.ZERO;
            case 1:
                return args.get(0);
            default:
                return new OrFormula<T>(args);
            }
        }
    }

    @Override
    public Formula<T> buildNot(Formula<T> fml) {
        if (fml == this.ONE) {
            return this.ZERO;
        }
        if (fml == this.ZERO) {
            return this.ONE;
        }
        if (fml instanceof NotFormula) { // avoid double negations
            return ((NotFormula<T>) fml).arg;
        }
        else {
            return new NotFormula<T>(fml);
        }
    }

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
            List<Formula<T>> args = new ArrayList<Formula<T>>(2);
            args.add(f1);
            args.add(f2);
            return new XorFormula<T>(args);
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
        else { // build a comb: ((f1 xor f2) xor f3)

            // for the lower part of the comb
            List<Formula<T>> lowerArgs = new ArrayList<Formula<T>>(2);
            lowerArgs.add(f1);
            lowerArgs.add(f2);
            XorFormula<T> resultLower = new XorFormula<T>(lowerArgs);

            List<Formula<T>> args = new ArrayList<Formula<T>>(2);
            args.add(resultLower);
            args.add(f3);
            return new XorFormula<T>(args);
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
        case 2:
            return this.buildXor(fmlae.get(0), fmlae.get(1));
        case 3:
            return this.buildXor(fmlae.get(0), fmlae.get(1), fmlae.get(2));
        default:
            Set<Formula<T>> argsSet = new LinkedHashSet<Formula<T>>(fmlae);
            boolean even = true; // even number of ONEs seen so far
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

            // All right, we have at least one argument.
            List<Formula<T>> args = new ArrayList<Formula<T>>(argsSet);
            if (! even) {
                Formula<T> notArg0 = this.buildNot(args.get(0));
                args.set(0, notArg0);
            }

            switch (argsSize) {
            case 1:
                return args.get(0);
            default:
                // Be careful, flattening XorFormulae is not a good idea.
                // Tseitin's algorithm runs /much/ slower on XorFormulae
                // with many arguments. Instead, explicitly build a
                // comb-like structure such that any XorFormula will
                // only have two arguments.
                return this.buildXorComb(args);
            }
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
        return new IffFormula<T>(left, right);
    }

    @Override
    public Formula<T> buildIte(Formula<T> condition, Formula<T> thenFormula, Formula<T> elseFormula) {
        if (condition == this.ZERO) {
            return elseFormula;
        }
        if (condition == this.ONE || thenFormula == elseFormula) {
            return thenFormula;
        }
        return new IteFormula<T>(condition, thenFormula, elseFormula);
    }
}
