package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * Builds Formulae, that is used subformulae are *not* stored
 * and shared if used again later.
 * One can configure (using strategy) whether to flatten the Formulae,
 * build balanced binary trees, left or right combs, or to use the naive approach.
 * One can specify these parameters for and and or independantly, as well.
 * Note that certain combinations of these do not make sense in combination
 * with certain DimacsCreators.
 *
 * Also counts the number of built subformulae, and destroys itself once a given limit
 * is reached.
 *
 * Note that - especially using binary trees or combs - that number will grow pretty
 * fast without caching!
 *
 * @author Patrick Kabasci (based on FullSharingFlatteningFactory)
 * @version $Id$
 */
public class CountingFormulaFactory<T> extends AbstractCountingFormulaFactory<T> {

    private static final Logger log = Logger.getLogger("aprove.verification.oldframework.PropositionalLogic.Formulae.CountingFormulaFactory");

    private SplitMode andMode = SplitMode.FLATTEN;
    private SplitMode orMode = SplitMode.FLATTEN;

    private CountingFormulaFactory(SplitMode andSplit, SplitMode orSplit, int limit) {
        super(limit);
        this.andMode = andSplit;
        this.orMode = orSplit;
    }
    @Override
    public <U> CountingFormulaFactory<U> toTheory() {
        return new CountingFormulaFactory<U>(this.andMode, this.orMode, this.limit);
    }
    public static <U> CountingFormulaFactory<U> create(SplitMode andSplit, SplitMode orSplit, int limit) {
        return new CountingFormulaFactory<U>(andSplit, orSplit, limit);
    }

    @Override
    public Formula<T> buildNot(Formula<T> fml) {
        // Same as in FullSharingFlatteningFactory
        if (fml == this.ONE) {
            return this.ZERO;
        }
        if (fml == this.ZERO) {
            return this.ONE;
        }
        if (fml instanceof NotFormula) { // no double negations!
            Formula<T> result = ((NotFormula<T>) fml).arg;
            if (Globals.useAssertions) { // fml is not a double negation, is it?!
                assert !(result instanceof NotFormula);
            }
            return result;
        }
        else {
            NotFormula<T> res;
            res = new NotFormula<T>(fml);
            ++this.count;
            if (this.count > this.limit) {
                throw new BuiltTooManyException();
            }
            return res;

        }
    }


    @Override
    public Formula<T> buildAnd(List<? extends Formula<T>> fmlae) {
        switch (fmlae.size()) {
        case 0:
            return this.ONE;
        case 1:
            return fmlae.get(0);
        default:
            if (this.andMode == SplitMode.FLATTEN) {
                // Flattening
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
                    AndFormula<T> res;
                    res = new AndFormula<T>(args);
                    ++this.count;
                    if (this.count > this.limit) {
                        throw new BuiltTooManyException();
                    }
                    return res;
                }
            } else if (this.andMode == SplitMode.UNFILTERED) {
                AndFormula<T> res;
                res = new AndFormula<T>(fmlae);
                ++this.count;
                if (this.count > this.limit) {
                    throw new BuiltTooManyException();
                }
                return res;
            } else if (this.andMode == SplitMode.RIGHT_COMB || this.andMode == SplitMode.LEFT_COMB) {
                // Comb
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
                    argsSet.add(formula);
                }

                List<Formula<T>> args = new ArrayList<Formula<T>>(argsSet);
                switch (args.size()) {
                case 0:
                    return this.ONE;
                case 1:
                    return args.get(0);
                case 2:
                    AndFormula<T> res;
                    res = new AndFormula<T>(args);
                    ++this.count;
                    if (this.count > this.limit) {
                        throw new BuiltTooManyException();
                    }
                    return res;

                default:
                    // We need to expand the formula (if not yet present).
                    AndFormula<T> nAryRes;
                    List<Formula<T>> yRes = new ArrayList<Formula<T>>(argsSet.size() / 2 + 1);
                    int q = (this.andMode == SplitMode.RIGHT_COMB)? 1: 0;
                    for(int i=q; i < args.size() + q - 1; i++) {
                        yRes.add (args.get(i));
                    }
                    List<Formula<T>> andArgs = new ArrayList<Formula<T>>(2);
                    andArgs.add (args.get((this.andMode == SplitMode.RIGHT_COMB) ?0 :(args.size() -1)));
                    andArgs.add (this.buildAnd(yRes));
                    nAryRes = new AndFormula<T>(andArgs);
                    ++this.count;
                    if (this.count > this.limit) {
                        throw new BuiltTooManyException();
                    }

                    return nAryRes;
                }
            } else {
                // Balanced Tree
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
                    argsSet.add(formula);
                }

                List<Formula<T>> args = new ArrayList<Formula<T>>(argsSet);
                switch (args.size()) {
                case 0:
                    return this.ONE;
                case 1:
                    return args.get(0);
                case 2:
                    AndFormula<T> res;
                    res = new AndFormula<T>(args);
                    return res;

                default:
                    // We need to expand the formula (if not yet present).
                    AndFormula<T> nAryRes;
                    List<Formula<T>> xRes = new ArrayList<Formula<T>>(argsSet.size() / 2 + 1);
                    List<Formula<T>> yRes = new ArrayList<Formula<T>>(argsSet.size() / 2 + 1);
                    for (int i = 0; i < ((args.size() / 2) + args.size() % 2) ; i++ ) {
                        xRes.add( args.get(i));
                    }
                    for(int i=((args.size() / 2) + args.size() % 2); i < args.size(); i++) {
                        yRes.add (args.get(i));
                    }
                    List<Formula<T>> andArgs = new ArrayList<Formula<T>>(2);
                    andArgs.add (this.buildAnd(xRes));
                    andArgs.add (this.buildAnd(yRes));
                    nAryRes = new AndFormula<T>(andArgs);
                    ++this.count;
                    if (this.count > this.limit) {
                        throw new BuiltTooManyException();
                    }

                    return nAryRes;
                }

            }

        }
    }

    @Override
    public Formula<T> buildOr(List<Formula<T>> fmlae) {
        switch (fmlae.size()) {
        case 0:
            return this.ZERO;
        case 1:
            return fmlae.get(0);
        default:
            if (this.orMode == SplitMode.FLATTEN) {
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
                    OrFormula<T> res;
                    res = new OrFormula<T>(args);
                    ++this.count;
                    if (this.count > this.limit) {
                        throw new BuiltTooManyException();
                    }

                    return res;
                }
            } else if (this.andMode == SplitMode.UNFILTERED) {
                OrFormula<T> res;
                res = new OrFormula<T>(fmlae);
                ++this.count;
                if (this.count > this.limit) {
                    throw new BuiltTooManyException();
                }

                return res;
            } else if ((this.orMode == SplitMode.RIGHT_COMB) || (this.orMode == SplitMode.LEFT_COMB)) {
                // Comb
                // only necessary to check the elements of fmlae since
                // OrFormula.args.get(k) instanceof OrFormula cannot occur
                Set<Formula<T>> argsSet = new LinkedHashSet<Formula<T>>((fmlae.size()*11)/10);
                for (Formula<T> formula : fmlae) {
                    if (formula == this.ONE) {
                        return formula;
                    }
                    if (formula == this.ZERO) {
                        continue;
                    }
                    argsSet.add(formula);
                }

                List<Formula<T>> args = new ArrayList<Formula<T>>(argsSet);
                switch (args.size()) {
                case 0:
                    return this.ZERO;
                case 1:
                    return args.get(0);
                case 2:
                    OrFormula<T> res;
                    res = new OrFormula<T>(args);
                    ++this.count;
                    if (this.count > this.limit) {
                        throw new BuiltTooManyException();
                    }

                    return res;

                default:
                    // We need to expOr the formula (if not yet present).
                    OrFormula<T> nAryRes;
                    List<Formula<T>> yRes = new ArrayList<Formula<T>>(argsSet.size() / 2 + 1);
                    int q = (this.orMode == SplitMode.RIGHT_COMB) ? 1: 0;
                    for(int i=q; i < args.size() - 1 + q; i++) {
                        yRes.add (args.get(i));
                    }
                    List<Formula<T>> OrArgs = new ArrayList<Formula<T>>(2);
                    OrArgs.add (args.get((this.orMode == SplitMode.RIGHT_COMB) ? 0: (args.size()-1)));
                    OrArgs.add (this.buildOr(yRes));
                    nAryRes = new OrFormula<T>(OrArgs);
                    ++this.count;
                    if (this.count > this.limit) {
                        throw new BuiltTooManyException();
                    }
                    return nAryRes;
                }
            } else {
                // Balanced tree
                // only necessary to check the elements of fmlae since
                // OrFormula.args.get(k) instanceof OrFormula cannot occur
                Set<Formula<T>> argsSet = new LinkedHashSet<Formula<T>>((fmlae.size()*11)/10);
                for (Formula<T> formula : fmlae) {
                    if (formula == this.ONE) {
                        return formula;
                    }
                    if (formula == this.ZERO) {
                        continue;
                    }
                    argsSet.add(formula);
                }

                List<Formula<T>> args = new ArrayList<Formula<T>>(argsSet);
                switch (args.size()) {
                case 0:
                    return this.ZERO;
                case 1:
                    return args.get(0);
                case 2:
                    OrFormula<T> res;
                    res = new OrFormula<T>(args);
                    ++this.count;
                    if (this.count > this.limit) {
                        throw new BuiltTooManyException();
                    }

                    return res;

                default:
                    // We need to expand the formula.
                    OrFormula<T> nAryRes;
                    List<Formula<T>> xRes = new ArrayList<Formula<T>>(argsSet.size() / 2 + 1);
                    List<Formula<T>> yRes = new ArrayList<Formula<T>>(argsSet.size() / 2 + 1);
                    for (int i = 0; i < ((args.size() / 2) + args.size() % 2) ; i++ ) {
                        xRes.add( args.get(i));
                    }
                    for(int i=((args.size() / 2) + args.size() % 2); i < args.size(); i++) {
                        yRes.add (args.get(i));
                    }
                    List<Formula<T>> OrArgs = new ArrayList<Formula<T>>(2);
                    OrArgs.add (this.buildOr(xRes));
                    OrArgs.add (this.buildOr(yRes));
                    nAryRes = new OrFormula<T>(OrArgs);
                    ++this.count;
                    if (this.count > this.limit) {
                        throw new BuiltTooManyException();
                    }

                    return nAryRes;
                }
            }
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
            Set<Formula<T>> argsSet = new LinkedHashSet<Formula<T>>(2);
            argsSet.add(f1);
            argsSet.add(f2);
            XorFormula<T> result;
            List<Formula<T>> args = new ArrayList<Formula<T>>(2);
            args.add(f1);
            args.add(f2);
            result = new XorFormula<T>(args);
            ++this.count;
            if (this.count > this.limit) {
                throw new BuiltTooManyException();
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
            XorFormula<T> result;
            // for the lower part of the comb
            Set<Formula<T>> lowerArgsSet = new LinkedHashSet<Formula<T>>(2);
            lowerArgsSet.add(f1);
            lowerArgsSet.add(f2);
            XorFormula<T> resultLower;
            List<Formula<T>> lowerArgs = new ArrayList<Formula<T>>(2);
            lowerArgs.add(f1);
            lowerArgs.add(f2);
            resultLower = new XorFormula<T>(lowerArgs);
            ++this.count;
            if (this.count > this.limit) {
                throw new BuiltTooManyException();
            }
            List<Formula<T>> args = new ArrayList<Formula<T>>(2);
            args.add(resultLower);
            args.add(f3);
            result = new XorFormula<T>(args);
            ++this.count;
            if (this.count > this.limit) {
                throw new BuiltTooManyException();
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
            // at least 4 fmlae; unlikely to happen
            // -> no result caching here for now, TODO take care of that
            //    iff it ever turn out to be used
            if (Globals.DEBUG_FUHS) {
                CountingFormulaFactory.log.log(Level.FINE, "******** Entered buildXor(...) with a list of " + size + " formulae as arg ********\n");
            }

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

            // now just build the formula without caching it and return it
            switch (argsSize) {
            case 1:
                return args.get(0);
            case 2:
                ++this.count;
                if (this.count > this.limit) {
                    throw new BuiltTooManyException();
                }
                return new XorFormula<T>(args);

            default:
                // xor combs are preferrable to flattened XorFormulae
                // because of the way Tseitin's algorithm works on XOR
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
        IffFormula<T> res;
        res = new IffFormula<T>(left, right);
        ++this.count;
        if (this.count > this.limit) {
            throw new BuiltTooManyException();
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
        IteFormula<T> res = new IteFormula<T>(condition, thenFormula, elseFormula);
        ++this.count;
        if (this.count > this.limit) {
            throw new BuiltTooManyException();
        }
        return res;
    }

    @Override
    public Formula<T> buildAtLeast(List<Formula<T>> args, int cardinality) {
        ++this.count;
        if (this.count > this.limit) {
            throw new BuiltTooManyException();
        }
        return new AtLeastFormula<T>(args, cardinality);
    }

    @Override
    public Formula<T> buildAtMost(List<Formula<T>> args, int cardinality) {
        ++this.count;
        if (this.count > this.limit) {
            throw new BuiltTooManyException();
        }
        return new AtMostFormula<T>(args, cardinality);
    }

    @Override
    public Formula<T> buildCount(List<Formula<T>> args, int cardinality) {
        ++this.count;
        if (this.count > this.limit) {
            throw new BuiltTooManyException();
        }
        return new CountFormula<T>(args, cardinality);
    }
}
