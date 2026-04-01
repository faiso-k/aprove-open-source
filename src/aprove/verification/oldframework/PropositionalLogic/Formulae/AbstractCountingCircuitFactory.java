package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public abstract class AbstractCountingCircuitFactory<T> extends
        AbstractCountingFormulaFactory<T> {

    private static final Logger log = Logger.getLogger("aprove.verification.oldframework.PropositionalLogic.Formulae.AbstractCountingCircuitFactory");

    // circuit caches
    protected final Map<Formula<T>, Formula<T>> NOTS = new HashMap<Formula<T>, Formula<T>>();
    protected final Map<Set<Formula<T>>, Formula<T>> ANDS = new HashMap<Set<Formula<T>>, Formula<T>>();
    protected final Map<Set<Formula<T>>, Formula<T>> ORS = new HashMap<Set<Formula<T>>, Formula<T>>();
    protected final Map<Set<Formula<T>>, Formula<T>> XORS = new HashMap<Set<Formula<T>>, Formula<T>>();
    protected final Map<Pair<Formula<T>, Formula<T>>, Formula<T>> IFFS = new HashMap<Pair<Formula<T>, Formula<T>>, Formula<T>>();
    protected final Map<Triple<Formula<T>, Formula<T>, Formula<T>>, Formula<T>> ITES = new HashMap<Triple<Formula<T>, Formula<T>, Formula<T>>, Formula<T>>();
    protected final Map<Pair<MultiSet<Formula<T>>, Integer>, Formula<T>> ATLEASTS = new HashMap<Pair<MultiSet<Formula<T>>, Integer>, Formula<T>>();
    protected final Map<Pair<MultiSet<Formula<T>>, Integer>, Formula<T>> ATMOSTS = new HashMap<Pair<MultiSet<Formula<T>>, Integer>, Formula<T>>();
    protected final Map<Pair<MultiSet<Formula<T>>, Integer>, Formula<T>> COUNTS = new HashMap<Pair<MultiSet<Formula<T>>, Integer>, Formula<T>>();
    protected final Map<T, TheoryAtom<T>> THEORY_ATOMS = new HashMap<T, TheoryAtom<T>>();

    // evaluate which caches are actually used productively
    public int notHits = 0;
    public int notMisses = 0;
    public int andHits = 0;
    public int andMisses = 0;
    public int orHits = 0;
    public int orMisses = 0;
    public int xorHits = 0;
    public int xorMisses = 0;
    public int iffHits = 0;
    public int iffMisses = 0;
    public int theoryHits = 0;
    public int theoryMisses = 0;

    /**
     * @param limit maximum number of formulae this factory will build,
     *  must be at least 2 (ZERO and ONE will always be built)
     */
    public AbstractCountingCircuitFactory(int limit) {
        super(limit);
    }

    @Override
    public TheoryAtom<T> buildTheoryAtom(T t) {
        TheoryAtom<T> res = this.THEORY_ATOMS.get(t);
        if (Globals.DEBUG_FUHS) {
            if (res == null) {
                ++this.theoryMisses;
            }
            else {
                ++this.theoryHits;
            }
        }
        if (res == null) {
            res = new TheoryAtom<T>(t);
            this.THEORY_ATOMS.put(t, res);
        }
        return res;
    }

    @Override
    public Formula<T> buildNot(Formula<T> fml) {
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
            Formula<T> res = this.NOTS.get(fml);
            if (Globals.DEBUG_FUHS) {
                if (res == null) {
                    ++this.notMisses;
                }
                else {
                    ++this.notHits;
                }
            }
            if (res == null) {
                ++this.count;
                if (this.count > this.limit) {
                    throw new BuiltTooManyException();
                }
                res = new NotFormula<T>(fml);
                this.NOTS.put(fml, res);
            }
            return res;
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
                ++this.count;
                if (this.count > this.limit) {
                    throw new BuiltTooManyException();
                }
                List<Formula<T>> args = new ArrayList<Formula<T>>(2);
                args.add(f1);
                args.add(f2);
                result = new XorFormula<T>(args);
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
                // for the lower part of the comb
                Set<Formula<T>> lowerArgsSet = new LinkedHashSet<Formula<T>>(2);
                lowerArgsSet.add(f1);
                lowerArgsSet.add(f2);
                Formula<T> resultLower = this.XORS.get(lowerArgsSet);
                if (Globals.DEBUG_FUHS) {
                    if (resultLower == null) {
                        ++this.xorMisses;
                    }
                    else {
                        ++this.xorHits;
                    }
                }
                if (resultLower == null) {
                    ++this.count;
                    if (this.count > this.limit) {
                        throw new BuiltTooManyException();
                    }
                    List<Formula<T>> lowerArgs = new ArrayList<Formula<T>>(2);
                    lowerArgs.add(f1);
                    lowerArgs.add(f2);
                    resultLower = new XorFormula<T>(lowerArgs);
                    this.XORS.put(lowerArgsSet, resultLower);
                }
                ++this.count;
                if (this.count > this.limit) {
                    throw new BuiltTooManyException();
                }
                List<Formula<T>> args = new ArrayList<Formula<T>>(2);
                args.add(resultLower);
                args.add(f3);
                result = new XorFormula<T>(args);
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
            // at least 4 fmlae; unlikely to happen
            // -> no result caching here for now, TODO take care of that
            //    iff it ever turn out to be used
            if (Globals.DEBUG_FUHS) {
                AbstractCountingCircuitFactory.log.log(Level.FINE, "******** Entered buildXor(...) with a list of " + size + " formulae as arg ********\n");
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
            ++this.count;
            if (this.count > this.limit) {
                throw new BuiltTooManyException();
            }
            res = new IffFormula<T>(left, right);
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
            res = new IteFormula<T>(condition, thenFormula, elseFormula);
            this.ITES.put(lr, res);
            ++this.count;
            if (this.count > this.limit) {
                throw new BuiltTooManyException();
            }
        }
        return res;
    }

    @Override
    public Formula<T> buildAtLeast(List<Formula<T>> fmlae, int cardinality) {
        if (Globals.useAssertions) {
            assert cardinality >= 0;
        }
        if (cardinality <= 0) {
            return this.ONE;
        }
        final int fmlaeSize = fmlae.size();
        if (cardinality > fmlaeSize) {
            return this.ZERO;
        }

        switch (fmlaeSize) {
        case 0: // cardinality == 0 has already been ruled out!
            return this.ZERO;
        case 1:
            return cardinality == 1 ? fmlae.get(0) : this.ZERO;
        default:
            MultiSet<Formula<T>> argsMultiSet = new HashMultiSet<Formula<T>>((fmlae.size()*11)/10);
            for (Formula<T> formula : fmlae) {
                if (formula == this.ZERO) {
                    continue;
                }
                if (formula == this.ONE) {
                    cardinality--;
                    continue;
                }
                argsMultiSet.add(formula);
            }
            // cardinality may well have a negative value now
            if (cardinality <= 0) {
                return this.ONE;
            }
            List<Formula<T>> args = argsMultiSet.toList();
            switch (args.size()) {
            case 0: // again, cardinality == 0 has already been ruled out!
                return this.ZERO;
            case 1:
                return cardinality == 1 ? args.get(0) : this.ZERO;
            default:
                Pair<MultiSet<Formula<T>>, Integer> argsMultiSetWithCard =
                    new Pair<MultiSet<Formula<T>>, Integer>(argsMultiSet,
                            cardinality);
                Formula<T> res = this.ATLEASTS.get(argsMultiSetWithCard);
                if (res == null) {
                    ++this.count;
                    if (this.count > this.limit) {
                        throw new BuiltTooManyException();
                    }
                    res = new AtLeastFormula<T>(args, cardinality);
                    this.ATLEASTS.put(argsMultiSetWithCard, res);
                }
                return res;
            }
        }
    }

    @Override
    public Formula<T> buildAtMost(List<Formula<T>> fmlae, int cardinality) {
        final int fmlaeSize = fmlae.size();
        if (fmlaeSize <= cardinality) {
            return this.ONE;
        }

        // "at most k (x_1, ... x_n)" holds iff
        // "at least (n-k) (-x_1, ..., -x_n)" holds
        List<Formula<T>> notFmlae = new ArrayList<Formula<T>>(fmlaeSize);
        for (Formula<T> f : fmlae) {
            notFmlae.add(this.buildNot(f));
        }
        Formula<T> res = this.buildAtLeast(notFmlae, fmlaeSize - cardinality);
        return res;
    }

    @Override
    public Formula<T> buildCount(List<Formula<T>> fmlae, int cardinality) {
        Formula<T> atLeastFml = this.buildAtLeast(fmlae, cardinality);
        Formula<T> atMostFml = this.buildAtMost(fmlae, cardinality);
        Formula<T> bothFml = this.buildAnd(atLeastFml, atMostFml);
        return bothFml;
    }
}
