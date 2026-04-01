package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * Builds Circuits, that is used subformulae are stored
 * and shared if used again later.
 * One can configure (using strategy) whether to flatten the Circuits,
 * build balanced binary trees, left or right combs, or to use the naive approach.
 * One can specify these parameters for "and" and "or" independently, as well.
 * Note that certain combinations of these do not make sense in combination
 * with certain DimacsCreators.
 *
 * Also counts the number of built subformulae, and destroys itself once a given limit
 * is reached.
 *
 * @author Patrick Kabasci (based on FullSharingFlatteningFactory)
 * @version $Id$
 */
public class CountingCircuitFactory<T> extends AbstractCountingCircuitFactory<T> {

    private SplitMode andMode = SplitMode.FLATTEN;
    private SplitMode orMode = SplitMode.FLATTEN;

    private CountingCircuitFactory(SplitMode andSplit, SplitMode orSplit, int limit) {
        super(limit);
        this.andMode = andSplit;
        this.orMode = orSplit;
    }


    @Override
    public <U> CountingCircuitFactory<U> toTheory() {
        return new CountingCircuitFactory<U>(this.andMode, this.orMode, this.limit);
    }

    public static <U> CountingCircuitFactory<U> create(SplitMode andSplit, SplitMode orSplit, int limit) {
        return new CountingCircuitFactory<U>(andSplit, orSplit, limit);
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
                    Formula<T> res = this.ANDS.get(argsSet);
                    if (Globals.DEBUG_FUHS) {
                        if (res == null) {
                            ++this.andMisses;
                        }
                        else {
                            ++this.andHits;
                        }
                    }
                    if (res == null) {
                        res = new AndFormula<T>(args);
                        this.ANDS.put(argsSet, res);
                        ++this.count;
                        if (this.count > this.limit) {
                            throw new BuiltTooManyException();
                        }
                    }
                    return res;
                }
            } else if (this.andMode == SplitMode.UNFILTERED) {
                Set<Formula<T>> argSet = new LinkedHashSet<Formula<T>>(fmlae);
                Formula<T> res = this.ANDS.get(argSet);
                if (Globals.DEBUG_FUHS) {
                    if (res == null) {
                        ++this.andMisses;
                    }
                    else {
                        ++this.andHits;
                    }
                }
                if (res == null) {
                    res = new AndFormula<T>(fmlae);
                    this.ANDS.put(argSet, res);
                    ++this.count;
                    if (this.count > this.limit) {
                        throw new BuiltTooManyException();
                    }
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
                }

                List<Formula<T>> args = new ArrayList<Formula<T>>(argsSet);
                switch (args.size()) {
                case 0:
                    return this.ONE;
                case 1:
                    return args.get(0);
                case 2:
                    Formula<T> res = this.ANDS.get(argsSet);
                    if (Globals.DEBUG_FUHS) {
                        if (res == null) {
                            ++this.andMisses;
                        }
                        else {
                            ++this.andHits;
                        }
                    }
                    if (res == null) {
                        res = new AndFormula<T>(args);
                        this.ANDS.put(argsSet, res);
                        ++this.count;
                        if (this.count > this.limit) {
                            throw new BuiltTooManyException();
                        }
                    }
                    return res;

                default:
                    // We need to expand the formula (if not yet present).
                    Formula<T> nAryRes = this.ANDS.get(argsSet);
                    if (Globals.DEBUG_FUHS) {
                        if (nAryRes == null) {
                            ++this.andMisses;
                        }
                        else {
                            ++this.andHits;
                        }
                    }
                    if (nAryRes == null) {
                        List<Formula<T>> yRes = new ArrayList<Formula<T>>(argsSet.size());
                        int q = (this.andMode == SplitMode.RIGHT_COMB)? 1: 0;
                        for(int i=q; i < args.size() + q - 1; i++) {
                            yRes.add (args.get(i));
                        }
                        List<Formula<T>> andArgs = new ArrayList<Formula<T>>(2);
                        andArgs.add (args.get((this.andMode == SplitMode.RIGHT_COMB) ?0 :(args.size() -1)));
                        andArgs.add (this.buildAnd(yRes));
                        nAryRes = new AndFormula<T>(andArgs);
                        this.ANDS.put(argsSet, nAryRes);
                        ++this.count;
                        if (this.count > this.limit) {
                            throw new BuiltTooManyException();
                        }
                    }
                    return nAryRes;
                }
            } else {


                // Balanced Tree
                // only necessary to check the elements of fmlae since
                // AndFormula.args.get(k) instanceof AndFormula cannot occur
                Set<Formula<T>> argsSet = new LinkedHashSet<Formula<T>>((fmlae.size()*11)/10);


               /*for (Formula formula : fmlae) {
                    if (formula == this.ZERO) {
                        return formula;
                    }
                } */

                List<Formula<T>> args = new ArrayList<Formula<T>>(argsSet);
                switch (args.size()) {
                case 0:
                    return this.ONE;
                case 1:
                    return args.get(0);
                case 2:
                    Formula<T> res = this.ANDS.get(argsSet);
                    if (Globals.DEBUG_FUHS) {
                        if (res == null) {
                            ++this.andMisses;
                        }
                        else {
                            ++this.andHits;
                        }
                    }
                    if (res == null) {
                        res = new AndFormula<T>(args);
                        this.ANDS.put(argsSet, res);
                    }
                    return res;

                default:
                    // We need to expand the formula (if not yet present).
                    Formula<T> nAryRes = this.ANDS.get(argsSet);
                    if (Globals.DEBUG_FUHS) {
                        if (nAryRes == null) {
                            ++this.andMisses;
                        }
                        else {
                            ++this.andHits;
                        }
                    }
                    if (nAryRes == null) {
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
                        this.ANDS.put(argsSet, nAryRes);
                        ++this.count;
                        if (this.count > this.limit) {
                            throw new BuiltTooManyException();
                        }
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
                    Formula<T> res = this.ORS.get(argsSet);
                    if (Globals.DEBUG_FUHS) {
                        if (res == null) {
                            ++this.orMisses;
                        }
                        else {
                            ++this.orHits;
                        }
                    }
                    if (res == null) {
                        res = new OrFormula<T>(args);
                        this.ORS.put(argsSet, res);
                        ++this.count;
                        if (this.count > this.limit) {
                            throw new BuiltTooManyException();
                        }
                    }
                    return res;
                }
            } else if (this.andMode == SplitMode.UNFILTERED) {
                Set<Formula<T>> argSet = new LinkedHashSet<Formula<T>>(fmlae);
                Formula<T> res = this.ORS.get(argSet);
                if (Globals.DEBUG_FUHS) {
                    if (res == null) {
                        ++this.orMisses;
                    }
                    else {
                        ++this.orHits;
                    }
                }
                if (res == null) {
                    res = new OrFormula<T>(fmlae);
                    this.ORS.put(argSet, res);
                    ++this.count;
                    if (this.count > this.limit) {
                        throw new BuiltTooManyException();
                    }
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
                }

                List<Formula<T>> args = new ArrayList<Formula<T>>(argsSet);
                switch (args.size()) {
                case 0:
                    return this.ZERO;
                case 1:
                    return args.get(0);
                case 2:
                    Formula<T> res = this.ORS.get(argsSet);
                    if (Globals.DEBUG_FUHS) {
                        if (res == null) {
                            ++this.orMisses;
                        }
                        else {
                            ++this.orHits;
                        }
                    }
                    if (res == null) {
                        res = new OrFormula<T>(args);
                        this.ORS.put(argsSet, res);
                        ++this.count;
                        if (this.count > this.limit) {
                            throw new BuiltTooManyException();
                        }
                    }
                    return res;

                default:
                    // We need to expOr the formula (if not yet present).
                    Formula<T> nAryRes = this.ORS.get(argsSet);
                    if (Globals.DEBUG_FUHS) {
                        if (nAryRes == null) {
                            ++this.orMisses;
                        }
                        else {
                            ++this.orHits;
                        }
                    }
                    if (nAryRes == null) {
                        List<Formula<T>> yRes = new ArrayList<Formula<T>>(argsSet.size() / 2 + 1);
                        int q = (this.orMode == SplitMode.RIGHT_COMB) ? 1: 0;
                        for(int i=q; i < args.size() - 1 + q; i++) {
                            yRes.add (args.get(i));
                        }
                        List<Formula<T>> OrArgs = new ArrayList<Formula<T>>(2);
                        OrArgs.add (args.get((this.orMode == SplitMode.RIGHT_COMB) ? 0: (args.size()-1)));
                        OrArgs.add (this.buildOr(yRes));
                        nAryRes = new OrFormula<T>(OrArgs);
                        this.ORS.put(argsSet, nAryRes);
                        ++this.count;
                        if (this.count > this.limit) {
                            throw new BuiltTooManyException();
                        }
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
                }

                List<Formula<T>> args = new ArrayList<Formula<T>>(argsSet);
                switch (args.size()) {
                case 0:
                    return this.ZERO;
                case 1:
                    return args.get(0);
                case 2:
                    Formula<T> res = this.ORS.get(argsSet);
                    if (Globals.DEBUG_FUHS) {
                        if (res == null) {
                            ++this.orMisses;
                        }
                        else {
                            ++this.orHits;
                        }
                    }
                    if (res == null) {
                        res = new OrFormula<T>(args);
                        this.ORS.put(argsSet, res);
                        ++this.count;
                        if (this.count > this.limit) {
                            throw new BuiltTooManyException();
                        }
                    }
                    return res;

                default:
                    // We need to expOr the formula (if not yet present).
                    Formula<T> nAryRes = this.ORS.get(argsSet);
                    if (Globals.DEBUG_FUHS) {
                        if (nAryRes == null) {
                            ++this.orMisses;
                        }
                        else {
                            ++this.orHits;
                        }
                    }
                    if (nAryRes == null) {
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
                        this.ORS.put(argsSet, nAryRes);
                        ++this.count;
                        if (this.count > this.limit) {
                            throw new BuiltTooManyException();
                        }
                    }
                    return nAryRes;
                }
            }
        }
    }
}
