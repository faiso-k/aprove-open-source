package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * Provides some common functionality and attributes for
 * CountingFormulaFactories.
 *
 * User beware, when it is attempted to *actually* build more than limit
 * Formula objects (returning cached formulae != building) with an instance
 * of an implementing class, a BuiltTooManyException will be thrown.
 *
 * Note to implementors:
 * We (usually) take care of increasing the count and (if necessary) of
 * throwing the BuiltTooManyException right before calling "new FooFormula(...)",
 * so do not increment the count if you do not actually invoke
 * "new FooFormula(...)".
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public abstract class AbstractCountingFormulaFactory<T> implements aprove.verification.oldframework.PropositionalLogic.CountingFormulaFactory<T> {

    public final Constant<T> ZERO = new Constant<T>(false);
    public final Constant<T> ONE = new Constant<T>(true);

    protected int count;
    protected final int limit;
    // maximum number of formulae this factory will build;
    // refuse afterwards. for this. we throw a BuiltTooManyException.

    /**
     * @param limit maximum number of formulae this factory will build,
     *  must be at least 2 (ZERO and ONE will always be built)
     */
    public AbstractCountingFormulaFactory(int limit) {
        if (Globals.useAssertions) {
            assert limit >= 2; // pointless otherwise
        }
        this.limit = limit;
        this.count = 2; // ZERO and ONE have been built already
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.PropositionalLogic.Formulae.FormulaFactory#buildVariable()
     */
    @Override
    public Variable<T> buildVariable() {
        ++this.count;
        if (this.count > this.limit) {
            throw new BuiltTooManyException();
        }
        return new Variable<T>();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.PropositionalLogic.Formulae.FormulaFactory#buildVariables(int)
     */
    @Override
    public List<Variable<T>> buildVariables(int numberOfVars) {
        List<Variable<T>> result;
        result = new ArrayList<Variable<T>>(numberOfVars);
        for (int i = 0; i < numberOfVars; ++i) {
            result.add(this.buildVariable());
        }
        return result;
    }

    @Override
    public Constant<T> buildConstant(boolean one) {
        return one ? this.ONE : this.ZERO;
    }

    @Override
    public TheoryAtom<T> buildTheoryAtom(T t) {
        ++this.count;
        if (this.count > this.limit) {
            throw new BuiltTooManyException();
        }
        return new TheoryAtom<T>(t);
    }

    @Override
    public List<TheoryAtom<T>> buildTheoryAtoms(final List<T> t) {
        final List<TheoryAtom<T>> res = new LinkedList<TheoryAtom<T>>();
        for (final T a : t) {
            res.add(this.buildTheoryAtom(a));
        }
        return res;
    }

    @Override
    public Formula<T> buildAnd(final Formula<T> f1, final Formula<T> f2) {
        final List<Formula<T>> args = new ArrayList<Formula<T>>(2);
        args.add(f1);
        args.add(f2);
        return this.buildAnd(args);
    }

    @Override
    public Formula<T> buildAnd(Formula<T> f1, Formula<T> f2, Formula<T> f3) {
        List<Formula<T>> args = new ArrayList<Formula<T>>(3);
        args.add(f1);
        args.add(f2);
        args.add(f3);
        return this.buildAnd(args);
    }

    @Override
    public Formula<T> buildOr(Formula<T> f1, Formula<T> f2) {
        List<Formula<T>> args = new ArrayList<Formula<T>>(2);
        args.add(f1);
        args.add(f2);
        return this.buildOr(args);
    }

    @Override
    public Formula<T> buildOr(Formula<T> f1, Formula<T> f2, Formula<T> f3) {
        List<Formula<T>> args = new ArrayList<Formula<T>>(3);
        args.add(f1);
        args.add(f2);
        args.add(f3);
        return this.buildOr(args);
    }

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

    /**
     * Just builds an xor comb from args, does not do any simplification.
     *
     * @param args to be xor-ed, must have at least size 2
     * @return the corresponding xor comb
     */
    protected XorFormula<T> buildXorComb(List<Formula<T>> fmlae) {
        int size = fmlae.size();
        if (Globals.useAssertions) {
            assert size >= 2;
        }
        this.count += size - 1;
        if (this.count > this.limit) {
            throw new BuiltTooManyException();
        }
        XorFormula<T> result;
        List<Formula<T>> args;
        args = new ArrayList<Formula<T>>(2);
        args.add(fmlae.get(0));
        args.add(fmlae.get(1));
        result = new XorFormula<T>(args);
        for (int i = 2; i < size; ++i) {
            args = new ArrayList<Formula<T>>(2);
            args.add(result);
            args.add(fmlae.get(i));
            result = new XorFormula<T>(args);
        }
        return result;
    }

    @Override
    public Formula<T> buildImplication(Formula<T> left, Formula<T> right) {
        return this.buildOr(this.buildNot(left),right);
    }

    @Override
    public CapsuleFormula<T> buildCapsule(Formula<T> capsule) {
        return new CapsuleFormula<T>(capsule);
    }

    @Override
    public Formula<T> buildLabel(Formula<T> capsule, String label) {
        if (Globals.createSatViewLabels) {
            return new LabelFormula<T>(capsule, label);
        } else {
            return capsule;
        }
    }
}
