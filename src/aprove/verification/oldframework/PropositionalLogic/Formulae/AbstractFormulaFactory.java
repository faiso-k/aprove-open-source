package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * Provides some common functionality and attributes for FormulaFactories.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public abstract class AbstractFormulaFactory<T> implements FormulaFactory<T> {

    public final Constant<T> ZERO = new Constant<T>(false);
    public final Constant<T> ONE = new Constant<T>(true);

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.PropositionalLogic.Formulae.FormulaFactory#buildVariable()
     */
    @Override
    public Variable<T> buildVariable() {
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

    @Override
    public Formula<T> buildImplication(Formula<T> left, Formula<T> right) {
        return this.buildOr(this.buildNot(left),right);
    }

    /**
     * Just builds an xor comb from args, does not do any simplification.
     *
     * @param args to be xor-ed, must have at least size 2
     * @return the corresponding xor comb
     */
    protected XorFormula<T> buildXorComb(List<Formula<T>> fmlae) {
        if (Globals.useAssertions) {
            assert fmlae.size() >= 2;
        }

        int size = fmlae.size();
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
    public Formula<T> buildAtLeast(List<Formula<T>> args, int cardinality) {
        return new AtLeastFormula<T>(args, cardinality);
    }

    @Override
    public Formula<T> buildAtMost(List<Formula<T>> args, int cardinality) {
        return new AtMostFormula<T>(args, cardinality);
    }

    @Override
    public Formula<T> buildCount(List<Formula<T>> args, int cardinality) {
        return new CountFormula<T>(args, cardinality);
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
