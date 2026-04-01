package aprove.verification.oldframework.PropositionalLogic;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.Formulae.*;

public interface FormulaFactory<T> {

    /**
     * @return the next fresh Variable
     */
    Variable<T> buildVariable();

    /**
     * @return a list of numberOfVars fresh Variables
     */
    public abstract List<Variable<T>> buildVariables(int numberOfVars);

    public abstract Constant<T> buildConstant(boolean one);
    public abstract List<TheoryAtom<T>> buildTheoryAtoms(final List<T> t);
    public abstract TheoryAtom<T> buildTheoryAtom(T t);
    public abstract Formula<T> buildAnd(List<? extends Formula<T>> args);
    public abstract Formula<T> buildAnd(Formula<T> f1, Formula<T> f2);
    public abstract Formula<T> buildAnd(Formula<T> f1, Formula<T> f2, Formula<T> f3);
    public abstract Formula<T> buildOr(List<Formula<T>> args);
    public abstract Formula<T> buildOr(Formula<T> f1, Formula<T> f2);
    public abstract Formula<T> buildOr(Formula<T> f1, Formula<T> f2, Formula<T> f3);
    public abstract Formula<T> buildNot(Formula<T> arg);

    /**
     * Note that n-ary xor is true iff <b>an odd number</b> of its arguments
     * is true!
     *
     * @param args
     * @return
     */
    public abstract Formula<T> buildXor(List<Formula<T>> args);
    public abstract Formula<T> buildXor(Formula<T> f1, Formula<T> f2);

    /**
     * Note that ternary xor is true iff <b>1 or 3</b> of its arguments
     * are true!
     *
     * @param f1
     * @param f2
     * @param f3
     * @return
     */
    public abstract Formula<T> buildXor(Formula<T> f1, Formula<T> f2, Formula<T> f3);
    public abstract Formula<T> buildIff(Formula<T> left, Formula<T> right);
    public abstract Formula<T> buildIte(Formula<T> condition,
            Formula<T> thenFormula, Formula<T> elseFormula);
    public abstract Formula<T> buildImplication(Formula<T> left, Formula<T> right);

    /**
     * In general, There is no guarantee that a formula passed on as some
     * argument will actually be included in the final formula that is later
     * converted into CNF and solved by the SAT solver.
     * This method encapsulates a formula in such a way that it will not be
     * optimized away. Benefit: You can then also for sure retrieve the truth
     * value that the SAT solver assigned to the particular encapsulated
     * formula.
     */
    public abstract Formula<T> buildCapsule(Formula<T> capsule);
    /** and, especially relevant for debug purposes with SATView, label this formula.
     */
    public abstract Formula<T> buildLabel(Formula<T> capsule, String label);

    public abstract Formula<T> buildAtLeast(List<Formula<T>> args, int cardinality);
    public abstract Formula<T> buildAtMost(List<Formula<T>> args, int cardinality);
    public abstract Formula<T> buildCount(List<Formula<T>> args, int cardinality);

    public abstract <TT> FormulaFactory<TT> toTheory();
}
