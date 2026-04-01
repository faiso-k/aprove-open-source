package aprove.verification.oldframework.PropositionalLogic;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.Formulae.*;

public interface FineGrainedFormulaVisitor<S, T> {

    /**
     * If get() returns null, a visit is performed, otherwise the object
     * returned by get() is returned when the visitor is applied.
     *
     * @param f - might be mapped to s.th. by the visitor
     * @return the value f is mapped to (null if there is no such value)
     */
    public S get(Formula<T> f);

    // maybe add in* as well, maybe someone needs them.

    public S outAnd(AndFormula<T> f, List<S> l);
    public S outConstant(Constant<T> f);
    public S outIff(IffFormula<T> f, S g1, S g2);
    public S outIte(IteFormula<T> f, S g1, S g2, S g3);
    public S outNot(NotFormula<T> f, S g);
    public S outOr(OrFormula<T> f, List<S> l);
    public S outTheoryAtom(TheoryAtom<T> f);
    public S outVariable(Variable<T> f);
    public S outXor(XorFormula<T> f, List<S> l);

    public S outAtLeast(AtLeastFormula<T> f, List<S> l);
    public S outAtMost(AtMostFormula<T> f, List<S> l);
    public S outCount(CountFormula<T> f, List<S> l);
}
