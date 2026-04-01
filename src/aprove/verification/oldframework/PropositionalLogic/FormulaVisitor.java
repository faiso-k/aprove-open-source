package aprove.verification.oldframework.PropositionalLogic;

import aprove.verification.oldframework.PropositionalLogic.Formulae.*;

/**
 * @author nowonder
 * @author fuhs
 * @version $Id$
 *
 * @param <S> - return type of the visitor's methods
 * @param <T> - generic type of the theory atoms
 */
public interface FormulaVisitor<S, T> {

    public S caseAnd(AndFormula<T> f);
    public S caseConstant(Constant<T> f);
    public S caseIff(IffFormula<T> f);
    public S caseIte(IteFormula<T> f);
    public S caseNot(NotFormula<T> f);
    public S caseOr(OrFormula<T> f);
    public S caseTheoryAtom(TheoryAtom<T> f);
    public S caseVariable(Variable<T> f);
    public S caseXor(XorFormula<T> f);

    public S caseAtLeast(AtLeastFormula<T> f);
    public S caseAtMost(AtMostFormula<T> f);
    public S caseCount(CountFormula<T> f);

}
