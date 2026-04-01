package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

/**
 * Extracts exactly those theory atoms where between the atom and the root
 * of the formula there are only AndFormula nodes. In other words, extracts
 * those theory atoms that will by necessity hold in all models (and can
 * thus be used for further deductions that may simplify the task for the
 * solver). These atoms then correspond to "global" constraints.
 *
 * @author fuhs
 *
 * @param <T>
 */
public class GlobalAtomExtractor<T> extends MemorizingDepthFirstFormulaVisitor<T> {

    private Set<T> result;

    public GlobalAtomExtractor() {
        this.result = new LinkedHashSet<T>();
    }

    /**
     * @return the encapsulated set of theory propositions - handle with care
     */
    public Set<T> getResult() {
        return this.result;
    }

    // The following method is very consciously not overridden
    //public Object caseAnd(AndFormula<T> f)

    @Override
    public Object caseTheoryAtom(TheoryAtom<T> f) {
        if (this.visited.contains(f)) {return null;} else {this.visited.add(f);}
        this.result.add(f.getProposition());
        return null;
    }

    // on all other formula types conveniently ignore the children

    @Override
    public Object caseConstant(Constant<T> f) {
        return null;
    }

    @Override
    public Object caseIff(IffFormula<T> f) {
        return null;
    }

    @Override
    public Object caseIte(IteFormula<T> f) {
        return null;
    }

    @Override
    public Object caseNot(NotFormula<T> f) {
        return null;
    }

    @Override
    public Object caseOr(OrFormula<T> f) {
        return null;
    }

    @Override
    public Object caseVariable(Variable<T> f) {
        return null;
    }

    @Override
    public Object caseXor(XorFormula<T> f) {
        return null;
    }

    @Override
    public Object caseAtLeast(AtLeastFormula<T> f) {
        return null;
    }

    @Override
    public Object caseAtMost(AtMostFormula<T> f) {
        return null;
    }

    @Override
    public Object caseCount(CountFormula<T> f) {
        return null;
    }
}
