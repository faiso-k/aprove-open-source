package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * Atomic propositions over some theory.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class TheoryAtom<T> extends Variable<T> {

    private T proposition;

    TheoryAtom(T t) {
        this.proposition = t;
    }

    @Override
    public boolean isTheoryAtom() {
        return true;
    }

    @Override
    public boolean isVariable() {
        return true;
    }

    @Override
    public boolean isConstant() {
        return false;
    }

    @Override
    public boolean isLiteral() {
        return true;
    }

    @Override
    public String toString() {
        return this.proposition.toString();
    }

    @Override
    public String toString(Map<? extends AbstractVariable<T>, ?> map) {
        Object o;
        if (map == null) {
            o = this;
        } else {
            o = map.get(this);
            if (o == null) {
                o = this;
            }
        }
        return o.toString();
    }

    @Override
    public int getGateType() {
        throw new UnsupportedOperationException("TheoryAtoms do not have a gate type!");
    }

    @Override
    public void addGates(List<CircuitGate> gates) {}
    // nothing to add, and the id of a variable is not changed here either

    @Override
    public <S> S apply(FormulaVisitor<S, T> visitor) {
        return visitor.caseTheoryAtom(this);
    }

    @Override
    public <S> S apply(FineGrainedFormulaVisitor<S, T> visitor) {
        S result = visitor.get(this);
        if (result == null) {
            result = visitor.outTheoryAtom(this);
        }
        return result;
    }

    public T getProposition() {
        return this.proposition;
    }

    @Override
    public boolean interpret(Set<Integer> trueVars) {
        throw new RuntimeException("Interpreting like this only works for formulae without theory atoms!");
    }
}
