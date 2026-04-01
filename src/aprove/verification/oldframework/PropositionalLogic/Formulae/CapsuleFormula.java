package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * CapsuleFormula encapsules a Formula whose value is interesting for the calculation, avoiding it to be optimized away.
 * Does not contain any logic itself.
 * @author kabasci
 *
 */
public class CapsuleFormula<T> extends AbstractFormula<T> {

    final Formula<T> encapsuledFormula;

    CapsuleFormula(Formula<T> encapsule) {
        this.encapsuledFormula = encapsule;
    }

    @Override
    public void addGates(List<CircuitGate> gates) {
       this.encapsuledFormula.addGates(gates);
    }

    @Override
    public <S> S apply(FormulaVisitor<S, T> visitor) {
        return this.encapsuledFormula.apply(visitor);
    }

    @Override
    public <S> S apply(FineGrainedFormulaVisitor<S, T> visitor) {
        return this.encapsuledFormula.apply(visitor);
    }

    @Override
    public int countSub() {
        return this.encapsuledFormula.countSub();
    }

    @Override
    public Formula<T> evaluate(ValueCache<T> cache) {
        return this.encapsuledFormula.evaluate(cache);
    }

    @Override
    public int getGateType() {
        return this.encapsuledFormula.getGateType();
    }

    @Override
    public int getId() {
        return this.encapsuledFormula.getId();
    }

    @Override
    public boolean isAtomic() {
        return this.encapsuledFormula.isAtomic();
    }

    @Override
    public boolean isConstant() {
        return this.encapsuledFormula.isConstant();
    }

    @Override
    public boolean isLiteral() {
        return this.encapsuledFormula.isLiteral();
    }

    @Override
    public boolean isVariable() {
        return this.encapsuledFormula.isVariable();
    }

    @Override
    public int label(int newId) {
        return this.encapsuledFormula.label(newId);
    }

    @Override
    public String toString(Map<? extends AbstractVariable<T>, ?> map) {
        return this.encapsuledFormula.toString(map);
    }

    @Override
    public String toString() {
        return this.encapsuledFormula.toString();
    }

    @Override
    public void update(ValueCache<T> cache, boolean one) {
        this.encapsuledFormula.update(cache, one);
    }

    public Formula<T> getCapsule() {
        return this.encapsuledFormula;
    }

    @Override
    public boolean interpret(Set<Integer> trueVars) {
        return this.encapsuledFormula.interpret(trueVars);
    }
}
