package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * The only purpose of the labeled Formula is to provide a description for
 * SAT debugging.
 * Unlike a capsule, it is not guaranteed to persist!
 * CNF generation will ignore it to the point of joining appropriate subformulae.
 * @author patrick
 *
 */
public class LabelFormula<T> extends AbstractFormula<T> implements NamedFormula {

    final Formula<T> encapsuledFormula;

    String description = "<>";

    LabelFormula(Formula<T> encapsule, String description) {
        this.encapsuledFormula = encapsule;
        this.description = description;
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
    public String getDescription() {
        return this.description;
    }

    @Override
    public String getType() {
        // TODO Auto-generated method stub
        return "LABEL";
    }

    @Override
    public void setDescription(String description) {
        this.description = description;
    }

    @Override
    public boolean interpret(Set<Integer> trueVars) {
        return this.encapsuledFormula.interpret(trueVars);
    }
}
