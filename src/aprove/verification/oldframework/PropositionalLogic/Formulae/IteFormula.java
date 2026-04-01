package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * If condition then thenFormula else elseFormula, i.e.,
 * (condition -> thenFormula) and (not condition -> elseFormula).
 * Preferable over encoding the above by hand since improved encodings
 * of this construct to CNF are employed by SAT4J 1.7.
 *
 * @author Carsten Fuhs
 * @version $Id$
 * @param <T>
 */
public class IteFormula<T> extends JunctorFormula<T> {

    Formula<T> condition;
    Formula<T> thenFormula;
    Formula<T> elseFormula;

    /**
     * @param condition
     * @param thenFormula
     * @param elseFormula
     */
    IteFormula(final Formula<T> condition, final Formula<T> thenFormula,
            final Formula<T> elseFormula) {
        this.condition = condition;
        this.thenFormula = thenFormula;
        this.elseFormula = elseFormula;
    }

    @Override
    public String getJunctor() {
        return "ite";
    }

    @Override
    public void addGates(List<CircuitGate> gates) {
        if (this.id != AbstractFormula.ID_UNSET) {
            gates.add(this.gate);
            this.id = AbstractFormula.ID_UNSET;
            this.condition.addGates(gates);
            this.thenFormula.addGates(gates);
            this.elseFormula.addGates(gates);
        }
    }

    @Override
    public <S> S apply(FormulaVisitor<S, T> visitor) {
        return visitor.caseIte(this);
    }

    @Override
    public <S> S apply(FineGrainedFormulaVisitor<S, T> visitor) {
        S result = visitor.get(this);
        if (result == null) {
            S s1, s2, s3;
            s1 = this.condition.apply(visitor);
            s2 = this.thenFormula.apply(visitor);
            s3 = this.elseFormula.apply(visitor);
            result = visitor.outIte(this, s1, s2, s3);
        }
        return result;
    }


    @Override
    public int countSub() {
        return 1 + this.condition.countSub()
                 + this.thenFormula.countSub()
                 + this.elseFormula.countSub();
    }


    @Override
    public Formula<T> evaluate(ValueCache<T> cache) {
        return cache.getFactory().buildIte(this.condition.evaluate(cache),
                this.thenFormula.evaluate(cache),
                this.elseFormula.evaluate(cache));
    }

    @Override
    public int getGateType() {
        return CircuitGate.IFTHENELSE;
    }

    @Override
    public boolean isLiteral() {
        return false;
    }

    @Override
    public int label(int id) {
        if (this.id == AbstractFormula.ID_UNSET) {
            // not yet labeled with an id -> label children first
            id = this.condition.label(id);
            id = this.thenFormula.label(id);
            id = this.elseFormula.label(id);
            this.gate = CircuitGate.create(CircuitGate.IFTHENELSE, id,
                    new int[] {this.condition.getId(),
                            this.thenFormula.getId(), this.elseFormula.getId()});
            this.id = id++;
        }
        return id;
    }

    @Override
    public String toString() {
        return this.toString(null);
    }

    @Override
    public String toString(Map<? extends AbstractVariable<T>, ?> map) {
        StringBuilder builder = new StringBuilder("ite");
        int id = this.getId();
        if (id != AbstractFormula.ID_UNSET) {
            builder.append("[");
            builder.append(id);
            builder.append("]");
        }
        builder.append("(");
        builder.append(this.condition.toString(map));
        builder.append(", ");
        builder.append(this.thenFormula.toString(map));
        builder.append(", ");
        builder.append(this.elseFormula.toString(map));
        builder.append(")");
        return builder.toString();
    }

    @Override
    public void update(ValueCache<T> cache, boolean one) {}

    public Formula<T> getCondition() {
        return this.condition;
    }

    public Formula<T> getThen() {
        return this.thenFormula;
    }

    public Formula<T> getElse() {
        return this.elseFormula;
    }

    @Override
    public boolean interpret(Set<Integer> trueVars) {
        boolean condTruth = this.condition.interpret(trueVars);
        boolean result = condTruth ?
                this.thenFormula.interpret(trueVars) :
                this.elseFormula.interpret(trueVars);
        return result;
    }
}
