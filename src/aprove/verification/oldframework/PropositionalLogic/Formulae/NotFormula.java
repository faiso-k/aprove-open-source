package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * A formula with a negation at its root.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class NotFormula<T> extends JunctorFormula<T> {

    Formula<T> arg; // the argument of the negation operator

    NotFormula(Formula<T> fml) {
        this.arg = fml;
    }

    public Formula<T> getArg() {
        return this.arg;
    }

    public int getLiteralId() {
        if (Globals.useAssertions) {
            assert this.isLiteral();
        }
        return -this.arg.getId();
    }

    @Override
    public boolean isLiteral() {
        return this.arg.isVariable();
    }

    @Override
    public String getJunctor() {
        return "!";
    }

    @Override
    public String toString() {
        return this.toString(null);
    }

    @Override
    public String toString(Map<? extends AbstractVariable<T>, ?> map) {
        StringBuilder sb = new StringBuilder();
        sb.append(this.getJunctor());
        int id = this.getId();
        if (id != AbstractFormula.ID_UNSET) {
            sb.append("[");
            sb.append(id);
            sb.append("]");
        }
        sb.append(this.arg.toString(map));
        return sb.toString();
    }

    @Override
    public int getGateType() {
        return CircuitGate.NOT;
    }

    @Override
    public int label(int id) {
        if (this.id == AbstractFormula.ID_UNSET) {
            // this is still unlabeled
            id = this.arg.label(id);
            this.gate = CircuitGate.create(CircuitGate.NOT, id, new int[]{this.arg.getId()});
            this.id = id++;
        }
        return id;
    }

    @Override
    public void addGates(List<CircuitGate> gates) {
        if (this.id != AbstractFormula.ID_UNSET) {
            gates.add(this.gate);
            this.id = AbstractFormula.ID_UNSET;
            this.arg.addGates(gates);
        }
    }

    @Override
    public Formula<T> evaluate(ValueCache<T> cache) {
        return cache.getFactory().buildNot(this.arg.evaluate(cache));
    }

    @Override
    public void update(ValueCache<T> cache, boolean one) {
        this.arg.update(cache, !one);
    }

    @Override
    public <S> S apply(FormulaVisitor<S, T> visitor) {
        return visitor.caseNot(this);
    }

    @Override
    public int countSub() {
        return 1+this.arg.countSub();
    }

    @Override
    public <S> S apply(FineGrainedFormulaVisitor<S, T> visitor) {
        S result = visitor.get(this);
        if (result == null) {
            S theS = this.arg.apply(visitor);
            result = visitor.outNot(this, theS);
        }
        return result;

    }

    @Override
    public boolean interpret(Set<Integer> trueVars) {
        boolean argTruth = this.arg.interpret(trueVars);
        return ! argTruth;
    }
}
