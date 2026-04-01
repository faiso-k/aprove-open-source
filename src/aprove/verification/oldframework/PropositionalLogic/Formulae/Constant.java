package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * The boolean literals 0 and 1.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class Constant<T> extends Atom<T> {

    private boolean value; // true means 1; false means 0

    Constant(boolean isTrue) {
        this.value = isTrue;
        this.id = AbstractFormula.ID_UNSET;
        this.gate = null;
    }

    @Override
    public boolean isConstant() {
        return true;
    }

    @Override
    public boolean isVariable() {
        return false;
    }

    @Override
    public boolean isLiteral() {
        return false;
    }

    @Override
    public String toString() {
        return (this.value ? "T" : "F");
    }

    @Override
    public String toString(Map<? extends AbstractVariable<T>, ?> map) {
        return this.toString();
    }

    @Override
    public int getId() {
        int result = this.id;
        if ((result == AbstractFormula.ID_UNSET) && (this.gate != null)) {
            return this.gate.output;
        }
        return result;
    }

    @Override
    public int getGateType() {
        return (this.value ? CircuitGate.TRUE : CircuitGate.FALSE);
    }

    public boolean getValue() {
        return this.value;
    }

    @Override
    public int label(int id) {
        if (this.id == AbstractFormula.ID_UNSET) {
            // this has not yet been labeled
            this.gate = CircuitGate.create(this.getGateType(), id,
                    CircuitGate.NO_INPUTS);
            this.id = id++;
        }
        return id;
    }

    @Override
    public void addGates(List<CircuitGate> gates) {
        if (this.id != AbstractFormula.ID_UNSET) {
            gates.add(this.gate);
            this.id = AbstractFormula.ID_UNSET;
        }
    }

    @Override
    public Formula<T> evaluate(ValueCache<T> cache) {
        return this;
    }

    @Override
    public void update(ValueCache<T> cache, boolean one) {}

    @Override
    public <S> S apply(FormulaVisitor<S, T> visitor) {
        return visitor.caseConstant(this);
    }

    @Override
    public <S> S apply(FineGrainedFormulaVisitor<S, T> visitor) {
        S result = visitor.get(this);
        if (result == null) {
            result = visitor.outConstant(this);
        }
        return result;
    }

    @Override
    public boolean interpret(Set<Integer> trueVars) {
        return this.value;
    }
}
