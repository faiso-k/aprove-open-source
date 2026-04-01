package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * A formula which has an n-ary junctor at its root where n >= 2.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public abstract class NaryJunctorFormula<T> extends JunctorFormula<T> {

    protected List<? extends Formula<T>> args; // the child formulae

    /**
     * Builds an n-ary formula, makes args the child list of this.
     * Beware, modifications to args after the constructor call will
     * affect this!
     *
     * @param args The argument vector for this,
     *  will be incorporated into this, must contain at least 2 elements.
     */
    protected NaryJunctorFormula(List<? extends Formula<T>> args) {
        if (Globals.useAssertions) {
            assert(args.size() > 1);
        }
        this.args = args;
    }

    @Override
    public boolean isLiteral() {
        return false;
    }

    public List<? extends Formula<T>> getArgs() {
        return this.args;
    }

    /**
     * @return the formula in infix form.
     */
    @Override
    public String toString() {
        return this.toString(null);
    }

    @Override
    public String toString(Map<? extends AbstractVariable<T>, ?> map) {
        StringBuilder sb = new StringBuilder();
        sb.append('(');
        boolean notFirst = false;
        for (Formula<T> fml : this.args) {
            if (notFirst) {
                sb.append(' ');
                sb.append(this.getJunctor());
                int id = this.getId();
                if (id != AbstractFormula.ID_UNSET) {
                    sb.append('[');
                    sb.append(id);
                    sb.append(']');
                }
                sb.append(' ');
            }
            sb.append(fml.toString(map));
            notFirst = true;
        }
        sb.append(')');
        return sb.toString();
    }

    @Override
    public int label(int id) {
        if (this.id == AbstractFormula.ID_UNSET) {
            // this has not been labeled yet
            for (Formula<T> formula : this.args) {
                id = formula.label(id);
            }
            int[] inputs = new int[this.args.size()];
            for (int i = 0; i < inputs.length; ++i) {
                inputs[i] = this.args.get(i).getId();
            }
            this.gate = CircuitGate.create(this.getGateType(), id, inputs);
            this.id = id++;
        }
        return id;
    }

    @Override
    public void addGates(List<CircuitGate> gates) {
        if (this.id != AbstractFormula.ID_UNSET) {
            gates.add(this.gate);
            this.id = AbstractFormula.ID_UNSET;
            for (Formula<T> formula : this.args) {
                formula.addGates(gates);
            }
        }
    }

    @Override
    public int countSub() {
        int sum = 1;
        for (Formula<T> arg : this.args) {
            sum += arg.countSub();
        }
        return sum;
    }
}
