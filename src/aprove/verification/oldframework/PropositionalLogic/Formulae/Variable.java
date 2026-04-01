package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * Propositional variables.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class Variable<T> extends AbstractVariable<T> implements NamedFormula {

    private static String NO_NAME = "<>";

    // The memory will be worth it... if not, it's just a pointer.
    private String name = Variable.NO_NAME;

    @Override
    public String toString() {
        if (! this.name.equals(Variable.NO_NAME)) {
            // Well, there is a name for it, so output this.
            return this.name;
        } else if (this.id == AbstractFormula.ID_UNSET) {
            // According to the Java API docu, that is the
            // suffix of Object.toString() that follows
            // after the '@' char. We don't want to see
            // the class name every time.
            return Integer.toHexString(this.hashCode());
        } else {
            // The id is somewhat more interesting, but
            // only return it if it has been set
            return Integer.toString(this.id);
        }
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

    /**
     * @return Returns the id of this.
     */
    @Override
    public int getId() {
        return this.id;
    }

    @Override
    public int label(int id) {
        if (this.id == AbstractFormula.ID_UNSET) {
            this.id = id++;
        }
        return id;
    }

    @Override
    public void addGates(List<CircuitGate> gates) {}
    // nothing to add, and the id of a variable is not changed here either

    @Override
    public <S> S apply(FormulaVisitor<S, T> visitor) {
        return visitor.caseVariable(this);
    }

    @Override
    public <S> S apply(FineGrainedFormulaVisitor<S, T> visitor) {
        S result = visitor.get(this);
        if (result == null) {
            result = visitor.outVariable(this);
        }
        return result;
    }

    @Override
    public String getDescription() {
        // TODO Auto-generated method stub
        return this.name;
    }

    @Override
    public String getType() {
        return "VAR";
    }

    @Override
    public void setDescription(String description) {
        if (Globals.createSatViewLabels) {
            this.name = description;
        } else { // Discard string to free memory on next gc
            return;
        }
    }

    @Override
    public boolean interpret(Set<Integer> trueVars) {
        return trueVars.contains(this.id);
    }
}
