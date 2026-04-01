package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * IFF of just 2 formulae.
 * TODO Create a superclass BinaryJunctorFormula iff we need another
 * binary junctor.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class IffFormula<T> extends JunctorFormula<T> {

    Formula<T> left;
    Formula<T> right;

    IffFormula(Formula<T> left, Formula<T> right) {
        this.left = left;
        this.right = right;
    }

    @Override
    public boolean isLiteral() {
        return false;
    }

    @Override
    public String getJunctor() {
        return "iff";
    }

    @Override
    public String toString() {
        return this.toString(null);
    }

    @Override
    public String toString(Map<? extends AbstractVariable<T>, ?> map) {
        StringBuilder builder = new StringBuilder();
        builder.append('(');
        builder.append(this.left.toString(map));
        builder.append(' ');
        builder.append(this.getJunctor());
        int id = this.getId();
        if (id != AbstractFormula.ID_UNSET) {
            builder.append('[');
            builder.append(id);
            builder.append(']');
        }
        builder.append(' ');
        builder.append(this.right.toString(map));
        builder.append(')');
        return builder.toString();
    }

    @Override
    public int getGateType() {
        return CircuitGate.IFF;
    }

    @Override
    public int label(int id) {
        if (this.id == AbstractFormula.ID_UNSET) {
            // not yet labeled with an id -> label children first
            id = this.left.label(id);
            id = this.right.label(id);
            this.gate = CircuitGate.create(CircuitGate.IFF, id, new int[] {this.left.getId(), this.right.getId()});
            this.id = id++;
        }
        return id;
    }

    @Override
    public void addGates(List<CircuitGate> gates) {
        if (this.id != AbstractFormula.ID_UNSET) {
            gates.add(this.gate);
            this.id = AbstractFormula.ID_UNSET;
            this.left.addGates(gates);
            this.right.addGates(gates);
        }
    }

    @Override
    public Formula<T> evaluate(ValueCache<T> cache) {
        return cache.getFactory().buildIff(this.left.evaluate(cache), this.right.evaluate(cache));
    }

    @Override
    public void update(ValueCache<T> cache, boolean one) {}

    @Override
    public <S> S apply(FormulaVisitor<S, T> visitor) {
        return visitor.caseIff(this);
    }

    @Override
    public int countSub() {
        return 1+this.left.countSub()+this.right.countSub();
    }

    @Override
    public <S> S apply(FineGrainedFormulaVisitor<S, T> visitor) {
        S result = visitor.get(this);
        if (result == null) {
            S s1, s2;
            s1 = this.left.apply(visitor);
            s2 = this.right.apply(visitor);
            result = visitor.outIff(this, s1, s2);
        }
        return result;
    }

    public Formula<T> getArg1() {
        return this.left;
    }

    public Formula<T> getArg2() {
        return this.right;
    }

    @Override
    public boolean interpret(Set<Integer> trueVars) {
        boolean leftTruth = this.left.interpret(trueVars);
        boolean rightTruth = this.right.interpret(trueVars);
        return leftTruth == rightTruth;
    }
}
