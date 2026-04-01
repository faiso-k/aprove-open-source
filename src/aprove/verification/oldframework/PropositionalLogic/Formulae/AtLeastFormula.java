package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * ATLEAST_k(fmlae) holds iff at least k of the elements of
 * fmlae evaluate to "true".
 *
 * @author Carsten Fuhs
 */
public class AtLeastFormula<T> extends CardinalityFormula<T> {

    AtLeastFormula(List<? extends Formula<T>> args, int cardinality) {
        super(args, cardinality);
    }

    @Override
    public <S> S apply(FormulaVisitor<S, T> visitor) {
        return visitor.caseAtLeast(this);
    }

    @Override
    public <S> S apply(FineGrainedFormulaVisitor<S, T> visitor) {
        S result = visitor.get(this);
        if (result == null) {
            List<S> intermediates = new ArrayList<S>(this.args.size());
            for (Formula<T> f : this.args) {
                S inter = f.apply(visitor);
                intermediates.add(inter);
            }
            result = visitor.outAtLeast(this, intermediates);
        }
        return result;
    }

    @Override
    protected int computeNextLabel(int currentId) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    @Override
    public int getGateType() {
        return CircuitGate.ATLEAST;
    }

    @Override
    public String getJunctor() {
        return "atleast_" + this.cardinality;
    }

    @Override
    public boolean interpret(Set<Integer> trueVars) {
        if (this.cardinality <= 0) {
            return true;
        }
        if (this.cardinality > this.args.size()) {
            return false;
        }
        boolean result = false;
        int truthsSeen = 0;
        for (Formula<T> f : this.args) {
            boolean fTruth = f.interpret(trueVars);
            if (fTruth) {
                ++truthsSeen;
                if (truthsSeen >= this.cardinality) {
                    result = true;
                    break;
                }
            }
        }
        return result;
    }
}
