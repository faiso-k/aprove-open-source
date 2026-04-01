package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * ATMOST_k(fmlae) holds iff at most k of the elements of
 * fmlae evaluate to "true".
 *
 * @author Carsten Fuhs
 */
public class AtMostFormula<T> extends CardinalityFormula<T> {

    AtMostFormula(List<? extends Formula<T>> args, int cardinality) {
        super(args, cardinality);
    }

    @Override
    public <S> S apply(FormulaVisitor<S, T> visitor) {
        return visitor.caseAtMost(this);
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
            result = visitor.outAtMost(this, intermediates);
        }
        return result;
    }

    @Override
    protected int computeNextLabel(int currentId) {
        throw new UnsupportedOperationException("Not yet implemented.");
    }

    @Override
    public int getGateType() {
        return CircuitGate.ATMOST;
    }

    @Override
    public String getJunctor() {
        return "atmost_" + this.cardinality;
    }

    @Override
    public boolean interpret(Set<Integer> trueVars) {
        if (this.cardinality > this.args.size()) {
            return true;
        }
        boolean result = true;
        int truthsSeen = 0;
        for (Formula<T> f : this.args) {
            boolean fTruth = f.interpret(trueVars);
            if (fTruth) {
                ++truthsSeen;
                if (truthsSeen > this.cardinality) {
                    result = false;
                    break;
                }
            }
        }
        return result;
    }
}
