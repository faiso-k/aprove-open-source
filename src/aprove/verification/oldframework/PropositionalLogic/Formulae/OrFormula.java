package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * OR of n formulae, n >= 2.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class OrFormula<T> extends NaryJunctorFormula<T> {

    OrFormula(List<? extends Formula<T>> fmlae) {
        super(fmlae);
    }

    @Override
    public String getJunctor() {
        return "or";
    }

    @Override
    public int getGateType() {
        return CircuitGate.OR;
    }

    @Override
    public Formula<T> evaluate(ValueCache<T> cache) {
        List<Formula<T>> args = new ArrayList<Formula<T>>();
        for (Formula<T> arg : this.args) {
            args.add(arg.evaluate(cache));
        }
        return cache.getFactory().buildOr(args);
    }

    @Override
    public void update(ValueCache<T> cache, boolean one) {}

    @Override
    public <S> S apply(FormulaVisitor<S, T> visitor) {
        return visitor.caseOr(this);
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
            result = visitor.outOr(this, intermediates);
        }
        return result;
    }

    @Override
    public boolean interpret(Set<Integer> trueVars) {
        boolean result = false;
        for (Formula<T> f : this.args) {
            boolean fTruth = f.interpret(trueVars);
            if (fTruth) {
                result = true;
                break;
            }
        }
        return result;
    }
}
