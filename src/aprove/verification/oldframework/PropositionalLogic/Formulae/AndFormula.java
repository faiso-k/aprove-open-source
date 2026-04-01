package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * AND of n formulae, n >= 2.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class AndFormula<T> extends NaryJunctorFormula<T> {

    AndFormula(List<? extends Formula<T>> fmlae) {
        super(fmlae);
    }

    @Override
    public String getJunctor() {
        return "and";
    }

    @Override
    public int getGateType() {
        return CircuitGate.AND;
    }

    @Override
    public Formula<T> evaluate(ValueCache<T> cache) {
        List<Formula<T>> args = new ArrayList<Formula<T>>(this.args.size());
        for (Formula<T> arg : this.args) {
            args.add(arg.evaluate(cache));
        }
        return cache.getFactory().buildAnd(args);
    }

    @Override
    public void update(ValueCache<T> cache, boolean one) {
        for (Formula<T> arg : this.args) {
            arg.update(cache, one);
        }
    }

    @Override
    public <S> S apply(FormulaVisitor<S, T> visitor) {
        return visitor.caseAnd(this);
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
            result = visitor.outAnd(this, intermediates);
        }
        return result;
    }

    @Override
    public boolean interpret(Set<Integer> trueVars) {
        boolean result = true;
        for (Formula<T> f : this.args) {
            boolean fTruth = f.interpret(trueVars);
            if (! fTruth) {
                result = false;
                break;
            }
        }
        return result;
    }
}
