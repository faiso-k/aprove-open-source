package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * XOR of n formulae, n >= 2. An XorFormula evaluates to true iff
 * <b>an odd number of its arguments</b> evaluates to true.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class XorFormula<T> extends NaryJunctorFormula<T> {

    XorFormula(List<? extends Formula<T>> fmlae) {
        super(fmlae);
    }

    @Override
    public String getJunctor() {
        return "xor";
    }

    @Override
    public int getGateType() {
        return CircuitGate.XOR;
    }

    @Override
    public Formula<T> evaluate(ValueCache<T> cache) {
        List<Formula<T>> args = new ArrayList<Formula<T>>(this.args.size());
        for (Formula<T> arg : this.args) {
            args.add(arg.evaluate(cache));
        }
        return cache.getFactory().buildXor(args);
    }

    @Override
    public void update(ValueCache<T> cache, boolean one) {}

    @Override
    public <S> S apply(FormulaVisitor<S, T> visitor) {
        return visitor.caseXor(this);
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
            result = visitor.outXor(this, intermediates);
        }
        return result;
    }

    @Override
    public boolean interpret(Set<Integer> trueVars) {
        boolean result = false;
        for (Formula<T> f : this.args) {
            boolean fTruth = f.interpret(trueVars);
            result = result ^ fTruth;
        }
        return result;
    }
}
