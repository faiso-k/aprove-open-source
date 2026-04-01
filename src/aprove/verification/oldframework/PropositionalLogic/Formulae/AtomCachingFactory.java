package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * Builds formulae. Only NotFormulae are flattened when created,
 * and only constants are cached. Directly nested occurrences of
 * logical operators are allowed. For example, ((A and B) and C)
 * is okay.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class AtomCachingFactory<T> extends AbstractFormulaFactory<T> {

    @Override
    public Formula<T> buildAnd(List<? extends Formula<T>> fmlae) {
        switch (fmlae.size()) {
        case 0:
            return this.ONE;
        case 1:
            return fmlae.get(0);
        default:
            return new AndFormula<T>(fmlae);
        }
    }


    @Override
    public <U> FormulaFactory<U> toTheory() {
        return new AtomCachingFactory<U>();
    }

    @Override
    public Formula<T> buildOr(List<Formula<T>> fmlae) {
        switch (fmlae.size()) {
        case 0:
            return this.ZERO;
        case 1:
            return fmlae.get(0);
        default:
            return new OrFormula<T>(fmlae);
        }
    }

    @Override
    public Formula<T> buildNot(Formula<T> fml) {
        if (fml == this.ONE) {
            return this.ZERO;
        }
        if (fml == this.ZERO) {
            return this.ONE;
        }
        if (fml instanceof NotFormula) { // no double negations!
            Formula<T> result = ((NotFormula<T>) fml).arg;
            if (Globals.useAssertions) { // fml is not a double negation, is it?!
                assert !(result instanceof NotFormula);
            }
            return result;
        }
        else {
            return new NotFormula<T>(fml);
        }
   }

    @Override
    public Formula<T> buildXor(List<Formula<T>> fmlae) {
        switch (fmlae.size()) {
        case 0:
            return this.ZERO;
        case 1:
            return fmlae.get(0);
        case 2:
            return new XorFormula<T>(fmlae);
        default:
            return this.buildXorComb(fmlae);
        }
    }

    @Override
    public Formula<T> buildIff(Formula<T> left, Formula<T> right) {
        return new IffFormula<T>(left, right);
    }

    @Override
    public Formula<T> buildIte(Formula<T> condition, Formula<T> thenFormula, Formula<T> elseFormula) {
        return new IteFormula<T>(condition, thenFormula, elseFormula);
    }
}
