package aprove.verification.oldframework.PropositionalLogic.Formulae;

import java.util.*;

import aprove.*;
import aprove.verification.oldframework.PropositionalLogic.*;

/**
 * A formula which has an n-ary junctor at its root where n >= 2
 * and which in addition has a single int parameter as part of its
 * type specification.
 *
 * @author Carsten Fuhs
 */
public abstract class CardinalityFormula<T> extends NaryJunctorFormula<T> {

    // the parameter of the formula type, i.e., the cardinality
    protected int cardinality;

    protected CardinalityFormula(List<? extends Formula<T>> args,
            int cardinality) {
        super(args);
        if (Globals.useAssertions) {
            assert cardinality >= 0 : "Negative cardinalities are somewhat pointless.";
        }
        this.cardinality = cardinality;
    }

    /**
     * @return the cardinality of this formula
     */
    public int getCardinality() {
        return this.cardinality;
    }

    @Override
    public abstract String getJunctor();

    @Override
    public abstract int getGateType();

    @Override
    public abstract <S> S apply(FormulaVisitor<S, T> visitor);

    @Override
    public abstract <S> S apply(FineGrainedFormulaVisitor<S, T> visitor);


    @Override
    public Formula<T> evaluate(ValueCache<T> cache) {
        throw new UnsupportedOperationException("evaluate(ValueCache<T>) not yet implemented for type CardinalityFormula!");
    }

    @Override
    public void update(ValueCache<T> cache, boolean one) {
        throw new UnsupportedOperationException("update(ValueCache<T>, boolean) not yet implemented for type CardinalityFormula!");
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
            this.gate = CircuitGate.create(this.getGateType(), id, inputs,
                    this.cardinality);
            this.id = id;

            // in general, the next formula will not just get the label id + 1,
            // but we need to reserve space for additional variables on CNF
            // level
            int result = this.computeNextLabel(id);
            return result;
        }
        return id;
    }

    /**
     * Compute the next id that can be used for labeling after this formula
     * has been labeled. In contrast to many other formula types, this is
     * non-trivial for CardinalityFormulae since here the CNF encoding will
     * in general introduce additional ids.
     *
     * @param currentId the id for which the next label is to be computed
     * @return the next label that may be used
     */
    protected abstract int computeNextLabel(int currentId);
}
