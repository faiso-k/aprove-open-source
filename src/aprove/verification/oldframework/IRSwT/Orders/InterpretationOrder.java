package aprove.verification.oldframework.IRSwT.Orders;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.IDPProblem.*;

/**
 *
 * Represents an order induced by some interpretation.
 * @author Matthias Hoelzel
 *
 * @param <Domain> Probably integers or rational numbers.
 */
public class InterpretationOrder<Domain extends Exportable> extends AbstractOrder {
    /**
     * Represent a term interpretation.
     */
    private final Interpretation<Domain> interpretation;

    /**
     * Constructor!
     * @param inputRules set of considered rules
     * @param inducingInterpretation the inducing order
     * @param strictOriented set of strict oriented rules
     * @param bounded set of bounded rules
     */
    public InterpretationOrder(
        final Set<IGeneralizedRule> inputRules,
        final Interpretation<Domain> inducingInterpretation,
        final LinkedHashSet<IGeneralizedRule> strictOriented,
        final LinkedHashSet<IGeneralizedRule> bounded)
    {
        super(inputRules, strictOriented, bounded);
        this.interpretation = inducingInterpretation;
    }

    @Override
    public void export(final Export_Util eu, final StringBuilder sb) {
        this.interpretation.export(eu, sb);
        this.exportStrictAndBounded(sb, eu);
    }
}
