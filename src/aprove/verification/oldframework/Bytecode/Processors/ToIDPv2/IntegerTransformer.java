package aprove.verification.oldframework.Bytecode.Processors.ToIDPv2;

import java.math.*;
import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

/**
 * This class transforms references to (abstract) integer variables to terms.
 *
 * @author Christian von Essen
 */
public class IntegerTransformer extends ValueTransformer {
    /**
     * {@inheritDoc}
     */
    @Override
    public Collection<? extends ITerm<BigInt>> transform(
        final State s,
        final State stateWithInformation,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap,
        final AbstractVariableReference ref,
        final TransformationDispatcher dispatcher,
        final Set<AbstractVariableReference> seenRefs,
        final Set<AbstractVariableReference> possiblePredecessors,
        final ReferenceAccessInformation changedConnectionInformation)
    {
        final AbstractVariable v = s.getAbstractVariable(ref);

        /*
         * This is a special case for variables that are freshly created in the
         * new state (for example by a CONV operation from int to long). Just
         * return the variable:
         */
        if (v == null) {
            return Collections.singleton(dispatcher.<BigInt>getVariable(ref, seenRefs, s));
        }

        assert (v instanceof AbstractInt) : "IntegerTransformer only transforms integers";

        final AbstractInt i = (AbstractInt) v;

        if (i.isLiteral()) {
            return Collections.singleton(IntegerTransformer.getConstantIntegerTerm(((LiteralInt) i).getLiteral()));
        }
        if (ref.pointsToConstantInt()) {
            final AbstractVariable av = s.getAbstractVariable(ref);
            assert (av instanceof AbstractInt);
            final AbstractInt abstractInt = (AbstractInt) av;
            assert (abstractInt.isLiteral());
            return Collections.singleton(IntegerTransformer.getConstantIntegerTerm(abstractInt.getLiteral()));

        }
        return Collections.singleton(dispatcher.<BigInt>getVariable(ref, seenRefs, s));
    }

    /**
     * Convert an integer i into the ITRS term i@z
     * @param i integer
     * @return ITRS Term
     */
    public static IFunctionApplication<BigInt> getConstantIntegerTerm(final BigInteger i) {
        return IDPPredefinedMap.DEFAULT_MAP.createIntIntTerm(BigInt.create(i), DomainFactory.INTEGERS);
    }

    /**
     * Convert an integer i into the ITRS term i@z
     * @param i integer
     * @return ITRS Term
     */
    public static IFunctionApplication<BigInt> getConstantIntegerTerm(final Integer i) {
        return IntegerTransformer.getConstantIntegerTerm(BigInteger.valueOf(i));
    }
}
