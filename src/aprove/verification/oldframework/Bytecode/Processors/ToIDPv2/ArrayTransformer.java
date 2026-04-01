package aprove.verification.oldframework.Bytecode.Processors.ToIDPv2;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;

/**
 * This class transforms references to (abstract) array variables to terms.
 *
 * @author Christian von Essen
 */
public class ArrayTransformer extends ValueTransformer {
    /**
     * The function symbol used for arrays (both concrete and abstract):
     */
    public static final IFunctionSymbol<UnknownRing> ARRAY_CONSTR = IFunctionSymbol.<UnknownRing>createChecked(
        "ARRAY",
        1,
        IDPPredefinedMap.DEFAULT_MAP);

    /**
     * {@inheritDoc}
     */
    @Override
    public Collection<? extends ITerm<?>> transform(
        final State s,
        final State stateWithInformation,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap,
        final AbstractVariableReference ref,
        final TransformationDispatcher dispatcher,
        final Set<AbstractVariableReference> seenRefs,
        final Set<AbstractVariableReference> possiblePredecessors,
        final ReferenceAccessInformation changedConnectionInformation)
    {
        final Collection<ITerm<?>> res = new LinkedList<>();
        final Array a = (Array) s.getAbstractVariable(ref);

        final AbstractVariableReference changedRef;
        if (changedConnectionInformation != null) {
            changedRef = changedConnectionInformation.getAccessedRef();
        } else {
            changedRef = null;
        }

        if (dispatcher.getConverterArguments().encodePathLength) {
            //This is the changed reference:
            if (ref.equals(changedRef)) {
                if (changedConnectionInformation instanceof ArrayAccessInformation) {
                    /*
                     * The change is a primitive:
                     */
                    if (!changedRef.pointsToReferenceType()) {
                        res.add(dispatcher.getVariableLength(ref, s));
                    } else {
                        res.add(dispatcher.getVariableLengthChanged(ref, s));
                    }
                } else {
                    res.add(dispatcher.getVariableLengthChanged(ref, s));
                }
            } else if (possiblePredecessors != null && possiblePredecessors.contains(ref)) {
                res.add(dispatcher.getVariableLengthChanged(ref, s));
            } else {
                res.add(dispatcher.getVariableLength(ref, s));
            }
        }

        if (dispatcher.getConverterArguments().encodeArrayLengthSeparately) {
            if (a != null) {
                res.add(dispatcher.transformInt(s, a.getLength()));
            } else {
                res.add(dispatcher.getVariableArrayLength(ref, s));
            }
        }

        //We don't need the rest if we only do PL:
        if (!dispatcher.getConverterArguments().encodeReferenceTypesAsTerms) {
            return res;
        }

        if (s.getHeapAnnotations().isMaybeExisting(ref)) {
            if (possiblePredecessors.contains(ref)) {
                res.add(dispatcher.changedByWriteAccessVariable(ref, seenRefs, s));
            } else {
                res.add(dispatcher.<UnknownRing>getVariable(ref, seenRefs, s));
            }
            return res;
        }

        final ITerm<BigInt> length;
        if (a instanceof AbstractArray) {
            length = dispatcher.transformInt(s, a.getLength());
        } else {
            final ConcreteArray ca = (ConcreteArray) a;
            length = IntegerTransformer.getConstantIntegerTerm(ca.getLiteralLength());
        }

        /*
        final ITerm<UnknownRing> data;
        if (a instanceof AbstractArray) {
        if (possiblePredecessors.contains(ref)) {
            data = dispatcher.changedByWriteAccessVariable(ref, seenRefs, s);
        } else {
            data = dispatcher.arrayVariable(ref, seenRefs, s);
        }
        } else {
        final ConcreteArray ca = (ConcreteArray) a;
        final ArrayList<ITerm<?>> dataContent = new ArrayList<ITerm<?>>(2 * ca.getLiteralLength());
        for (int i = 0; i < ca.getLiteralLength(); i++) {
            if (ca.get(s, ref, i).pointsToInt()) {
                dataContent.addAll(dispatcher.<BigInt>transform(
                        s, stateWithInformation, refMap, ref,
                        ca.get(s, ref, i), seenRefs,
                        possiblePredecessors, changedConnectionInformation));
            } else {
                dataContent.addAll(dispatcher.<UnknownRing>transform(
                        s, stateWithInformation, refMap, ref,
                        ca.get(s, ref, i), seenRefs,
                        possiblePredecessors, changedConnectionInformation));
            }
        }
        final IFunctionSymbol<UnknownRing> dataSym =
            IFunctionSymbol.<UnknownRing>createChecked("DATA_" + dataContent.size(), dataContent.size(), IDPPredefinedMap.DEFAULT_MAP);
        data = IFunctionApplication.create(dataSym, ImmutableCreator.create(dataContent));
        }*/

        final ITerm<UnknownRing> array;
        //If we have done this separately already, encode some trash value here:
        if (dispatcher.getConverterArguments().encodeArrayLengthSeparately) {
            array = ITerm.createFunctionApplication(ArrayTransformer.ARRAY_CONSTR, dispatcher.getVariableArrayLength(ref, s));
        } else {
            array = ITerm.createFunctionApplication(ArrayTransformer.ARRAY_CONSTR, length);
        }
        res.add(ITerm.createFunctionApplication(InstanceTransformer.JAVA_LANG_OBJECT_NAME, array));
        return res;
    }
}
