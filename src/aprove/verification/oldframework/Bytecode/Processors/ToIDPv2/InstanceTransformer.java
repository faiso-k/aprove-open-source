package aprove.verification.oldframework.Bytecode.Processors.ToIDPv2;

import java.util.*;
import java.util.concurrent.atomic.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Processors.ToSCC.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import immutables.*;

/**
 * This class transforms references to (abstract) instance variables to terms.
 *
 * @author Christian von Essen
 */
public class InstanceTransformer extends ValueTransformer {
    /**
     * EOC.
     */
    public static final String EOC = "EOC";

    /**
     * The function symbol used for the java.lang.Object class:
     */
    public static final IFunctionSymbol<UnknownRing> JAVA_LANG_OBJECT_NAME =
        IFunctionSymbol.<UnknownRing>createChecked(ClassName.Important.JAVA_LANG_OBJECT.getClassName().toString(), 1,
            IDPPredefinedMap.DEFAULT_MAP);

    /**
     * The function symbol used for the null pointer:
     */
    public static final IFunctionSymbol<UnknownRing> NULL_NAME = IFunctionSymbol.<UnknownRing>createChecked("NULL", 0,
        IDPPredefinedMap.DEFAULT_MAP);

    /**
     * The function symbol used for the null pointer:
     */
    public static final IFunctionSymbol<UnknownRing> END_OF_CLASS_NAME = IFunctionSymbol.<UnknownRing>createChecked(
        InstanceTransformer.EOC, 0, IDPPredefinedMap.DEFAULT_MAP);

    /**
     * This marker is used to denote that the current instance has no extending
     * instance (e.g. Object(EOC) for an instance of exactly and only Object).
     */
    private static final ITerm<UnknownRing> END_OF_CLASS = ITerm.createFunctionApplication(InstanceTransformer.END_OF_CLASS_NAME);

    /**
     * The constructor used for null references.
     */
    private static final ITerm<UnknownRing> NULL = ITerm.createFunctionApplication(InstanceTransformer.NULL_NAME);

    /**
     * The term used to encode cyclic object instances:
     */
    public static final ITerm<UnknownRing> CYCLIC_INSTANCE_TERM = ITerm.createFunctionApplication(
        InstanceTransformer.JAVA_LANG_OBJECT_NAME,
        ITerm.createFunctionApplication(IFunctionSymbol.create("EOR", 0, IDPPredefinedMap.DEFAULT_MAP)));

    /**
     * Just to create fresh variables for abstract fields.
     */
    private final AtomicInteger abstractFieldCounter = new AtomicInteger();

    /**
     * {@inheritDoc}
     */
    @Override
    public Collection<? extends ITerm<?>> transform(final State s,
        final State stateWithInformation,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap,
        final AbstractVariableReference ref,
        final TransformationDispatcher dispatcher,
        final Set<AbstractVariableReference> seenRefs,
        final Set<AbstractVariableReference> possiblePredecessors,
        final ReferenceAccessInformation changedConnectionInformation) {
        final ObjectInstance obj = (ObjectInstance) s.getAbstractVariable(ref);
        final Collection<ITerm<?>> res = new LinkedList<>();

        final UsedFieldsAnalysis usedFieldAnalysis = dispatcher.getUsedFieldAnalysis();

        final AbstractVariableReference changedRef;
        if (changedConnectionInformation != null) {
            changedRef = changedConnectionInformation.getAccessedRef();
        } else {
            changedRef = null;
        }

        if (dispatcher.getConverterArguments().encodePathLength) {
            //This is the changed reference:
            if (ref.equals(changedRef)) {
                if (changedConnectionInformation instanceof InstanceAccessInformation) {
                    final InstanceAccessInformation ifE = (InstanceAccessInformation) changedConnectionInformation;
                    final Collection<String> usedFields = usedFieldAnalysis.getUsedFieldNames(ifE.getClassName());

                    /*
                     * The change is a primitive or to a field that is never
                     * read, so the value stays the same:
                     */
                    if (!changedRef.pointsToReferenceType() || !usedFields.contains(ifE.getFieldName())) {
                        res.add(dispatcher.getVariableLength(ref, s));

                    } else {
                        final IFunctionSymbol<BigInt> add =
                            IDPPredefinedMap.DEFAULT_MAP.<BigInt>getFunctionSymbolChecked(PredefinedFunction.Func.Add,
                                DomainFactory.INTEGER_INTEGER);

                        final IFunctionApplication<BigInt> writtenValPlusOne;
                        if (ifE.getReadOrWrittenRef().isNULLRef()) {
                            writtenValPlusOne = IntegerTransformer.getConstantIntegerTerm(1);
                        } else {
                            writtenValPlusOne =
                                ITerm.createFunctionApplication(add,
                                    dispatcher.getVariableLength(ifE.getReadOrWrittenRef(), s),
                                    IntegerTransformer.getConstantIntegerTerm(1));
                        }

                        /*
                         * There is only reference field, so the path length is
                         * equal to the written value + 1:
                         */
                        if (usedFieldAnalysis.getNumberOfUsedReferenceFields(ifE.getClassName()) <= 1) {
                            res.add(writtenValPlusOne);

                            /*
                             * The new length is the max of the written value + 1 and
                             * the old value.
                             */
                        } else {
                            final IFunctionApplication<BigInt> maxOfWrittenValPlusOneAndOldVal =
                                ITerm.createFunctionApplication(RuleCreator.INTERNAL_MAX_SYMBOL,
                                    dispatcher.getVariableLength(ref, s), writtenValPlusOne);

                            res.add(maxOfWrittenValPlusOneAndOldVal);
                        }
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
            res.add(dispatcher.getVariableArrayLength(ref, s));
        }

        //We don't need the rest if we only do PL:
        if (obj instanceof AbstractInstance) {
            if (dispatcher.getConverterArguments().encodeReferenceTypesAsTerms) {
                if (ref.equals(changedRef) || (possiblePredecessors != null && possiblePredecessors.contains(ref))) {
                    res.add(dispatcher.changedByWriteAccessVariable(ref, seenRefs, s));
                } else {
                    res.add(dispatcher.<UnknownRing>getVariable(ref, seenRefs, s));
                }
            }
            return res;
        }

        if (ref.isNULLRef() || (obj != null && obj.isNULL())) {
            //Remove the variable, put in the constant 0 instead.
            res.clear();
            if (dispatcher.getConverterArguments().encodePathLength) {
                res.add(IntegerTransformer.getConstantIntegerTerm(0));
            }
            if (dispatcher.getConverterArguments().encodeReferenceTypesAsTerms) {
                res.add(InstanceTransformer.NULL);
            }
            return res;
        }

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

        assert (obj != null) : "Ref " + ref + " pointing to instance which is not there in\n" + s;

        // now we know that the instance does exist
        ConcreteInstance inst = (ConcreteInstance) obj;
        inst = inst.getMostSpecializedInstance();

        /*
         * We build the term walking the class tree from the most specialized
         * instance to its root. The currently encoded part is stored in
         * subTypeTerm - when we are done, subTypeTerm is our full result.
         */
        ITerm<UnknownRing> subTypeTerm;

        // Do we need an EOC or a variable for the innermost term?
        final AbstractType type = s.getAbstractType(ref);
        TypeTree tt = inst.getType();
        final FuzzyType maxCommonSuperType = type.maximalCommonSupertype(s.getClassPath());

        //This is a non-realized array of a primitive type:
        if (maxCommonSuperType instanceof FuzzyPrimitiveType) {
            subTypeTerm = dispatcher.changedByWriteAccessVariable(ref, seenRefs, s);
            //Otherwise, it's an actual instance:
        } else if (type.isConcrete()
            && ((FuzzyClassType) maxCommonSuperType).getMinimalClass().equals(tt.getClassName())) {
            subTypeTerm = InstanceTransformer.END_OF_CLASS;
        } else {
            if (possiblePredecessors.contains(ref)) {
                subTypeTerm = dispatcher.changedByWriteAccessVariable(ref, seenRefs, s);
            } else {
                subTypeTerm = dispatcher.nonRealizedSubInstanceVariable(ref, seenRefs, s);
            }
        }

        // Now we will build the term
        while (inst != null) {
            /*
             * If we have done the used fields analysis, then we want to use it and
             * only encode fields that were read. Otherwise, just encode
             * everything.
             */
            Collection<String> fields;
            if (usedFieldAnalysis != null) {
                fields = usedFieldAnalysis.getUsedFieldNames(tt.getClassName());
            } else {
                fields = inst.getFieldNames();
            }

            final int arity = fields.size() + 1;

            // The arguments of this slice.
            final ArrayList<ITerm<?>> args = new ArrayList<>(arity);

            // The first argument always is the sub type term.
            args.add(subTypeTerm);

            if (fields.size() > 0) {
                for (final String fieldName : fields) {
                    final AbstractVariableReference fieldRef = inst.getField(tt.getClassName(), fieldName, true);
                    if (fieldRef == null) {
                        /*
                         * This is a partially abstract object, we do not have a value for this field. Just use a fresh
                         * variable.
                         */
                        final IVariable<UnknownRing> freshVar =
                            ITerm.createVariable("abstractField" + this.abstractFieldCounter.incrementAndGet(),
                                DomainFactory.UNKNOWN);
                        args.add(freshVar);
                    } else if (fieldRef.pointsToAnyIntegerType()) {
                        args.addAll(dispatcher.<BigInt>transform(s, stateWithInformation, refMap, ref, fieldRef,
                            seenRefs, possiblePredecessors, changedConnectionInformation));
                    } else {
                        args.addAll(dispatcher.<UnknownRing>transform(s, stateWithInformation, refMap, ref, fieldRef,
                            seenRefs, possiblePredecessors, changedConnectionInformation));
                    }
                }
            }

            // This slice's root symbol
            final IFunctionSymbol<UnknownRing> sym = InstanceTransformer.getConstructorSymbol(tt.getClassName(), args.size());

            subTypeTerm = ITerm.<UnknownRing>createFunctionApplication(sym, ImmutableCreator.create(args));
            inst = inst.getSuperClassInstance();
            tt = tt.getSuperType();
        }

        res.add(subTypeTerm);
        return res;
    }

    /**
     * @param cn Classname to get constructor for
     * @param arity the arity of the function symbol
     * @return a function symbol for the instances class, e.g. "O" for
     * java.lang.Object
     */
    public static IFunctionSymbol<UnknownRing> getConstructorSymbol(final ClassName cn, final int arity) {
        // TODO short! unique!
        return IFunctionSymbol.<UnknownRing>createChecked(cn.toString(), arity, IDPPredefinedMap.DEFAULT_MAP);
    }
}
