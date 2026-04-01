package aprove.verification.oldframework.Bytecode.Processors.ToIDPv2;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.PredefinedFunction.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.Processors.*;
import aprove.verification.oldframework.Bytecode.Processors.ToSCC.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * In our TerminationSCC2IDPv2 conversion, we create one RuleCreator instance per SCC and use it to generate one rule
 * per edge.
 * @author Christian von Essen, Marc Brockschmidt
 */
public final class RuleCreator {
    /**
     * The name of the symbol used for internal MAX function we provide.
     */
    public static final String INTERNAL_MAX_NAME = "JBCMAX";

    /**
     * The function symbol used for internal MAX function we provide.
     */
    public static final IFunctionSymbol<BigInt> INTERNAL_MAX_SYMBOL = IFunctionSymbol.<BigInt>createChecked(
        RuleCreator.INTERNAL_MAX_NAME,
        2,
        IDPPredefinedMap.DEFAULT_MAP);

    /**
     * This marker is used to denote that the current stackframe is the topmost one in a state.
     */
    private static final String END_OF_STACK_NAME = "EOS";

    /**
     * This is the base name of the symbol encoding static variables. To obtain a function symbol, "_label" is appended,
     * where label is usually the id of the node encoded.
     */
    private static final String STATIC_VARS_SYMBOL_NAME = "STATIC";

    /**
     * Parameters for the enclosing conversion processor.
     */
    private final ConverterArguments arguments;

    /**
     * The variable construction thingy.
     */
    private final TransformationDispatcher dispatcher;

    /**
     * The factory creating formulas for this problem.
     */
    private final ItpfFactory itpfFactory;

    /**
     * Information relating to the whole SCC.
     */
    private final SCCAnnotations sccAnnotations;

    /**
     * Convenience class holding information about references we consider interesting and want to encode in our rules.
     */
    private final InterestingReferences interestingRefs;

    /**
     * @param graph SCC of an FIGraph
     * @param dispatch Instance controlling how references are transformed by dispatching specific transformers
     * @param itpfFact factory creating formulas for this problem.
     * @param sccAnns information relating to the whole SCC
     * @param args Arguments of the calling conversion processor
     * @param aborter the aborter
     * @throws AbortionException when the aborter kicks in
     */
    public RuleCreator(
        final JBCGraph graph,
        final ConverterArguments args,
        final TransformationDispatcher dispatch,
        final SCCAnnotations sccAnns,
        final ItpfFactory itpfFact,
        final Abortion aborter) throws AbortionException
    {
        assert (args.useFlatEncoding) : "Only flat term encoding supported.";
        this.arguments = args;
        this.dispatcher = dispatch;
        this.itpfFactory = itpfFact;
        this.sccAnnotations = sccAnns;
        if (this.arguments.encodeOnlyInterestingRefs) {
            this.interestingRefs = new InterestingReferences(graph, false, aborter);
        } else {
            this.interestingRefs = null;
        }
    }

    /**
     * @param ref some reference
     * @param state the enclosing state
     * @return true if this reference should be encoded in the result
     */
    private boolean shouldEncodeRef(final AbstractVariableReference ref, final State state) {
        if (this.arguments.encodeOnlyInterestingRefs) {
            return this.interestingRefs.isOfInterestFor(ref, state);
        } else {
            return true;
        }
    }

    /**
     * Converts a single edge from the FIGraph to an ITRS rule.
     * @param edge Some edge from the transformed SCC that should be translated to a rule
     * @param forComplexity Creates COM symbols on the RHS, overrides whatever value <code>encodeMethodReturns</code> has.
     * @param encodeMethodReturns if true, method calls will be properly encoded, i.e., we have rules of the form f(x,y)
     * -> f(g(x),y) and f(g_end(z), y) -> h(z, y). If false, we will not try to use the information from the method
     * return and generate rules f(x,y) -> g(x) and f(x,y) -> h(z, y).
     * @return a rule corresponding to <code>edge</code>
     */
    public Collection<IRule> convert(final Edge edge, final boolean forComplexity, final boolean encodeMethodReturns) {
        final State startState = edge.getStart().getState();
        final State endState = edge.getEnd().getState();
        final EdgeInformation info = edge.getLabel();

        ISubstitution rhsSubst = ISubstitution.emptySubstitution();
        ITerm<BooleanRing> edgeConstraint = null;
        ReferenceAccessInformation changedConnectionInformation = null;

        final MarkerFieldAnalysis markerAnalysis =
            (MarkerFieldAnalysis) this.sccAnnotations.getAnalysis(MarkerFieldAnalysis.class);

        // Check variable information on the edge for stuff we can use:
        for (final VariableInformation vi : info) {
            if (vi instanceof IntegerResultInformation) {
                /*
                 * If we computed a new integer (i.e. i3 = i1 X i2), then we
                 * need to substitute i3 by X(i1,i2) on the right hand side:
                 */
                rhsSubst =
                    rhsSubst.termCompose(this.getSubstitutionFromIntegerComputation(
                        (IntegerResultInformation) vi,
                        startState));
                /*
                 * In some cases we also want to note if the variables are zero
                 * or one.
                 */
                final ITerm<BooleanRing> resultTerm =
                    this.getConstraintFromIntegerComputation((IntegerResultInformation) vi, startState, endState);
                edgeConstraint = RuleCreator.getConjunction(edgeConstraint, resultTerm);
            }

            /*
             * If we have asserted an integer relation (by refinement or split),
             * then we want to add the according condition to the rule.
             */
            if (vi instanceof JBCIntegerRelation) {
                final JBCIntegerRelation iR = (JBCIntegerRelation) vi;
                final AbstractVariableReference leftRef = iR.getLeftIntRef();
                final AbstractVariableReference rightRef;
                if (iR.rightIntegerIsNoRef()) {
                    rightRef = null;
                } else {
                    rightRef = iR.getRightIntRef();
                }

                /*
                 * Only mark these if the references will be encoded in one of
                 * the two states:
                 */
                if (((this.shouldEncodeRef(leftRef, startState) || (this.shouldEncodeRef(leftRef, endState))))
                    && (rightRef == null || (this.shouldEncodeRef(rightRef, startState) || (this.shouldEncodeRef(
                        rightRef,
                        endState)))))
                {
                    final IFunctionApplication<BooleanRing> relationTerm =
                        RuleCreator.getRelationTermFromIntegerRelation(
                            (JBCIntegerRelation) vi,
                            this.dispatcher,
                            startState);
                    edgeConstraint = RuleCreator.getConjunction(edgeConstraint, relationTerm);
                }
            }

            // Find the reference written to, if any exists.
            if (vi instanceof ReferenceAccessInformation) {
                final ReferenceAccessInformation rA = (ReferenceAccessInformation) vi;
                if (rA.isWrite()) {
                    changedConnectionInformation = rA;

                    //Check if this relevant for a marker field:
                    if (rA instanceof InstanceAccessInformation && markerAnalysis != null) {
                        final InstanceAccessInformation iAI = (InstanceAccessInformation) rA;
                        final FieldIdentifier writtenFieldId = iAI.getFieldIdentifier();
                        for (final Entry<FieldRelation, AbstractVariableReference> e : markerAnalysis
                            .getMarkerVarNames()
                            .entrySet())
                        {
                            final FieldRelation fieldRel = e.getKey();
                            if (!fieldRel.getFieldInRelation().equals(writtenFieldId)) {
                                continue;
                            }

                            final AbstractVariableReference oldValueRef = iAI.getOverwrittenRef();
                            final AbstractVariableReference newValueRef = iAI.getReadOrWrittenRef();

                            final int counterChange =
                                RuleCreator.counterChangeForFieldRelation(edge, fieldRel, oldValueRef, newValueRef);

                            if (counterChange > 0) {
                                markerAnalysis.noteIncrease(fieldRel);
                            }

                            final AbstractVariableReference markCounter = e.getValue();
                            final IVariable<BigInt> counterVar =
                                this.dispatcher.<BigInt>getVariable(
                                    markCounter,
                                    Collections.<AbstractVariableReference>emptySet(),
                                    startState);
                            final IFunctionSymbol<BigInt> add =
                                IDPPredefinedMap.DEFAULT_MAP.<BigInt>getFunctionSymbolChecked(
                                    PredefinedFunction.Func.Add,
                                    DomainFactory.INTEGER_INTEGER);

                            rhsSubst =
                                rhsSubst.extend(ISubstitution.create(
                                    counterVar,
                                    ITerm.createFunctionApplication(
                                        add,
                                        counterVar,
                                        IntegerTransformer.getConstantIntegerTerm(counterChange))));

                            //Require that this is always non-negative:
                            final IFunctionSymbol<BooleanRing> ge =
                                IDPPredefinedMap.DEFAULT_MAP.<BooleanRing>getFunctionSymbolChecked(
                                    PredefinedFunction.Func.Ge,
                                    DomainFactory.INTEGER_INTEGER);
                            final IFunctionApplication<BooleanRing> relationTerm =
                                ITerm.createFunctionApplication(
                                    ge,
                                    counterVar,
                                    IntegerTransformer.getConstantIntegerTerm(0));
                            edgeConstraint = RuleCreator.getConjunction(edgeConstraint, relationTerm);
                        }
                    }
                }

                final AbstractVariableReference accessedRef = rA.getAccessedRef();
                if (this.arguments.encodePathLength) {
                    if (rA.isRead()
                        && accessedRef.pointsToReferenceType()
                        && !startState.getHeapAnnotations().getCyclicStructures().isCyclic(accessedRef))
                    {
                        final IVariable<BigInt> readInstLength =
                            this.dispatcher.getVariableLength(accessedRef, startState);
                        final IVariable<BigInt> readResLength =
                            this.dispatcher.getVariableLength(rA.getReadOrWrittenRef(), endState);
                        final IFunctionSymbol<BooleanRing> gt =
                            IDPPredefinedMap.DEFAULT_MAP.<BooleanRing>getFunctionSymbolChecked(
                                PredefinedFunction.Func.Gt,
                                DomainFactory.INTEGER_INTEGER);
                        final IFunctionSymbol<BigInt> add =
                            IDPPredefinedMap.DEFAULT_MAP.<BigInt>getFunctionSymbolChecked(
                                PredefinedFunction.Func.Add,
                                DomainFactory.INTEGER_INTEGER);

                        rhsSubst =
                            rhsSubst.extend(ISubstitution.create(
                                readResLength,
                                ITerm.createFunctionApplication(
                                    add,
                                    readInstLength,
                                    IntegerTransformer.getConstantIntegerTerm(-1))));

                        final IFunctionApplication<BooleanRing> nonNullCond =
                            ITerm.createFunctionApplication(
                                gt,
                                readInstLength,
                                IntegerTransformer.getConstantIntegerTerm(0));
                        edgeConstraint = RuleCreator.getConjunction(edgeConstraint, nonNullCond);
                    }
                }
            }

            if (vi instanceof ObjectCreationInformation) {
                final ObjectCreationInformation oci = (ObjectCreationInformation) vi;

                if (this.arguments.encodePathLength) {
                    rhsSubst =
                        rhsSubst.extend(ISubstitution.create(
                            this.dispatcher.getVariableLength(oci.getRef(), endState),
                            IntegerTransformer.getConstantIntegerTerm(1)));
                }

                //Note if we create a new object of this type:
                if (markerAnalysis != null) {
                    final ClassName createdClass = oci.getCreatedClass();
                    final TypeTree createdType = startState.getClassPath().getTypeTree(createdClass);
                    for (final Entry<FieldRelation, AbstractVariableReference> e : markerAnalysis
                        .getMarkerVarNames()
                        .entrySet())
                    {
                        final FieldRelation fieldRel = e.getKey();
                        final ClassName enclosingClass = fieldRel.getFieldInRelation().getClassName();

                        if (createdType.isSubClassOf(enclosingClass)) {
                            final AbstractVariableReference markCounter = e.getValue();
                            final IVariable<BigInt> counterVar =
                                this.dispatcher.<BigInt>getVariable(
                                    markCounter,
                                    Collections.<AbstractVariableReference>emptySet(),
                                    startState);
                            final IFunctionSymbol<BigInt> add =
                                IDPPredefinedMap.DEFAULT_MAP.<BigInt>getFunctionSymbolChecked(
                                    PredefinedFunction.Func.Add,
                                    DomainFactory.INTEGER_INTEGER);

                            final int counterChange =
                                RuleCreator.counterChangeForFieldRelation(
                                    edge,
                                    fieldRel,
                                    null,
                                    AbstractVariableReference.create(AbstractInt.getZero(), OperandType.INTEGER));

                            if (counterChange > 0) {
                                rhsSubst =
                                    rhsSubst.extend(ISubstitution.create(
                                        counterVar,
                                        ITerm.createFunctionApplication(
                                            add,
                                            counterVar,
                                            IntegerTransformer.getConstantIntegerTerm(1))));
                                markerAnalysis.noteIncrease(fieldRel);
                            }
                        }
                    }
                }
            }

            if (this.arguments.encodeReferenceDistances && vi instanceof DefiniteReachabilityAnnotationCreation) {
                final DefiniteReachabilityAnnotationCreation drac = (DefiniteReachabilityAnnotationCreation) vi;

                final IVariable<BigInt> oldVar =
                    TransformationDispatcher.createDefiniteReachabilityVariable(
                        drac.getOldAnnotation(),
                        null,
                        false);
                final boolean sameVar = drac.getOldAnnotation().equals(drac.getNewAnnotation());
                final IVariable<BigInt> newVar =
                    TransformationDispatcher.createDefiniteReachabilityVariable(drac.getNewAnnotation(), null, sameVar);
                if (sameVar) {
                    final IVariable<BigInt> varWithoutNew =
                        TransformationDispatcher.createDefiniteReachabilityVariable(
                            drac.getNewAnnotation(),
                            null,
                            false);
                    rhsSubst = rhsSubst.extend(ISubstitution.create(varWithoutNew, newVar));
                }

                final IFunctionSymbol<BooleanRing> rel;
                Func func;
                switch (drac.getRelation()) {
                case EQ:
                    func = PredefinedFunction.Func.Eq;
                    break;
                case GE:
                    func = PredefinedFunction.Func.Ge;
                    break;
                case GT:
                    func = PredefinedFunction.Func.Gt;
                    break;
                case LE:
                    func = PredefinedFunction.Func.Le;
                    break;
                case LT:
                    func = PredefinedFunction.Func.Lt;
                    break;
                default:
                    func = null;
                    assert (false);
                }
                rel =
                    IDPPredefinedMap.DEFAULT_MAP.<BooleanRing>getFunctionSymbolChecked(
                        func,
                        DomainFactory.INTEGER_INTEGER);
                final IFunctionApplication<BooleanRing> dracCond = ITerm.createFunctionApplication(rel, newVar, oldVar);

                edgeConstraint = RuleCreator.getConjunction(edgeConstraint, dracCond);

                // for the old DefReach annotation mark that its length is >= 0
                final IFunctionSymbol<BooleanRing> ge =
                    IDPPredefinedMap.DEFAULT_MAP.<BooleanRing>getFunctionSymbolChecked(
                        PredefinedFunction.Func.Ge,
                        DomainFactory.INTEGER_INTEGER);
                final IFunctionApplication<BigInt> zero = IntegerTransformer.getConstantIntegerTerm(0);
                final IFunctionApplication<BooleanRing> geZero = ITerm.createFunctionApplication(ge, oldVar, zero);
                edgeConstraint = RuleCreator.getConjunction(edgeConstraint, geZero);
            }
        }

        if (info instanceof EvaluationEdge || info instanceof InitializationStateChange) {
            return this.convertEvaluationEdge(
                edge,
                forComplexity,
                rhsSubst,
                edgeConstraint,
                changedConnectionInformation,
                encodeMethodReturns);
        } else if (info instanceof RefinementEdge || info instanceof SplitEdge) {
            return this.convertRefinementEdge(edge, forComplexity, rhsSubst, edgeConstraint);
        } else if (info instanceof InstanceEdge) {
            return this.convertInstanceEdge(edge, forComplexity);
        } else if (info instanceof CallAbstractEdge) {
            return this.convertCallAbstractEdge(edge, forComplexity, encodeMethodReturns);
        } else if (info instanceof MethodSkipEdge) {
            return this.convertMethodSkipEdge(edge, forComplexity, encodeMethodReturns);
        }

        return Collections.<IRule>emptySet();
    }

    private static int counterChangeForFieldRelation(
        final Edge edge,
        final FieldRelation fieldRel,
        final AbstractVariableReference oldValueRef,
        final AbstractVariableReference newValueRef)
    {
        /*
         * Check by SMT:
         *  (1) Get maximal path to collect all relevant information,
         *  (2) Convert path to SMT formula
         *  (3) Check if (oldVal REL) and (newVal REL) hold/don't hold
         *  (4) Compute change from these truth values
         */

        // Get the path:
        final LinkedList<Edge> maxPath = new LinkedList<>();
        Node curNode = edge.getStart();
        final Set<Node> visitedNodes = new LinkedHashSet<>();
        while (curNode.getInEdges().size() == 1) {
            if (!visitedNodes.add(curNode)) {
                break;
            }
            final Edge inEdge = curNode.getInEdges().iterator().next();
            if (inEdge.getLabel() instanceof InstanceEdge) {
                break;
            }
            maxPath.addFirst(inEdge);
            curNode = inEdge.getStart();
        }

        // Convert to SMT:
        final Pair<List<SMTLIBTheoryAtom>, List<SMTLIBTheoryAtom>> pathFormulae =
            SMTUtilities.convertPathToSMTFormulas(maxPath, null, "", false);

        final List<SMTLIBTheoryAtom> allFormulae = new LinkedList<>();
        allFormulae.addAll(pathFormulae.x);
        allFormulae.addAll(pathFormulae.y);

        // Check if fieldRel holds for the old value:
        final FormulaFactory<SMTLIBTheoryAtom> factory = new AtomCachingFactory<>();
        final Formula<SMTLIBTheoryAtom> contextFormula = factory.buildAnd(factory.buildTheoryAtoms(allFormulae));

        if (oldValueRef != null) {
            final boolean oldFieldValueSatisfiesRel =
                RuleCreator.fieldRelTruthValueForRef(fieldRel, oldValueRef, contextFormula, true, factory);
            if (oldFieldValueSatisfiesRel) {
                final boolean newFieldValueDoesNotSatisfyRel =
                    RuleCreator.fieldRelTruthValueForRef(fieldRel, newValueRef, contextFormula, false, factory);
                //Old one satisfied, new one doesn't => Decrease
                if (newFieldValueDoesNotSatisfyRel) {
                    return -1;
                } else {
                    //Old one satisfied, new one does => No change or decrease, approximate:
                    return 0;
                }
            }
        }

        //This is for the object creation case: There was no old value...
        final boolean oldFieldValueDoesNotSatisfyRel;
        if (oldValueRef != null) {
            oldFieldValueDoesNotSatisfyRel =
                RuleCreator.fieldRelTruthValueForRef(fieldRel, oldValueRef, contextFormula, false, factory);
        } else {
            oldFieldValueDoesNotSatisfyRel = true;
        }

        if (oldFieldValueDoesNotSatisfyRel) {
            final boolean newFieldValueDoesNotSatisfyRel =
                RuleCreator.fieldRelTruthValueForRef(fieldRel, newValueRef, contextFormula, false, factory);
            //Old didn't satisfy, new one doesn't => No change:
            if (newFieldValueDoesNotSatisfyRel) {
                return 0;
            }
        }

        return 1;
    }

    /**
     * @param fieldRel Some field relation
     * @param ref Some reference that should be used in that
     * @param contextFormula SMT formula encoding context information
     * @param proveOrDisprove indicates if we want to prove the relation or its negation
     * @return
     */
    private static boolean fieldRelTruthValueForRef(
        final FieldRelation fieldRel,
        final AbstractVariableReference ref,
        final Formula<SMTLIBTheoryAtom> contextFormula,
        final boolean proveOrDisprove,
        final FormulaFactory<SMTLIBTheoryAtom> factory)
    {

        // Convert fieldRel + ref to SMT values
        final SMTLIBIntValue refSMT = ref.toSMTIntValue("");
        final SMTLIBIntValue cmpRefSMT = fieldRel.getRelatedReference().toSMTIntValue("");

        final SMTLIBTheoryAtom fieldRelFormula;

        // FIXME Code and documentation do not fit together in the next 7 lines
        //If we want to prove that it holds, we need to show UNSAT for the inverted relation
        if (proveOrDisprove) {
            fieldRelFormula = fieldRel.getRelationType().toSMTAtom(refSMT, cmpRefSMT);
            //If we want to prove that it not holds, we need to show UNSAT for the normal relation
        } else {
            fieldRelFormula = fieldRel.getRelationType().invert().toSMTAtom(refSMT, cmpRefSMT);
        }

        // Construct formula as !(context -> fieldRel), prove
        final Formula<SMTLIBTheoryAtom> formula =
            factory.buildNot(factory.buildImplication(contextFormula, factory.buildTheoryAtom(fieldRelFormula)));

        final SMTEngine smtEngine = new SMTLIBEngine();
        try {
            YNM res;
            try {
                res =
                    smtEngine
                        .satisfiable(Collections.singletonList(formula), SMTLogic.QF_NIA, AbortionFactory.create());
            } catch (final WrongLogicException e) {
                System.err.println("Solver error: " + e.getErrorMessage());
                res = YNM.MAYBE;
            }
            if (res == YNM.NO) {
                return true;
            }
        } catch (final AbortionException e) {
            return false;
        }

        return false;
    }

    /**
     * @param edge the evaluation edge to convert.
     * @param rhsSubst a substitution mapping new variable names to old names.
     * @param edgeConstraint a constrain generated from the information on the edge.
     * @param changedConnectionInformation an encoding of the heap connection that was changed in this evaluation (or
     * null, if no such change exists).
     * @param encodeMethodReturns if true, method calls will be properly encoded, i.e., we have rules of the form
     * <ul>
     * <li>f(x,y) -eval-> f_1(f_0(x),y)</li>
     * <li>f_0(x) -callAbstract-> g(x)</li>
     * <li>f_1(g_end(z),y) -MethodSkip-> h(z,y)</li>
     * </ul>
     * If false, we will not try to use the information from the method return and generate rules
     * <ul>
     * <li>f(x,y) -eval-> f_1(x,y)</li>
     * <li>f(x,y) -eval-> f_0(x)</li>
     * <li>f_0(x) -callAbstract-> g(x)</li>
     * <li>f_1(x, y) -MethodSkip-> h(z,y)</li>
     * </ul>
     * @return a rule corresponding to <code>edge</code> (according to RTA'10, RTA'11 papers).
     */
    @SuppressWarnings("unchecked")
    private Collection<IRule> convertEvaluationEdge(
        final Edge edge,
        final boolean forComplexity,
        final ISubstitution rhsSubst,
        final ITerm<BooleanRing> edgeConstraint,
        final ReferenceAccessInformation changedConnectionInformation,
        final boolean encodeMethodReturns)
    {
        final Node startNode = edge.getStart();
        final String startID = startNode.getNodeNumber() + "";
        final State startState = startNode.getState();
        final Node endNode = edge.getEnd();
        final String endID = endNode.getNodeNumber() + "";
        final State endState = endNode.getState();

        final IFunctionApplication<UnknownRing> lhs;

        lhs = this.getFlatTermForState(startState, startID);
        ITerm<BooleanRing> extraIntInfo = null;

        final Collection<IFunctionApplication<UnknownRing>> rhss = new LinkedList<>();
        if (changedConnectionInformation != null) {
            final AbstractVariableReference changedRef = changedConnectionInformation.getAccessedRef();
            final Set<AbstractVariableReference> possiblePredecessors = new LinkedHashSet<>();
            possiblePredecessors.addAll(startState
                .getHeapAnnotations()
                .getJoiningStructures()
                .getReferencesWithPartner(changedRef));
            /*
             * As we wrote to a ref, we will need to replace the abstract (i.e.
             * non-concrete) predecessors of the changed with fresh variables
             * to ensure correctness of our translation:
             */
            rhss.add(this.getFlatTermForState(
                endState,
                null,
                null,
                endID,
                changedConnectionInformation,
                possiblePredecessors,
                endState.getCallStack().size() - 1,
                0,
                0));
        } else {
            /*
             * We need to create two stackframes for the case that we are
             * abstracting in the next step:
             */
            final Set<Edge> followingEdges = endNode.getOutEdges();
            boolean hasAbstractEdge = false;
            boolean hasSkipEdge = false;
            boolean hasOtherEdge = false;

            State stateForTopFrame = null;

            for (final Edge e : followingEdges) {
                if (e.getLabel() instanceof CallAbstractEdge) {
                    hasAbstractEdge = true;
                    stateForTopFrame = e.getEnd().getState();
                } else if (e.getLabel() instanceof MethodSkipEdge) {
                    hasSkipEdge = true;
                } else {
                    hasOtherEdge = true;
                }
            }
            assert (!(hasAbstractEdge && hasOtherEdge));
            if (hasSkipEdge || hasAbstractEdge) {
                final IFunctionApplication<UnknownRing> inCalledMethodRhs;

                //If we don't encode methods properly, get some additional integer information here. Is useful for TerminatorRec01, for example
                if (!encodeMethodReturns) {
                    for (final AbstractVariableReference ref : startState.getReferences().keySet()) {
                        if (ref.pointsToInteger()) {
                            extraIntInfo =
                                RuleCreator.getConjunction(
                                    extraIntInfo,
                                    RuleCreator.getRelationTermRelativeToInteger(ref, 1, this.dispatcher, startState));
                        }
                    }
                    for (final JBCIntegerRelation rel : startState.getIntegerRelations().getRelations()) {
                        extraIntInfo =
                            RuleCreator.getConjunction(
                                extraIntInfo,
                                RuleCreator.getRelationTermFromIntegerRelation(rel, this.dispatcher, startState));
                    }
                }

                if (stateForTopFrame != null) {
                    inCalledMethodRhs = this.getFlatTermForState(stateForTopFrame, endID);
                } else {
                    inCalledMethodRhs =
                        this.getFlatTermForState(
                            endState,
                            null,
                            null,
                            endID,
                            null,
                            Collections.<AbstractVariableReference>emptySet(),
                            0,
                            0,
                            0);
                }
                if (encodeMethodReturns && !forComplexity) {
                    IFunctionApplication<UnknownRing> outerRhs;

                    outerRhs =
                        this.getFlatTermForState(
                            endState,
                            null,
                            null,
                            endID,
                            null,
                            Collections.<AbstractVariableReference>emptySet(),
                            endState.getCallStack().size() - 1,
                            1,
                            1);

                    rhss.add((IFunctionApplication<UnknownRing>) outerRhs.replaceAt(
                        IPosition.create(new int[] {0 }),
                        inCalledMethodRhs));
                } else {
                    //For the call, we don't need to do nesting (it will be continued by the call abstract edge)
                    rhss.add(inCalledMethodRhs);
                    //For the rest, encode the full state (it will be continued by the method skip edge)
                    rhss.add(this.getFlatTermForState(
                        endState,
                        null,
                        null,
                        endID,
                        null,
                        Collections.<AbstractVariableReference>emptySet(),
                        endState.getCallStack().size() - 1,
                        0,
                        1));
                }
            } else {
                rhss.add(this.getFlatTermForState(
                    endState,
                    null,
                    null,
                    endID,
                    null,
                    Collections.<AbstractVariableReference>emptySet(),
                    endState.getCallStack().size() - 1,
                    0,
                    0));
            }
        }
        final LinkedList<IRule> res = new LinkedList<>();

        if (forComplexity) {
            final ArrayList<IFunctionApplication<UnknownRing>> rhsFAs = new ArrayList<>();
            final IFunctionSymbol<UnknownRing> compoundSym =
                IFunctionSymbol.createChecked(
                    CpxIntTermHelper.ComPrefix + rhss.size(),
                    rhss.size(),
                    IDPPredefinedMap.DEFAULT_MAP);
            for (final IFunctionApplication<UnknownRing> rhs : rhss) {
                rhsFAs.add(rhs.applySubstitution(rhsSubst));
            }
            res.add(IRuleFactory.createWithExQuantifiedFreeVars(
                lhs,
                new IFunctionApplication<>(compoundSym, ImmutableCreator.create(rhsFAs)),
                RuleCreator.getConjunction(extraIntInfo, edgeConstraint),
                IDPPredefinedMap.DEFAULT_MAP,
                this.itpfFactory,
                true));
        } else {
            for (final IFunctionApplication<UnknownRing> rhs : rhss) {
                final IFunctionApplication<UnknownRing> rhsFinal = rhs.applySubstitution(rhsSubst);
                res.add(IRuleFactory.createWithExQuantifiedFreeVars(
                    lhs,
                    rhsFinal,
                    RuleCreator.getConjunction(extraIntInfo, edgeConstraint),
                    IDPPredefinedMap.DEFAULT_MAP,
                    this.itpfFactory,
                    true));
            }
        }

        return res;
    }

    /**
     * @param edge the refinement edge to convert.
     * @param rhsSubst a substitution mapping new variable names to old names.
     * @param originalEdgeConstraint a constrain generated from the information on the edge.
     * @return a rule corresponding to <code>edge</code> (according to RTA'10, RTA'11 papers).
     */
    private Collection<IRule> convertRefinementEdge(
        final Edge edge,
        final boolean forComplexity,
        final ISubstitution rhsSubst,
        final ITerm<BooleanRing> originalEdgeConstraint)
    {
        final Node startNode = edge.getStart();
        final String startID = startNode.getNodeNumber() + "";
        final State startState = startNode.getState();
        final Node endNode = edge.getEnd();
        final String endID = endNode.getNodeNumber() + "";
        final State endState = endNode.getState();
        ITerm<BooleanRing> edgeConstraint = originalEdgeConstraint;

        /*
         * This maps refs from the start state to a set of refs in the end
         * state. However, in the case of refinements, these should be singleton
         * sets:
         */
        final CollectionMap<AbstractVariableReference, AbstractVariableReference> refStartToEndRenaming =
            edge.getRefRenamingStartToEnd(null);
        final Map<AbstractVariableReference, AbstractVariableReference> refStartToEndRenamingMap =
            new LinkedHashMap<>();
        for (final Entry<AbstractVariableReference, Collection<AbstractVariableReference>> entry : refStartToEndRenaming
            .entrySet())
        {
            final AbstractVariableReference key = entry.getKey();
            assert (refStartToEndRenaming.get(key).size() <= 1) : "One ref in abstract state used to represent several refs from concrete state";
            refStartToEndRenamingMap.put(key, entry.getValue().iterator().next());
        }

        if (edge.getLabel() instanceof NEQRefinementEdge) {
            final NEQRefinementEdge neqRef = (NEQRefinementEdge) edge.getLabel();
            for (final DefiniteReachabilityAnnotation dra : startState.getHeapAnnotations().getDefiniteReachabilities())
            {
                if (this.arguments.encodeReferenceDistances && neqRef.hasRef(dra.getFrom())
                    && neqRef.hasRef(dra.getTo())) {
                    final IVariable<BigInt> var =
                        TransformationDispatcher.createDefiniteReachabilityVariable(
                            dra,
                            refStartToEndRenamingMap,
                            false);

                    final IFunctionSymbol<BooleanRing> gt =
                        IDPPredefinedMap.DEFAULT_MAP.<BooleanRing>getFunctionSymbolChecked(
                            PredefinedFunction.Func.Gt,
                            DomainFactory.INTEGER_INTEGER);

                    final IFunctionApplication<BooleanRing> gtNullCond =
                        ITerm.createFunctionApplication(gt, var, IntegerTransformer.getConstantIntegerTerm(0));

                    edgeConstraint = RuleCreator.getConjunction(edgeConstraint, gtNullCond);
                }
            }
        }

        final IFunctionApplication<UnknownRing> lhs;
        final IFunctionApplication<UnknownRing> rhs;
        lhs =
            this.getFlatTermForState(
                startState,
                endState,
                refStartToEndRenamingMap,
                startID,
                null,
                Collections.<AbstractVariableReference>emptySet(),
                endState.getCallStack().size() - 1,
                0,
                0,
                edge.getLabel());
        rhs = this.getFlatTermForState(endState, endID).applySubstitution(rhsSubst);

        if (forComplexity) {
            final IFunctionSymbol<UnknownRing> compoundSym =
                IFunctionSymbol.createChecked(CpxIntTermHelper.ComPrefix + "1", 1, IDPPredefinedMap.DEFAULT_MAP);
            return Collections.singleton(IRuleFactory.createWithExQuantifiedFreeVars(
                lhs,
                IFunctionApplication.<UnknownRing>create(compoundSym, rhs),
                edgeConstraint,
                IDPPredefinedMap.DEFAULT_MAP,
                this.itpfFactory,
                true));
        } else {
            return Collections.singleton(IRuleFactory.createWithExQuantifiedFreeVars(
                lhs,
                rhs,
                edgeConstraint,
                IDPPredefinedMap.DEFAULT_MAP,
                this.itpfFactory,
                true));
        }
    }

    /**
     * @param edge the instance edge to convert.
     * @return a rule corresponding to <code>edge</code> (according to RTA'10, RTA'11 papers).
     */
    private Collection<IRule> convertInstanceEdge(final Edge edge, final boolean forComplexity) {
        final Node startNode = edge.getStart();
        final String startID = startNode.getNodeNumber() + "";
        final State startState = startNode.getState();
        final Node endNode = edge.getEnd();
        final String endID = endNode.getNodeNumber() + "";
        final State endState = endNode.getState();

        // For instantiations, encode the second term with the values and refs
        // of the first:
        final IFunctionApplication<UnknownRing> lhs;

        lhs = this.getFlatTermForState(startState, startID);

        /*
         * This maps refs from the end state to a set of refs in the start
         * state. However, in the case of instatiations, these should be
         * singleton sets:
         */
        final CollectionMap<AbstractVariableReference, AbstractVariableReference> refEndToStartRenaming =
            edge.getRefRenamingEndToStart(null);
        final Map<AbstractVariableReference, AbstractVariableReference> refEndToStartRenamingMap =
            new LinkedHashMap<>();
        for (final Entry<AbstractVariableReference, Collection<AbstractVariableReference>> entry : refEndToStartRenaming
            .entrySet())
        {
            final AbstractVariableReference key = entry.getKey();
            assert (refEndToStartRenaming.get(key).size() <= 1) : "One ref in abstract state used to represent several refs from concrete state";
            refEndToStartRenamingMap.put(key, entry.getValue().iterator().next());
        }

        final IFunctionApplication<UnknownRing> rhs;
        rhs =
            this.getFlatTermForState(
                endState,
                startState,
                refEndToStartRenamingMap,
                endID,
                null,
                Collections.<AbstractVariableReference>emptySet(),
                endState.getCallStack().size() - 1,
                0,
                0);


        ITerm<BooleanRing> cond = null;
        if (this.arguments.encodeReferenceDistances) {
            final DefiniteReachabilities abstrDefReaches = endState.getHeapAnnotations().getDefiniteReachabilities();

            /*
             * We possibly have definite reachability annotations in the target
             * state that did not exist in the source state because the
             * corresponding references had an _existing_ connection. Hence,
             * search for such annotations and replace them by the length of the
             * existing connection.
             */
            final DefiniteReachabilities concrDefReaches = startState.getHeapAnnotations().getDefiniteReachabilities();
            HeapPositions concrHeapPos = null;
            nextDra: for (final DefiniteReachabilityAnnotation abstrDra : abstrDefReaches) {
                final AbstractVariableReference abstrFromRef = abstrDra.getFrom();
                final AbstractVariableReference abstrToRef = abstrDra.getTo();
                final AbstractVariableReference concrFromRef = refEndToStartRenamingMap.get(abstrFromRef);
                final AbstractVariableReference concrToRef = refEndToStartRenamingMap.get(abstrToRef);

                if (concrFromRef == null || concrToRef == null) {
                    continue;
                }

                //Find the corresponding annotation:
                DefiniteReachabilityAnnotation concrDra = null;
                for (final DefiniteReachabilityAnnotation curConcrDra : concrDefReaches) {
                    if (curConcrDra.getFrom().equals(concrFromRef) && curConcrDra.getTo().equals(concrToRef)
                        && abstrDra.getFields().containsAll(curConcrDra.getFields())) {
                        //Yay we have a winner!
                        concrDra = curConcrDra;
                        break;
                    }
                }

                if (concrDra != null) {
                    continue;
                }

                /*
                 * No fitting annotation, so there is supposedly a concrete
                 * connection between concrFromRef and concrToRef. Find it, and
                 * compute its length:
                 */
                if (concrHeapPos == null) {
                    concrHeapPos = new HeapPositions(startState, true);
                }

                // we want to find out the length between concrFromRef and concrToRef
                final Collection<StatePosition> concrToPoses = concrHeapPos.getPositionsForRef(concrToRef);
                final Collection<StatePosition> concrFromPoses = concrHeapPos.getPositionsForRef(concrFromRef);
                for (final StatePosition concrToPos : concrToPoses) {
                    for (final StatePosition concrFromPos : concrFromPoses) {
                        if (!concrFromPos.isPrefixOf(concrToPos)) {
                            // concrToRef is not reachable from concrFromRef
                            continue;
                        }
                        final NonRootPosition connection = concrToPos.getSuffixOf(concrFromPos);

                        //This is the abstracted connection:
                        Integer length = null;
                        if (connection != null && abstrDra.getFields().containsAll(connection.getHeapEdges())) {
                            length = connection.length();
                        } else if (connection == null) {
                            /*
                             * The suffix is epsilon, meaning the two positions are the same.
                             * Check for realized cycles starting in the current position.
                             */
                            int cycleLength = 0;
                            for (final NonRootPosition nrp : concrHeapPos.getContinuations(concrFromPos)) {
                                final Collection<HeapEdge> edgesOnContinuation = nrp.getHeapEdges();
                                if (abstrDra.getFields().containsAll(edgesOnContinuation)) {
                                    cycleLength = nrp.length();
                                    break;
                                }
                            }
                            if (!abstrDra.isAtLeastOneStep() || cycleLength > 0) {
                                length = cycleLength;
                            }
                        }
                        if (length != null) {
                            final IVariable<BigInt> abstrDraVar =
                                TransformationDispatcher.createDefiniteReachabilityVariable(abstrDra,
                                    refEndToStartRenamingMap, false);
                            final IFunctionSymbol<BooleanRing> eq =
                                IDPPredefinedMap.DEFAULT_MAP.<BooleanRing>getFunctionSymbolChecked(
                                    PredefinedFunction.Func.Eq, DomainFactory.INTEGER_INTEGER);
                            final IFunctionApplication<BooleanRing> abstrDraEq =
                                ITerm.createFunctionApplication(eq, abstrDraVar,
                                    IntegerTransformer.getConstantIntegerTerm(length));
                            cond = RuleCreator.getConjunction(cond, abstrDraEq);
                            continue nextDra;
                        }
                    }
                }
            }
        }

        if (forComplexity) {
            final IFunctionSymbol<UnknownRing> compoundSym =
                IFunctionSymbol.createChecked(CpxIntTermHelper.ComPrefix + "1", 1, IDPPredefinedMap.DEFAULT_MAP);
            return Collections.singleton(IRuleFactory.createWithExQuantifiedFreeVars(
                lhs,
                IFunctionApplication.<UnknownRing>create(compoundSym, rhs),
                cond,
                IDPPredefinedMap.DEFAULT_MAP,
                this.itpfFactory,
                true));
        } else {
            return Collections.singleton(IRuleFactory.createWithExQuantifiedFreeVars(
                lhs,
                rhs,
                cond,
                IDPPredefinedMap.DEFAULT_MAP,
                this.itpfFactory,
                true));
        }
    }

    /**
     * @param edge the call abstract edge to convert.
     * @param encodeMethodReturns if true, method calls will be properly encoded, i.e., we have rules of the form
     * <ul>
     * <li>f(x,y) -eval-> f_1(f_0(x),y)</li>
     * <li>f_0(x) -callAbstract-> g(x)</li>
     * <li>f_1(g_end(z),y) -MethodSkip-> h(z,y)</li>
     * </ul>
     * If false, we will not try to use the information from the method return and generate rules
     * <ul>
     * <li>f(x,y) -eval-> f_1(x,y)</li>
     * <li>f(x,y) -eval-> f_0(x)</li>
     * <li>f_0(x) -callAbstract-> g(x)</li>
     * <li>f_1(x, y) -MethodSkip-> h(z,y)</li>
     * </ul>
     * @return a rule corresponding to <code>edge</code> (according to RTA'10, RTA'11 papers).
     */
    private Collection<IRule> convertCallAbstractEdge(
        final Edge edge,
        final boolean forComplexity,
        final boolean encodeMethodReturns)
    {
        final Node startNode = edge.getStart();
        final String startID = startNode.getNodeNumber() + "";
        final Node endNode = edge.getEnd();
        final String endID = endNode.getNodeNumber() + "";
        final State endState = endNode.getState();

        // There was no abstraction step needed for this call:
        final IFunctionApplication<UnknownRing> lhs;

        // Only relable the topmost stackframe of the lhs here:
        lhs = this.getFlatTermForState(endState, startID);

        final IFunctionApplication<UnknownRing> rhs;
        rhs = this.getFlatTermForState(endState, endID, 0);

        if (forComplexity) {
            final IFunctionSymbol<UnknownRing> compoundSym =
                IFunctionSymbol.createChecked(CpxIntTermHelper.ComPrefix + "1", 1, IDPPredefinedMap.DEFAULT_MAP);
            return Collections.singleton(IRuleFactory.createWithExQuantifiedFreeVars(
                lhs,
                IFunctionApplication.<UnknownRing>create(compoundSym, rhs),
                null,
                IDPPredefinedMap.DEFAULT_MAP,
                this.itpfFactory,
                true));
        } else {
            return Collections.singleton(IRuleFactory.createWithExQuantifiedFreeVars(
                lhs,
                rhs,
                null,
                IDPPredefinedMap.DEFAULT_MAP,
                this.itpfFactory,
                true));
        }
    }

    /**
     * @param edge the method skip edge to convert.
     * @param encodeMethodReturns if true, method calls will be properly encoded, i.e., we have rules of the form
     * <ul>
     * <li>f(x,y) -eval-> f_1(f_0(x),y)</li>
     * <li>f_0(x) -callAbstract-> g(x)</li>
     * <li>f_1(g_end(z),y) -MethodSkip-> h(z,y)</li>
     * </ul>
     * If false, we will not try to use the information from the method return and generate rules
     * <ul>
     * <li>f(x,y) -eval-> f_1(x,y)</li>
     * <li>f(x,y) -eval-> f_0(x)</li>
     * <li>f_0(x) -callAbstract-> g(x)</li>
     * <li>f_1(x, y) -MethodSkip-> h(z,y)</li>
     * </ul>
     * @return a rule corresponding to <code>edge</code> (according to RTA'10, RTA'11 papers).
     */
    @SuppressWarnings("unchecked")
    private Collection<IRule> convertMethodSkipEdge(
        final Edge edge,
        final boolean forComplexity,
        final boolean encodeMethodReturns)
    {
        final Node startNode = edge.getStart();
        final String startID = startNode.getNodeNumber() + "";
        final State startState = startNode.getState();
        final Node endNode = edge.getEnd();
        final String endID = endNode.getNodeNumber() + "";
        final State endState = endNode.getState();

        final MethodSkipEdge mSkipEdge = (MethodSkipEdge) edge.getLabel();
        final Node returnNode = mSkipEdge.getNode();

        /*
         * Sometimes, the corresponding return state was already deleted. Then,
         * we don't need to check this edge.
         */
        if (returnNode == null) {
            return null;
        }

        final State returnState = returnNode.getState();

        final Map<AbstractVariableReference, AbstractVariableReference> startToEndMap =
            mSkipEdge.getCallingToResultUnchangedMap();

        final Map<AbstractVariableReference, AbstractVariableReference> returnToEndMap =
            mSkipEdge.getReturningToResultMap();

        /*
         * Here, we need to encode that we "skipped" a method m (by doing the
         * analysis of m on its own) and just need to apply the results. The
         * outer frames, i.e., everything but the innermost frame, is like in
         * startState. The innermost frame was rewritten to be like
         * returnedState. However, to get the rhs, we renamed some variables.
         * Furthermore, for the lhs, we possibly had some refinements which need
         * to be applied.
         */
        final IFunctionApplication<UnknownRing> rhs;
        final IPosition posOfInnermostFrame;
        rhs = this.getFlatTermForState(endState, endID);

        if (encodeMethodReturns && !forComplexity) {
            IFunctionApplication<UnknownRing> outerLhs =
                this.getFlatTermForState(
                    startState,
                    endState,
                    startToEndMap,
                    startID,
                    null,
                    Collections.<AbstractVariableReference>emptySet(),
                    startState.getCallStack().size() - 1,
                    1,
                    1);
            final IFunctionApplication<UnknownRing> innerLhs =
                this.getFlatTermForState(
                    returnState,
                    endState,
                    returnToEndMap,
                    returnNode.getNodeNumber() + "",
                    null,
                    Collections.<AbstractVariableReference>emptySet(),
                    0,
                    0,
                    0);

            //The old, outer counters have to burn, burn, burn!
            final MarkerFieldAnalysis markerAnalysis =
                (MarkerFieldAnalysis) this.sccAnnotations.getAnalysis(MarkerFieldAnalysis.class);
            if (markerAnalysis != null) {
                for (final AbstractVariableReference ref : markerAnalysis.getMarkerVarNames().values()) {
                    outerLhs =
                        outerLhs.applySubstitution(ISubstitution.create(this.dispatcher.getVariable(
                            ref,
                            Collections.<AbstractVariableReference>emptySet(),
                            startState), this.dispatcher.getVariableLengthChanged(ref, startState)));
                }
            }

            posOfInnermostFrame = IPosition.create(new int[] {0 });

            return Collections.singleton(IRuleFactory.createWithExQuantifiedFreeVars(
                (IFunctionApplication<UnknownRing>) outerLhs.replaceAt(posOfInnermostFrame, innerLhs),
                rhs,
                null,
                IDPPredefinedMap.DEFAULT_MAP,
                this.itpfFactory,
                true));
        } else {
            final IFunctionApplication<UnknownRing> lhs =
                this.getFlatTermForState(
                    startState,
                    endState,
                    startToEndMap,
                    startID,
                    null,
                    Collections.<AbstractVariableReference>emptySet(),
                    endState.getCallStack().size() - 1,
                    0,
                    1);

            if (forComplexity) {
                final IFunctionSymbol<UnknownRing> compoundSym =
                    IFunctionSymbol.createChecked(CpxIntTermHelper.ComPrefix + "1", 1, IDPPredefinedMap.DEFAULT_MAP);
                return Collections.singleton(IRuleFactory.createWithExQuantifiedFreeVars(
                    lhs,
                    IFunctionApplication.<UnknownRing>create(compoundSym, rhs),
                    null,
                    IDPPredefinedMap.DEFAULT_MAP,
                    this.itpfFactory,
                    true));
            } else {
                return Collections.singleton(IRuleFactory.createWithExQuantifiedFreeVars(
                    lhs,
                    rhs,
                    null,
                    IDPPredefinedMap.DEFAULT_MAP,
                    this.itpfFactory,
                    true));
            }
        }
    }

    /**
     * Transforms an integer result such as i3 = i1 X i2 into a substitution [i3/X(i1,i2)]
     * @param intRes Some integer computation result i3 = i1 X i2
     * @param startState state in which i1 and i2 are already existing (usually the state in which the integer
     * computation was performed).
     * @return [i3/X(i1,i2)]
     */
    @SuppressWarnings("unchecked")
    private ISubstitution getSubstitutionFromIntegerComputation(
        final IntegerResultInformation intRes,
        final State startState)
    {

        // Get information from the integer result information, piece for piece:
        final AbstractVariableReference firstOpRef = intRes.getFirstNumber();
        final ITerm<BigInt> firstOpTerm;
        // This is a special case for the NEG operation:
        if (firstOpRef == null) {
            assert (intRes.getArithmeticOperationType().equals(ArithmeticOperationType.NEG)) : "Missing first operator, but arithmetic operator isn't unary";
            firstOpTerm = IntegerTransformer.getConstantIntegerTerm(0);
        } else {
            firstOpTerm = this.dispatcher.transformInt(startState, firstOpRef);
        }

        final ITerm<BigInt> secondOpTerm;
        if (intRes.secondIsConstant()) {
            secondOpTerm =
                IntegerTransformer.getConstantIntegerTerm(((LiteralInt) intRes.getSecondConstant()).getLiteral());
        } else {
            secondOpTerm = this.dispatcher.transformInt(startState, intRes.getSecondNumber());
        }

        IFunctionSymbol<BigInt> operator = null;
        switch (intRes.getArithmeticOperationType()) {
        case ADD:
            operator =
                (IFunctionSymbol<BigInt>) IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbol(
                    PredefinedFunction.Func.Add,
                    DomainFactory.INTEGER_INTEGER);
            break;
        case MUL:
            operator =
                (IFunctionSymbol<BigInt>) IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbol(
                    PredefinedFunction.Func.Mul,
                    DomainFactory.INTEGER_INTEGER);
            break;
        case TIDIV:
            operator =
                (IFunctionSymbol<BigInt>) IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbol(
                    PredefinedFunction.Func.Div,
                    DomainFactory.INTEGER_INTEGER);
            break;
        case NEG:
            // -x = 0 - x
        case SUB:
            operator =
                (IFunctionSymbol<BigInt>) IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbol(
                    PredefinedFunction.Func.Sub,
                    DomainFactory.INTEGER_INTEGER);
            break;
        case TMOD:
            operator =
                (IFunctionSymbol<BigInt>) IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbol(
                    PredefinedFunction.Func.Mod,
                    DomainFactory.INTEGER_INTEGER);
            break;
        case AND:
        case XOR:
        case OR:
        case SHL:
        case SHR:
        case UREM:
        case USHR:
            //We can't handle these, so don't connect result to inputs:
            return ISubstitution.emptySubstitution();
        default:
            assert (false) : "Term representation for unknown arithmetic operation requested: "
                + intRes.getArithmeticOperationType();
            break;
        }
        final ITerm<BigInt> resultTerm = ITerm.createFunctionApplication(operator, firstOpTerm, secondOpTerm);

        if (intRes.getArithmeticOperationType() != ArithmeticOperationType.TIDIV) {
            final IVariable<BigInt> resultVar =
                this.dispatcher.getVariable(
                    intRes.getResult(),
                    Collections.<AbstractVariableReference>emptySet(),
                    startState);
            return ISubstitution.create(resultVar, resultTerm);
        } else {
            return ISubstitution.emptySubstitution();
        }
    }

    /**
     * Notes a relation to zero (or one) for some integer computations. For example, in i3 = i2 - i1, it is important to
     * know that i1 is not zero (to ensure some sort of strict monotonicity). Analogously, for multiplications and
     * divisions, we need to know the operands' relations to 1.
     * @param intRes Some integer computation result i3 = i1 X i2
     * @param startState state in which i1 and i2 are already existing (usually the state in which the integer
     * computation was performed).
     * @param endState state in which the result lives
     * @return <code>existingConstraint</code>, possibly extended by new constraints (using a conjunction).
     */
    private ITerm<BooleanRing> getConstraintFromIntegerComputation(
        final IntegerResultInformation intRes,
        final State startState,
        final State endState)
    {

        final ArithmeticOperationType op = intRes.getArithmeticOperationType();
        if (op == ArithmeticOperationType.ADD || (op == ArithmeticOperationType.SUB && !intRes.secondIsConstant())) {
            ITerm<BooleanRing> res = null;
            final AbstractVariableReference firstNumRef = intRes.getFirstNumber();
            if (this.shouldEncodeRef(firstNumRef, startState)) {
                final AbstractNumber firstNum = (AbstractNumber) startState.getAbstractVariable(firstNumRef);
                // We only want to encode integer information if this is != 0:
                if (firstNum instanceof AbstractInt && !intRes.secondIsConstant()) {
                    res = RuleCreator.getRelationTermRelativeToInteger(firstNumRef, 0, this.dispatcher, startState);
                }
            }

            if (!intRes.secondIsConstant()) {
                final AbstractVariableReference secondNumRef = intRes.getSecondNumber();
                if (this.shouldEncodeRef(secondNumRef, startState)) {
                    final AbstractNumber secondNum = (AbstractNumber) startState.getAbstractVariable(secondNumRef);
                    if (secondNum instanceof AbstractInt) {
                        res =
                            RuleCreator.getConjunction(res, RuleCreator.getRelationTermRelativeToInteger(
                                secondNumRef,
                                0,
                                this.dispatcher,
                                startState));
                    }
                }
            }
            return res;
        }

        if (op == ArithmeticOperationType.MUL || op == ArithmeticOperationType.TIDIV) {
            ITerm<BooleanRing> res = null;

            if (op == ArithmeticOperationType.TIDIV) {
                final AbstractVariableReference firstOpRef = intRes.getFirstNumber();
                final ITerm<BigInt> firstOpTerm = this.dispatcher.transformInt(startState, firstOpRef);
                final ITerm<BigInt> secondOpTerm;
                if (intRes.secondIsConstant()) {
                    secondOpTerm =
                        IntegerTransformer.getConstantIntegerTerm(((LiteralInt) intRes.getSecondConstant())
                            .getLiteral());
                } else {
                    secondOpTerm = this.dispatcher.transformInt(startState, intRes.getSecondNumber());
                }
                final AbstractVariableReference resRef = intRes.getResult();
                final ITerm<BigInt> resRefVar = this.dispatcher.transformInt(endState, resRef);

                final IFunctionSymbol<BigInt> div =
                    (IFunctionSymbol<BigInt>) IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbol(
                        PredefinedFunction.Func.Div,
                        DomainFactory.INTEGER_INTEGER);
                final IFunctionSymbol<BooleanRing> eq =
                    IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbolChecked(
                        PredefinedFunction.Func.Eq,
                        DomainFactory.INTEGER_INTEGER);

                res =
                    ITerm.createFunctionApplication(
                        eq,
                        resRefVar,
                        ITerm.createFunctionApplication(div, firstOpTerm, secondOpTerm));
            }

            final AbstractVariableReference firstNumRef = intRes.getFirstNumber();
            final AbstractInt firstNum = (AbstractInt) startState.getAbstractVariable(firstNumRef);
            if (this.shouldEncodeRef(firstNumRef, startState)) {
                if (firstNum instanceof AbstractInt) {
                    res =
                        RuleCreator.getConjunction(
                            res,
                            RuleCreator.getRelationTermRelativeToInteger(firstNumRef, 1, this.dispatcher, startState));
                }
            }

            if (!intRes.secondIsConstant()) {
                final AbstractVariableReference secondNumRef = intRes.getSecondNumber();
                if (this.shouldEncodeRef(secondNumRef, startState)) {
                    res =
                        RuleCreator.getConjunction(
                            res,
                            RuleCreator.getRelationTermRelativeToInteger(secondNumRef, 1, this.dispatcher, startState));
                }
            }

            if (op == ArithmeticOperationType.TIDIV && !intRes.secondIsConstant()) {
                final AbstractVariableReference secondNumRef = intRes.getSecondNumber();
                final AbstractInt secondNum = (AbstractInt) startState.getAbstractVariable(secondNumRef);
                final AbstractVariableReference resRef = intRes.getResult();
                if (this.shouldEncodeRef(resRef, endState)) {
                    final IFunctionSymbol<BooleanRing> lt =
                        IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbolChecked(
                            PredefinedFunction.Func.Lt,
                            DomainFactory.INTEGER_INTEGER);
                    final IFunctionSymbol<BooleanRing> le =
                        IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbolChecked(
                            PredefinedFunction.Func.Le,
                            DomainFactory.INTEGER_INTEGER);
                    final ITerm<BigInt> dividedRefVar = this.dispatcher.transformInt(startState, firstNumRef);
                    final ITerm<BigInt> resRefVar = this.dispatcher.transformInt(endState, resRef);

                    // r = x / y, where x > 0 and y > 1 => r < x
                    if (firstNum.isPositive() && secondNum.isPositive() && !secondNum.containsLiteral(1)) {
                        res = RuleCreator.getConjunction(res, ITerm.createFunctionApplication(lt, resRefVar, dividedRefVar));

                        // r = x / y, where x >= 0 and y > 1 => r <= x
                    } else if (firstNum.isNonNegative() && secondNum.isPositive() && !secondNum.containsLiteral(1)) {
                        res =
                            RuleCreator.getConjunction(
                                res,
                                ITerm.createFunctionApplication(le, resRefVar, dividedRefVar));

                        // r = x / y, where x < 0 and y > 1 => x < r
                    } else if (firstNum.isNegative() && secondNum.isPositive() && !secondNum.containsLiteral(1)) {
                        res = RuleCreator.getConjunction(res, ITerm.createFunctionApplication(lt, dividedRefVar, resRefVar));

                        // r = x / y, where x <= 0 and y > 1 => x <= r
                    } else if (firstNum.isNegative() && secondNum.isPositive() && !secondNum.containsLiteral(1)) {
                        res =
                            RuleCreator.getConjunction(
                                res,
                                ITerm.createFunctionApplication(le, dividedRefVar, resRefVar));
                    }
                }
            }
            return res;
        }

        return null;
    }

    /**
     * Turns a state into a flat term representation, where all variables and local references are put as arguments for
     * one function symbol. The first argument is still eos.
     * @param state Some state in our graph
     * @param label A label that is prepended to every function symbol created to represent stack frames. Should be
     * unique to a graph node.
     * @param startFrameIndex index of stackframe (from the top) at which the encoding should be started.
     * @return a function application encoding <code>state</code>
     */
    private IFunctionApplication<UnknownRing> getFlatTermForState(
        final State state,
        final String label,
        final int startFrameIndex)
    {
        return this.getFlatTermForState(
            state,
            null,
            null,
            label,
            null,
            Collections.<AbstractVariableReference>emptySet(),
            startFrameIndex,
            0,
            0);
    }

    /**
     * Turns a state into a flat term representation, where all variables and local references are put as arguments for
     * one function symbol. The first argument is still eos.
     * @param state Some state in our graph
     * @param label A label that is prepended to every function symbol created to represent stack frames. Should be
     * unique to a graph node.
     * @return a function application encoding <code>state</code>
     */
    private IFunctionApplication<UnknownRing> getFlatTermForState(final State state, final String label) {
        return this.getFlatTermForState(
            state,
            null,
            null,
            label,
            null,
            Collections.<AbstractVariableReference>emptySet(),
            state.getCallStack().size() - 1,
            0,
            0);
    }

    /**
     * Turns a state into a flat term representation, where all variables and local references are put as arguments for
     * one function symbol. The first argument is still eos.
     * @param state Some state in our graph
     * @param stateWithInformation Some other state from which information about some references should be retrieved
     * @param refMap Partial map of references from <code>state</code> to <code>stateWithInformation</code>. For refs
     * that are mapped, the corresponding value from <code>stateWithInformation</code> is encoded. For all others, the
     * value from <code>state</code> is taken.
     * @param label A label that is prepended to every function symbol created to represent stack frames. Should be
     * unique to a graph node.
     * @param startAtFrame index of stackframe (from the top) at which the encoding should be started. Stackframes below
     * are not considered for encoding.
     * @param excludesFramesAbove index of stackframe (from the top) at which the encoding should be stopped.
     * Stackframes on top of it are no longer considered for encoding.
     * @param changedConnectionInformation an encoding of the heap connection that was changed in this evaluation (or
     * null, if no such change exists).
     * @param possiblePredecessors References possibly reaching the changed reference. May be null.
     * @param id numeric ID that identifies the part of the state that is constructed.
     * @return a function application encoding <code>state</code>
     */
    private IFunctionApplication<UnknownRing> getFlatTermForState(
        final State state,
        final State stateWithInformation,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap,
        final String label,
        final ReferenceAccessInformation changedConnectionInformation,
        final Set<AbstractVariableReference> possiblePredecessors,
        final int startAtFrame,
        final int excludesFramesAbove,
        final int id)
    {
        return this.getFlatTermForState(
            state,
            stateWithInformation,
            refMap,
            label,
            changedConnectionInformation,
            possiblePredecessors,
            startAtFrame,
            excludesFramesAbove,
            id,
            null);
    }

    /**
     * Turns a state into a flat term representation, where all variables and local references are put as arguments for
     * one function symbol. The first argument is still eos.
     * @param state Some state in our graph
     * @param stateWithInformation Some other state from which information about some references should be retrieved
     * @param refMap Partial map of references from <code>state</code> to <code>stateWithInformation</code>. For refs
     * that are mapped, the corresponding value from <code>stateWithInformation</code> is encoded. For all others, the
     * value from <code>state</code> is taken.
     * @param label A label that is prepended to every function symbol created to represent stack frames. Should be
     * unique to a graph node.
     * @param startAtFrame index of stackframe (from the top) at which the encoding should be started. Stackframes below
     * are not considered for encoding.
     * @param excludesFramesAbove index of stackframe (from the top) at which the encoding should be stopped.
     * Stackframes on top of it are no longer considered for encoding.
     * @param changedConnectionInformation an encoding of the heap connection that was changed in this evaluation (or
     * null, if no such change exists).
     * @param possiblePredecessors References possibly reaching the changed reference. May be null.
     * @param id numeric ID that identifies the part of the state that is constructed.
     * @param followingEdgeLabel the edge following this node in the current encoding. Can be null.
     * @return a function application encoding <code>state</code>
     */
    @SuppressWarnings({"unchecked", "rawtypes" })
    private IFunctionApplication<UnknownRing> getFlatTermForState(
        final State state,
        final State stateWithInformation,
        final Map<AbstractVariableReference, AbstractVariableReference> refMap,
        final String label,
        final ReferenceAccessInformation changedConnectionInformation,
        final Set<AbstractVariableReference> possiblePredecessors,
        final int startAtFrame,
        final int excludesFramesAbove,
        final int id,
        final EdgeInformation followingEdgeLabel)
    {
        final CallStack callstack = state.getCallStack();

        final List<AbstractVariableReference> candRootReferences = new LinkedList<>();

        final MarkerFieldAnalysis markerAnalysis =
            (MarkerFieldAnalysis) this.sccAnnotations.getAnalysis(MarkerFieldAnalysis.class);

        // For the outermost frame, we encode the input references and marker field counters:
        for (int sfIndex = startAtFrame; sfIndex >= excludesFramesAbove; sfIndex--) {
            // Get all references in this stackframe:
            final StackFrame frame = callstack.get(sfIndex);
            assert (frame != null) : "Couldn't get " + sfIndex + "-th frame of:\n" + state;

            candRootReferences.addAll(frame.getInputReferences().getReferences());

            // Now get exception ref, local vars and operand stack:
            if (frame.hasException()) {
                candRootReferences.add(frame.getException());
            }
            for (final Integer varPos : frame.getActiveVariables()) {
                final AbstractVariableReference var = frame.getLocalVariable(varPos.intValue());
                if (var != null && !var.pointsToFloat()) {
                    candRootReferences.add(var);
                }
            }
            candRootReferences.addAll(frame.getOperandStack().getStack());
        }

        final LinkedList<ITerm<?>> rootTerms = new LinkedList<>();
        for (final AbstractVariableReference ref : candRootReferences) {
            if (this.shouldEncodeRef(ref, state)) {
                rootTerms.addAll(this.dispatcher.<SemiRing>transform(
                    state,
                    stateWithInformation,
                    refMap,
                    ref,
                    possiblePredecessors,
                    changedConnectionInformation));
            }
        }

        if (markerAnalysis != null && (startAtFrame == callstack.size() - 1)) {
            for (final AbstractVariableReference ref : markerAnalysis.getMarkerVarNames().values()) {
                rootTerms.add(this.dispatcher.<BigInt>getVariable(
                    ref,
                    Collections.<AbstractVariableReference>emptySet(),
                    state));
            }
        }

        if (this.arguments.encodeStaticFields) {
            // In END_OF_STACK, we may want to keep the encoding of static
            // variables
            final ArrayList<ITerm<?>> staticVarTerms = new ArrayList<>();
            final UsedFieldsAnalysis usedFieldAnalysis = this.dispatcher.getUsedFieldAnalysis();

            for (final Entry<ClassName, Map<String, AbstractVariableReference>> e : state
                .getStaticFields()
                .getEntries())
            {
                final ClassName cName = e.getKey();

                Collection<String> usedFields;
                if (usedFieldAnalysis != null) {
                    usedFields = usedFieldAnalysis.getUsedStaticFieldNames(cName);
                } else {
                    usedFields = e.getValue().keySet();
                }

                for (final Entry<String, AbstractVariableReference> f : e.getValue().entrySet()) {
                    final String fieldName = f.getKey();
                    final AbstractVariableReference ref = f.getValue();
                    if (usedFields.contains(fieldName) && this.shouldEncodeRef(ref, state)) {
                        staticVarTerms.addAll(this.dispatcher.<SemiRing>transform(
                            state,
                            stateWithInformation,
                            refMap,
                            ref,
                            possiblePredecessors,
                            changedConnectionInformation));
                    }
                }
            }

            final IFunctionSymbol<UnknownRing> staticVarSym =
                IFunctionSymbol.<UnknownRing>createChecked(
                    RuleCreator.STATIC_VARS_SYMBOL_NAME + "_" + label,
                    staticVarTerms.size(),
                    IDPPredefinedMap.DEFAULT_MAP);
            final IFunctionApplication<UnknownRing> staticVarApp =
                IFunctionApplication.create(staticVarSym, ImmutableCreator.create(staticVarTerms));

            rootTerms.addFirst(IFunctionApplication.create(
                IFunctionSymbol.<UnknownRing>createChecked(RuleCreator.END_OF_STACK_NAME, 1, IDPPredefinedMap.DEFAULT_MAP),
                ImmutableCreator.create(new ArrayList<ITerm<?>>(Collections.singleton(staticVarApp)))));
        } else {
            rootTerms.addFirst(IFunctionApplication.create(
                IFunctionSymbol.<UnknownRing>createChecked(RuleCreator.END_OF_STACK_NAME, 0, IDPPredefinedMap.DEFAULT_MAP),
                ImmutableCreator.create(new ArrayList<ITerm<?>>(0))));
        }

        if (this.arguments.encodeReferenceDistances) {
            final DefiniteReachabilities reaches = state.getHeapAnnotations().getDefiniteReachabilities();
            for (final DefiniteReachabilityAnnotation dra : reaches) {
                if (followingEdgeLabel instanceof EQRefinementEdge) {
                    final EQRefinementEdge eqRef = (EQRefinementEdge) followingEdgeLabel;
                    final AbstractVariableReference refA = eqRef.getReplacedRef();
                    final AbstractVariableReference refB = eqRef.getReplacementRef();

                    //The two variables were identified, so the counter is broken.
                    if ((dra.getFrom().equals(refA) && dra.getTo().equals(refB))
                        || (dra.getFrom().equals(refB) && dra.getTo().equals(refA))) {
                        rootTerms.addLast(TransformationDispatcher.createDefiniteReachabilityVariable(dra, null, false));
                        continue;
                    }
                }
                rootTerms.addLast(TransformationDispatcher.createDefiniteReachabilityVariable(dra, refMap, false));
            }
        }

        final StackFrame topmostEncodedFrame = callstack.get(excludesFramesAbove);

        // Now create the actual stackframe symbol:
        final int arity = rootTerms.size();
        // Create symbols in the form NODEID_STACKFRAMEID_OPCODE
        final IFunctionSymbol<UnknownRing> funcSym =
            IFunctionSymbol.<UnknownRing>createChecked(
                RuleCreator.getNameOfStateFunctionSymbol(label, id, topmostEncodedFrame.getCurrentOpCode()),
                arity,
                IDPPredefinedMap.DEFAULT_MAP);

        return ITerm.createFunctionApplication(funcSym, ImmutableCreator.create(new ArrayList<>(rootTerms)));
    }

    /**
     * @param label A label that is prepended to every function symbol created to represent stack frames. Should be
     * unique to a graph node.
     * @param id numeric ID that identifies the part of the state that is constructed.
     * @param opCode the opcode of the state
     * @return a unique name for the function symbol used to encode this state
     */
    public static String getNameOfStateFunctionSymbol(final String label, final int id, final OpCode opCode) {
        return "f"
            + label
            + "_"
            + id
            + "_"
            + opCode.getMethod().getName().replace('<', '_').replace('>', '_')
            + "_"
            + opCode.getShortName();
    }

    /**
     * Transforms an integer relation such as i1 > i2 to a term such as >(i1,i2).
     * @param ir Some relation between integers such as i1 > i2
     * @param dispatcher transformation dispatcher used to encode the used variables.
     * @param startState state in which i1 and i2 are already existing (usually the state in which the integer relation
     * was asserted).
     * @return the term for the integer relation (may be null).
     */
    private static IFunctionApplication<BooleanRing> getRelationTermFromIntegerRelation(
        final JBCIntegerRelation ir,
        final TransformationDispatcher dispatcher,
        final State startState)
    {
        final IntegerRelationType irType = ir.getRelationType();

        final ITerm<BigInt> leftTerm = dispatcher.transformInt(startState, ir.getLeftIntRef());

        final ITerm<BigInt> rightTerm;
        if (ir.rightIntegerIsNoRef()) {
            rightTerm = IntegerTransformer.getConstantIntegerTerm(((LiteralInt) ir.getRightInt()).getLiteral());
        } else {
            rightTerm = dispatcher.transformInt(startState, ir.getRightIntRef());
        }

        // Get the right (predefined) function symbol to represent the relation:
        final IFunctionSymbol<BooleanRing> op;
        boolean invert = false;
        switch (irType) {
        case LT:
            op =
                IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbolChecked(
                    PredefinedFunction.Func.Lt,
                    DomainFactory.INTEGER_INTEGER);
            break;
        case LE:
            op =
                IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbolChecked(
                    PredefinedFunction.Func.Le,
                    DomainFactory.INTEGER_INTEGER);
            break;
        case GT:
            op =
                IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbolChecked(
                    PredefinedFunction.Func.Gt,
                    DomainFactory.INTEGER_INTEGER);
            break;
        case GE:
            op =
                IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbolChecked(
                    PredefinedFunction.Func.Ge,
                    DomainFactory.INTEGER_INTEGER);
            break;
        case EQ:
            op =
                IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbolChecked(
                    PredefinedFunction.Func.Eq,
                    DomainFactory.INTEGER_INTEGER);
            break;
        case NE:
            // symNeq exists, but is not implemented in the ITRS framework:
            op =
                IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbolChecked(
                    PredefinedFunction.Func.Eq,
                    DomainFactory.INTEGER_INTEGER);
            invert = true;
            break;
        default:
            assert (false);
            op = null;
            break;
        }
        IFunctionApplication<BooleanRing> cond = ITerm.createFunctionApplication(op, leftTerm, rightTerm);

        // Avoid statements such as x = x:
        if (leftTerm.equals(rightTerm) && irType == IntegerRelationType.EQ) {
            cond = null;
            // To get !=, we have to do !(x = y). Add the negation symbol:
        } else if (invert) {
            final ArrayList<ITerm<BooleanRing>> args = new ArrayList<>();
            args.add(cond);
            cond =
                ITerm.createFunctionApplication(IDPPredefinedMap.DEFAULT_MAP.<BooleanRing>getFunctionSymbolChecked(
                    PredefinedFunction.Func.Lnot,
                    DomainFactory.BOOLEAN), ImmutableCreator.create(args));
        }

        return cond;
    }

    /**
     * Given a reference to an integer variable and an integer value, returns a term expressing the relation to this
     * value or null. Null is returned in the case when no relation is known (such as when the variable is (-inf, inf))
     * or when the relation is trivial (i.e. <code>ref</code> points to a literal integer value).
     * @param ref some variable reference to an integer variable
     * @param valueOfInterest some integer value to which the variable referenced by <code>ref</code> should be
     * compared.
     * @param dispatcher transformation dispatcher used to encode the used variables.
     * @param startState state in which i1 and i2 are already existing (usually the state in which the integer relation
     * was asserted).
     * @return the term for the integer relation (may be null).
     */
    private static IFunctionApplication<BooleanRing> getRelationTermRelativeToInteger(
        final AbstractVariableReference ref,
        final int valueOfInterest,
        final TransformationDispatcher dispatcher,
        final State startState)
    {

        final AbstractInt i = (AbstractInt) startState.getAbstractVariable(ref);
        if (i.isLiteral()) {
            return null;
        }
        IFunctionSymbol<BooleanRing> op = null;
        boolean invert = false;
        if (i instanceof IntervalInt) {
            final IntervalInt ii = (IntervalInt) i;
            final BigInteger valOfInterest = BigInteger.valueOf(valueOfInterest);

            // Compare upper and lower bounds:
            final int relOfLowerToValOfInterest = ii.getLower().compareTo(valOfInterest);
            final int relOfUpperToValOfInterest = ii.getUpper().compareTo(valOfInterest);

            /*
             * We have [l, u] and val and found out that l > val holds. Then [l,
             * u] > val holds. Rest is similar.
             */
            if (relOfLowerToValOfInterest == 1) {
                op =
                    IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbolChecked(
                        PredefinedFunction.Func.Gt,
                        DomainFactory.INTEGER_INTEGER);
            } else if (relOfLowerToValOfInterest == 0) {
                op =
                    IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbolChecked(
                        PredefinedFunction.Func.Ge,
                        DomainFactory.INTEGER_INTEGER);
            } else if (relOfUpperToValOfInterest == 0) {
                op =
                    IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbolChecked(
                        PredefinedFunction.Func.Le,
                        DomainFactory.INTEGER_INTEGER);
            } else if (relOfUpperToValOfInterest == -1) {
                op =
                    IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbolChecked(
                        PredefinedFunction.Func.Lt,
                        DomainFactory.INTEGER_INTEGER);
            }

            // We have some special tricks to handle the 0:
            if (op == null && valueOfInterest == 0) {
                if (!ii.containsLiteral(valOfInterest)) {
                    op =
                        IDPPredefinedMap.DEFAULT_MAP.getFunctionSymbolChecked(
                            PredefinedFunction.Func.Eq,
                            DomainFactory.INTEGER_INTEGER);
                    invert = true;
                }
            }
        }

        // If we have an operand, create a term:
        if (op != null) {
            IFunctionApplication<BooleanRing> result =
                ITerm.createFunctionApplication(
                    op,
                    dispatcher.transformInt(startState, ref),
                    IntegerTransformer.getConstantIntegerTerm(valueOfInterest));
            if (invert) {
                final ArrayList<ITerm<BooleanRing>> args = new ArrayList<>();
                args.add(result);
                result =
                    ITerm.createFunctionApplication(IDPPredefinedMap.DEFAULT_MAP.<BooleanRing>getFunctionSymbolChecked(
                        PredefinedFunction.Func.Lnot,
                        DomainFactory.BOOLEAN), ImmutableCreator.create(args));
            }
            return result;
        } else {
            return null;
        }

    }

    /**
     * Given two terms of which one is possibly null, return either the non-null term or the conjunction of both terms.
     * @param l some term (or null)
     * @param r some term (or null, if <code>l</code> is not null)
     * @return some non-null value, either l, r or the conjunction of both.
     */
    public static ITerm<BooleanRing> getConjunction(final ITerm<BooleanRing> l, final ITerm<BooleanRing> r) {
        if (l == null) {
            return r;
        } else if (r == null) {
            return l;
        }
        return ITerm.createFunctionApplication(IDPPredefinedMap.DEFAULT_MAP.<BooleanRing>getFunctionSymbolChecked(
            PredefinedFunction.Func.Land,
            DomainFactory.BOOLEAN_BOOLEAN), l, r);
    }
}
