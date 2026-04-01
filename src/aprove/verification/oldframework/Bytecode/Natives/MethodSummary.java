package aprove.verification.oldframework.Bytecode.Natives;

import static java.util.Collections.*;
import static java.util.stream.Collectors.*;

import java.math.BigInteger;
import java.util.*;
import java.util.function.BiConsumer;
import java.util.function.Function;
import java.util.logging.*;
import java.util.stream.*;

import org.json.*;

import aprove.input.Programs.jbc.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation.*;
import aprove.verification.oldframework.Bytecode.Graphs.Reachability.*;
import aprove.verification.oldframework.Bytecode.Merger.StatePosition.*;
import aprove.verification.oldframework.Bytecode.OpCode.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.Annotations.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.InputReferenceChangeInformation.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.Bytecode.Utils.MethodSummary.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class MethodSummary extends PredefinedMethod {

    public static final Logger logger = Logger.getLogger(MethodSummary.class.getName());

    static class SideEffectApplication {
        private AbstractType jlo;
        private State res;
        private Map<AbstractVariableReference, Pair<Optional<SimplePolynomial>, Optional<SimplePolynomial>>> abstractedInstances = new LinkedHashMap<>();

        public SideEffectApplication(State res) {
            this.res = res;
            jlo = new AbstractType(res.getClassPath(), FuzzyClassType.FT_JAVA_LANG_OBJECT.toAbstract());
        }

        public void noteInstanceToAbstract(AbstractVariableReference ref, Optional<SimplePolynomial> lb, Optional<SimplePolynomial> ub) {
            abstractedInstances.put(ref, new Pair<>(lb, ub));
        }

        public void abstractInstances() {
            HeapPositions heapPos = new HeapPositions(res);
            Set<AbstractVariableReference> pointingToConcreteInstances =
                    abstractedInstances.keySet().stream().filter(x -> res.getAbstractVariable(x) instanceof ConcreteInstance).collect(toSet());
            pointingToConcreteInstances.remove(AbstractVariableReference.NULLREF);
            Set<AbstractVariableReference> pointingToAbstractInstances =
                    abstractedInstances.keySet().stream().filter(x -> res.getAbstractVariable(x) instanceof AbstractInstance).collect(toSet());
            pointingToAbstractInstances.remove(AbstractVariableReference.NULLREF);
            Set<AbstractVariableReference> refsToAbstract = new LinkedHashSet<>();
            refsToAbstract.addAll(pointingToAbstractInstances);
            refsToAbstract.addAll(pointingToConcreteInstances);
            State newRes = res.replaceConcreteInstancesByAbstractedInstance(pointingToConcreteInstances, true);
            if (newRes == null) {
                newRes = res.clone();
            }
            for (AbstractVariableReference r: pointingToAbstractInstances) {
                AbstractVariable var = newRes.getAbstractVariable(r);
                newRes.replaceReference(r, newRes.createReferenceAndAdd(var, OperandType.ADDRESS));
            }
            res = newRes;
            res.gc();
            HeapPositions newHeapPos = new HeapPositions(res);
            HeapAnnotations ha = res.getHeapAnnotations();
            for (AbstractVariableReference r: refsToAbstract) {
                Optional<StatePosition> pi = heapPos.getPositionsForRef(r).stream().filter(newHeapPos::hasPosition).findAny();
                pi.map(newHeapPos::getReferenceForPos).ifPresent(x -> {
                    ha.setReachableTypes(x, jlo); //update reachable types
                    res.getCallStack().getStackFrameList().forEach(sf ->
                                                                           sf.getInputReferences().addChanges(newHeapPos, x, IRChangeInformations.unknownChange())
                    );//update IR
                });
            }
        }

        public Set<AbstractVariableReference> getAbstractedInstances() {
            return abstractedInstances.keySet();
        }

        public Optional<SimplePolynomial> getLowerBound(AbstractVariableReference r) {
            return abstractedInstances.get(r).x;
        }

        public Optional<SimplePolynomial> getUpperBound(AbstractVariableReference r) {
            return abstractedInstances.get(r).y;
        }

    }

    private final boolean isStatic;
    private final ComplexitySummary complexity;
    private final Set<ComplexitySummary> refinedComplexities;
    private final MethodIdentifier mid;
    private boolean isDefaultSummary;

    public MethodSummary(boolean isStatic,
                         ComplexitySummary complexity,
                         MethodIdentifier mid) {
        this(isStatic, complexity, new LinkedHashSet<>(), mid);
    }

    public MethodSummary(boolean isStatic,
                         ComplexitySummary complexity,
                         Set<ComplexitySummary> refinedComplexities,
                         MethodIdentifier mid) {
        this.isStatic = isStatic;
        this.complexity = complexity;
        this.refinedComplexities = refinedComplexities;
        this.mid = mid;
        validate();
    }

    private void validate() {
        Set<String> vars = new LinkedHashSet<>();
        int argCount = mid.getDescriptor().getArgumentCount();
        for (int i = 0; i < argCount; i++) {
            vars.add("arg" + i);
        }
        if (!isStatic) {
            vars.add("this");
        }
        vars.add("env");
        assert complexity.validate(vars);
        assert refinedComplexities.stream().allMatch(refinedComplexity -> refinedComplexity.validate(vars));

        assert complexity.predicate == null;
        assert refinedComplexities.stream().allMatch(refinedComplexity -> refinedComplexity.predicate != null);
    }

    @Override
    public Optional<List<String>> getArgs() {
        List<String> args = new ArrayList<>();
        if (!isStatic) {
            args.add("this");
        }
        for (int i = 0; i < mid.getDescriptor().getArgumentCount(); i++) {
            args.add("arg" + i);
        }
        return Optional.of(args);
    }

    private int getArgCount() {
        int res = mid.getDescriptor().getArgumentCount();
        if (!isStatic) {
            res++;
        }
        return res;
    }

    public MethodIdentifier getMethodIdentifier() {
        return mid;
    }

    /**
     * @param s Input state
     * @param result Object used for collecting the result
     * @return true iff a refinement was done
     */
    @Override
    public boolean refine(State s, Collection<Pair<State, ? extends EdgeInformation>> result) {
        if (s.getSplitResult() != null && s.getSplitResult() instanceof SummarySplitResult) {
            return refineExceptions(s, (SummarySplitResult) s.getSplitResult(), result);
        }

        Set<ComplexitySummary> defaultSummaries = calculatePredicateSummary(s, isStatic, complexity, refinedComplexities);

        boolean refined = false;
        for (ComplexitySummary e : refinedComplexities) {
            if (e.predicate.type == PredicateType.NULL || e.predicate.type == PredicateType.NOT_NULL) {
                refined |= refineNullRelation(s, e, defaultSummaries, isStatic, result);
            } else if(e.predicate.type.isIntegerRelation()) {
                refined |= refineIntegerRelation(s, e, defaultSummaries, isStatic, result);
            } else if (!e.predicate.type.needsNoRefinement()) {
                throw new NotYetImplementedException();
            }
        }
        if (!refined) {
            for (ComplexitySummary e : defaultSummaries) {
                State refinedS = s.clone();
                refinedS.setSplitResult(new SummarySplitResult(e));
                RefinementEdge refinementEdge = new RefinementEdge("", new LinkedHashMap<>());
                result.add(new Pair<>(refinedS, refinementEdge));
            }
        }

        return true;
    }

    private static boolean refineIntegerRelation(State s, ComplexitySummary summary, Set<ComplexitySummary> defaultSummaries, boolean isStatic, Collection<Pair<State, ? extends EdgeInformation>> result) {
        AbstractInt x = getIntFromName(s, summary.predicate.var0, isStatic);
        AbstractInt y = getIntFromName(s, summary.predicate.var1, isStatic);
        if (x.isLiteral() && y.isLiteral()) {
            // Case 1: x and y are literals
            if (AbstractInt.computeComparisonResult(summary.predicate.type.getIntegerRelationType(), x, y, false, false)) {
                State newState = s.clone();
                newState.setSplitResult(new SummarySplitResult(summary));
                String label = x.toString() + " " + summary.predicate.type.synonym + " " + y.toString();
                result.add(new Pair<>(newState, new RefinementEdge(label, new LinkedHashMap<>())));
                return true;
            }
            return false;
        } else if (x.isLiteral() || y.isLiteral()) {
            // Case 2: either x or y is an interval (but not both)
            AbstractVariableReference varRef = getArgumentFromName(s, x.isLiteral() ? summary.predicate.var1 : summary.predicate.var0, isStatic);
            Collection<Pair<AbstractInt, AbstractInt>> resultVariables =
                    IntegerRefinement.forIntegerRelation(x, y, summary.predicate.type.getIntegerRelationType());
            if (resultVariables != null && resultVariables.size() > 0) {
                for (Pair<AbstractInt, AbstractInt> vars : resultVariables) {
                    AbstractInt varOfInterest = x.isLiteral() ? vars.y : vars.x;
                    State newState = s.clone();

                    AbstractVariableReference newRef = newState.createReferenceAndAdd(varOfInterest, varRef.getPrimitiveType());
                    newState.replaceReference(varRef, newRef);

                    String label = varRef.toString() + ": " + varOfInterest.toString();

                    if (AbstractInt.computeComparisonResult(
                            summary.predicate.type.getIntegerRelationType(),
                            x.isLiteral() ? x : vars.x,
                            y.isLiteral() ? y : vars.y,
                            false,
                            false
                    )) {
                        newState.setSplitResult(new SummarySplitResult(summary));
                        RefinementEdge edge = new RefinementEdge(label, new LinkedHashMap<>());
                        result.add(new Pair<>(newState, edge));
                    } else {
                        for (ComplexitySummary e : defaultSummaries) {
                            State clonedState = newState.clone();
                            clonedState.setSplitResult(new SummarySplitResult(e));
                            RefinementEdge edge = new RefinementEdge(label, new LinkedHashMap<>());
                            result.add(new Pair<>(clonedState, edge));
                        }
                    }
                }
                return true;
            }
            return false;
        } else {
            // Case 3: x and y are intervals
            AbstractVariableReference xRef = getArgumentFromName(s, summary.predicate.var0, isStatic);
            AbstractVariableReference yRef = getArgumentFromName(s, summary.predicate.var1, isStatic);

            State sTrue = s.clone();
            State sFalse = s.clone();

            sTrue.note(xRef, summary.predicate.type.getIntegerRelationType(), yRef);
            sFalse.note(xRef, summary.predicate.type.getIntegerRelationType().invert(), yRef);

            sTrue.setSplitResult(new SummarySplitResult(summary));

            String labelTrue = xRef.toString() + " " + summary.predicate.type.getIntegerRelationType() + " " + yRef.toString();
            String labelFalse = xRef.toString() + " " + summary.predicate.type.getIntegerRelationType().invert() + " " + yRef.toString();

            if (AbstractInt.isDecidableComparison(summary.predicate.type.getIntegerRelationType(), x, y, x == y, false)) {
                if (AbstractInt.computeComparisonResult(summary.predicate.type.getIntegerRelationType(), x, y, x == y, false)) {
                    result.add(new Pair<>(sTrue, new RefinementEdge(labelTrue, new LinkedHashMap<>())));
                    return true;
                } else if (AbstractInt.computeComparisonResult(summary.predicate.type.getIntegerRelationType().invert(), x, y, x == y, false)) {
                    for (ComplexitySummary e : defaultSummaries) {
                        State clonedState = sFalse.clone();
                        clonedState.setSplitResult(new SummarySplitResult(e));
                        result.add(new Pair<>(clonedState, new RefinementEdge(labelFalse, new LinkedHashMap<>())));
                    }
                    return true;
                } else {
                    return false;
                }
            } else {
                result.add(new Pair<>(sTrue, new RefinementEdge(labelTrue, new LinkedHashMap<>())));
                for (ComplexitySummary e : defaultSummaries) {
                    State clonedState = sFalse.clone();
                    clonedState.setSplitResult(new SummarySplitResult(e));
                    result.add(new Pair<>(clonedState, new RefinementEdge(labelFalse, new LinkedHashMap<>())));
                }
                return true;
            }
        }
    }

    private static boolean refineNullRelation(State s, ComplexitySummary summary, Set<ComplexitySummary> defaultSummaries, boolean isStatic, Collection<Pair<State, ? extends EdgeInformation>> result) {
        AbstractVariableReference var = getArgumentFromName(s, summary.predicate.var0, isStatic);
        LinkedList<Pair<State, ? extends EdgeInformation>> states = new LinkedList<>();
        ObjectRefinement.forExistence(var, s, states);
        if (states.size() >= 2) {
            int entryIndex = summary.predicate.type == PredicateType.NULL ? 1 : 0;
            RefinementEdge defaultEdge = (RefinementEdge) states.get(1 - entryIndex).getValue();
            defaultEdge.setLabel("default:\n" + defaultEdge.getLabel());

            State stateTrue = states.get(entryIndex).getKey();
            EdgeInformation edgeTrue = states.get(entryIndex).getValue();
            stateTrue.setSplitResult(new SummarySplitResult(summary));
            result.add(new Pair<>(stateTrue, edgeTrue));

            State stateFalse = states.get(1 - entryIndex).getKey();
            EdgeInformation edgeFalse = states.get(1 - entryIndex).getValue();

            for (ComplexitySummary e : defaultSummaries) {
                State stateDefault = stateFalse.clone();
                stateDefault.setSplitResult(new SummarySplitResult(e));
                EdgeInformation edgeDefault = (EdgeInformation) edgeFalse.clone();
                result.add(new Pair<>(stateDefault, edgeDefault));
            }
            return true;
        }
        return false;
    }

    private static Set<ComplexitySummary> calculatePredicateSummary(State s,
                                                               boolean isStatic,
                                                               ComplexitySummary defaultSummary,
                                                               Set<ComplexitySummary> refinedComplexities) {
        Set<ComplexitySummary> heapAnnotationsCases = refinedComplexities.stream()
                                                                         .filter((e) -> e.predicate.type.needsNoRefinement())
                                                                         .collect(Collectors.toSet());
        Set<ComplexitySummary> res = new HashSet<>();
        for (ComplexitySummary e : heapAnnotationsCases) {
            if (isPredicateFulfilled(e.predicate, s, isStatic)) {
                res.add(e);
            }
        }
        if (res.isEmpty()) {
            res.add(defaultSummary);
        }
        return res;
    }

    private static boolean isPredicateFulfilled(Predicate predicate, State s, boolean isStatic) {
        AbstractVariableReference var0 = getArgumentFromName(s, predicate.var0, isStatic);
        AbstractVariableReference var1 = safeGetArgumentFromName(s, predicate.var1, isStatic);
        HeapAnnotations heapAnnotations = s.getHeapAnnotations();
        switch (predicate.type) {
            case SHARE:
                assert var1 != null;
                return heapAnnotations.getJoiningStructures().areJoining(var0, var1);
            case EQUALS:
                assert var1 != null;
                return heapAnnotations.getEqualityGraph().areMarkedAsPossiblyEqual(var0, var1);
            case CYCLIC:
                return heapAnnotations.getCyclicStructures().isCyclic(var0);
            case NON_TREE:
                return heapAnnotations.isPossiblyNonTree(var0);
            case DEFINITE_REACHABILITY:
                return heapAnnotations.getDefiniteReachabilities().areConnected(var0, var1);
            case REACHABLE_TYPES:
                ClassName className = ClassName.fromDotted(predicate.var1);
                boolean classAbstract = s.getClassPath().getClass(className).getType().isAbstract();
                FuzzyType type = new FuzzyClassType(className, !classAbstract);
                return heapAnnotations.getReachableTypes(var0).contains(type, s.getClassPath(), s.getJBCOptions());
            case INSTANCEOF:
                className = ClassName.fromDotted(predicate.var1);
                assert s.getAbstractVariable(var0) instanceof ConcreteInstance;
                ConcreteInstance var0Concrete = (ConcreteInstance) s.getAbstractVariable(var0);
                return var0Concrete.getMostSpecializedInstance().getType().isSubClassOf(className);
            default:
                throw new IllegalArgumentException(String.format(
                        "PredicateType '%s' is not yet implemented in refinement",
                        predicate.type));
        }
    }

    private static boolean refineExceptions(State s, SummarySplitResult splitResult, Collection<Pair<State, ? extends EdgeInformation>> result) {
        if (!splitResult.needsExceptionRefinement()) {
            return false;
        } if (!splitResult.summary.throwsSet.isEmpty()) {
            Set<String> maybeThrows = splitResult.summary.throwsSet;
            for (String exception : maybeThrows) {
                State exceptionState = s.clone();
                exceptionState.setSplitResult(splitResult.shallowCopy().replaceException(exception));
                result.add(new Pair<>(exceptionState, new RefinementEdge(exception + " thrown", new LinkedHashMap<>())));
            }
            if (!splitResult.summary.alwaysThrows) {
                State newState = s.clone();
                newState.setSplitResult(splitResult.shallowCopy().replaceException(null));
                result.add(new Pair<>(newState, new RefinementEdge("No exception thrown", new LinkedHashMap<>())));
            }
            return true;
        }
        return false;
    }

    private static AbstractVariableReference getArgumentFromName(State s, String name, boolean staticMethod) {
        AbstractVariableReference res = safeGetArgumentFromName(s, name, staticMethod);
        if (res == null) {
            throw new IllegalArgumentException("\"" + name + "\" is not allowed here");
        }
        return res;
    }

    private static AbstractVariableReference safeGetArgumentFromName(State s, String name, boolean staticMethod) {
        if ("this".equals(name) && !staticMethod) {
            return s.getCurrentStackFrame().getOperandStack().getStack().get(0);
        }
        if (name != null && name.startsWith("arg")) {
            int varIndex = Integer.parseInt(name.substring("arg".length())) + (staticMethod ? 0 : 1);
            return s.getCurrentStackFrame().getOperandStack().getStack().get(varIndex);
        }
        return null;
    }

    private static AbstractInt getIntFromName(State s, String name, boolean staticMethod) {
        if (name.startsWith("arg")) {
            AbstractVariable var = s.getAbstractVariable(getArgumentFromName(s, name, staticMethod));
            if (var instanceof AbstractInt) {
                return (AbstractInt) var;
            } else {
                throw new IllegalArgumentException("name is not an int");
            }
        } else {
            try {
                return LiteralInt.createLiteralInt(new BigInteger(name));
            } catch (NumberFormatException e) {
                throw new IllegalArgumentException("name is not a literal int (BigInteger)");
            }
        }
    }

    @Override
    public Pair<State, ? extends EdgeInformation> evaluate(State s) {
        State newState = s.clone();
        ClassPath cp = newState.getClassPath();
        assert s.getSplitResult() != null && s.getSplitResult() instanceof SummarySplitResult;
        SummarySplitResult splitResult = (SummarySplitResult) s.getSplitResult();
        ComplexitySummary refinedComplexity = splitResult.summary;

        PredefinedMethodEdge e = new PredefinedMethodEdge(
                instantiate(refinedComplexity.lowerTime, getArgs().get(), s),
                instantiate(refinedComplexity.upperTime, getArgs().get(), s),
                instantiate(refinedComplexity.lowerSpace, getArgs().get(), s),
                instantiate(refinedComplexity.upperSpace, getArgs().get(), s),
                isStatic,
                mid.getDescriptor().getReturnType() == null,
                getArgCount());

        Predicate predicate = splitResult.summary.predicate;
        if (predicate != null && predicate.type.needsNoRefinement()) {
            e.setAdditionalLabel(predicate.var0 + " " + predicate.type.synonym + (predicate.var1 == null ? "" : " " + predicate.var1));
        }

        SideEffectApplication sfa = applySideEffects(newState, refinedComplexity);
        State abstractedState = sfa.res;

        Map<AbstractVariableReference, AbstractVariableReference> refRenaming;
        if (abstractedState == null) {
            refRenaming = emptyMap();
        } else {
            refRenaming = computeRefRenaming(newState, abstractedState);
            newState = abstractedState;
        }

        addSizeBounds(s, e, sfa, refRenaming);

        e.setRefRenaming(refRenaming);

        AbstractVariableReference res = null;
        if (splitResult.getException() == null) {
            res = createReturnedValue();
        }

        removeHeapAnnotations(newState, refinedComplexity);
        addHeapAnnotations(newState, refinedComplexity, res);

        for (int i = 0; i < getArgCount(); i++) {
            newState.getCurrentStackFrame().popOperandStack();
        }

        if (splitResult.getException() == null && res != null) {
            addReturnedValue(s, newState, res, cp, e, refinedComplexity);
        }

        newState.gc();

        newState.setCurrentOpCode(newState.getCurrentOpCode().getNextOp());

        if (splitResult.getException() != null) {
            addException(newState, cp, splitResult.getException());
        }

        if (refinedComplexity.modifies.contains("env")) {
            Optional<SimplePolynomial> lb = refinedComplexity.sizeBounds.getLowerBound("env").map(x -> instantiate(x, getArgs().get(), s));
            Optional<SimplePolynomial> ub = refinedComplexity.sizeBounds.getUpperBound("env").map(x -> instantiate(x, getArgs().get(), s));
            e.add(new EnvrionmentChangeInformation(lb, ub));
        }

        return new Pair<>(splitResult.summary.terminates ? newState : s.clone(), e);
    }

    private void removeHeapAnnotations(State s, ComplexitySummary summary) {
        applyToDistinctPairs(summary.removed.joiningStructures,
                             (x, y) -> {
                                 JoiningStructures joins = s.getHeapAnnotations().getJoiningStructures();
                                 if (joins.areJoining(x, y)) {
                                     joins.remove(x, y);
                                     if (joins.hasCommonSuccessor(x, y)) {
                                         joins.add(x, y);
                                     }
                                 }
                             },
                             (x) -> getArgumentFromName(s, x, isStatic));

        applyToDistinctPairs(summary.removed.mayBeEqual,
                             (x, y) -> {
                                 EqualityGraph equal = s.getHeapAnnotations().getEqualityGraph();
                                 if (equal.areMarkedAsPossiblyEqual(x, y)) {
                                     equal.remove(x, y);
                                     if (equal.hasCommonSuccessor(x, y)) {
                                         equal.add(x, y);
                                     }
                                 }
                             },
                             (x) -> getArgumentFromName(s, x, isStatic));

        summary.removed.definiteReachabilities.forEach((e) -> {
            AbstractVariableReference from = getArgumentFromName(s, e.x, isStatic);
            AbstractVariableReference to = getArgumentFromName(s, e.z, isStatic);
            DefiniteReachabilities definiteReachabilities = s.getHeapAnnotations().getDefiniteReachabilities();
            definiteReachabilities.getAnnotations(from, to).forEach(definiteReachabilities::remove);
        });

        summary.removed.nonTree.forEach((x) -> {
            AbstractVariableReference ref = getArgumentFromName(s, x, isStatic);
            s.getHeapAnnotations().getPossiblyNonTreeRefs().remove(ref);
        });

        summary.removed.cyclic.forEach((e) -> {
            AbstractVariableReference ref = getArgumentFromName(s, e.x, isStatic);
            s.getHeapAnnotations().getCyclicStructures().remove(ref);
        });

        /*
        TODO: incomplete removal of reachable types. Please handle with care.
        The removal of reachable types can be quite complex, because we cannot remove too much information here.
        If we want to remove class A from reachable types, we need to remove A and all types B that somehow
        extend A.
        We also need to remove all classes C that A extends from (especially jlO).
        After checking this, we could have removed too much types, so we need to move up the type tree from A to C
        and add all types directly following C that A does not extend from.
        This can be very complex and require a lot of memory, so that it is not included here.
        Disclaimer: The following implementation is not complete! Please use with care.
        It needs to be completed and probably tested. The issues described above apply.
         */
//        summary.removed.reachableTypes.forEach((e) -> {
//            ClassPath cp = s.getClassPath();
//            AbstractVariableReference ref = getArgumentFromName(s, e.x, isStatic);
//            Set<FuzzyType> removableTypes = e.y.stream().map(y -> {
//                ClassName className = ClassName.fromDotted(y);
//                boolean classAbstract = s.getClassPath().getClass(className).getType().isAbstract();
//                return new FuzzyClassType(className, !classAbstract);
//            }).collect(toSet());
//            Set<FuzzyType> newReachableTypes = s.getHeapAnnotations().getReachableTypes(ref).getPossibleClassesCopy();
//            for (FuzzyType remove : removableTypes) {
//                Set<FuzzyType> add = new HashSet<>();
//                newReachableTypes = newReachableTypes.stream().filter(x -> {
//                    if (remove instanceof FuzzyPrimitiveType) {
//                        return !remove.equals(x);
//                    } else if (remove instanceof FuzzyClassType) {
//                        if (x instanceof FuzzyClassType) {
//                            if (cp.getTypeTree(((FuzzyClassType) x)).containsSuperType(((FuzzyClassType) remove).getMinimalClass())) {
//                                return false;
//                            } else if (cp.getTypeTree((FuzzyClassType) remove).containsSuperType(((FuzzyClassType) x).getMinimalClass())) {
//                                //cp.getTypeTree((FuzzyClassType) x).expand(s.getJBCOptions()).stream().filter();
//                                return true;
//                            } else {
//                                return true;
//                            }
//                        } else {
//                            return true;
//                        }
//                    } else {
//                        throw new UnsupportedOperationException("FuzzyType instances changed unexpectedly");
//                    }
//                }).collect(toSet());
//                newReachableTypes.addAll(add);
//            }
//            s.getHeapAnnotations().setReachableTypes(ref, new AbstractType(cp, s.getJBCOptions(), newReachableTypes));
//        });
    }

    private static FuzzyType createFuzzyTypeFromDotted(State s, String name) {
        for (OperandType e : OperandType.values()) {
            if (e.isPrimitive() && e.getShortName().equalsIgnoreCase(name)) {
                return new FuzzyPrimitiveType(e.getPrimChar(), 0);
            }
        }
        ClassName className = ClassName.fromDotted(name);
        boolean classAbstract = s.getClassPath().getClass(className).getType().isAbstract();
        return new FuzzyClassType(className, !classAbstract);
    }

    private void addHeapAnnotations(State s, ComplexitySummary summary, AbstractVariableReference res) {
        applyToDistinctPairs(summary.resulting.joiningStructures,
                             (x, y) -> s.getHeapAnnotations().getJoiningStructures().add(x, y),
                             (x) -> "ret".equals(x) ? res : getArgumentFromName(s, x, isStatic));

        applyToDistinctPairs(summary.resulting.mayBeEqual,
                             (x, y) -> s.getHeapAnnotations().getEqualityGraph().add(x, y),
                             (x) -> "ret".equals(x) ? res : getArgumentFromName(s, x, isStatic));

        summary.resulting.definiteReachabilities.forEach((e) -> {
            AbstractVariableReference from = "ret".equals(e.x) ? res : getArgumentFromName(s, e.x, isStatic);
            AbstractVariableReference to = "ret".equals(e.z) ? res : getArgumentFromName(s, e.z, isStatic);
            s.getHeapAnnotations().getDefiniteReachabilities().add(new DefiniteReachabilityAnnotation(from, to, e.y, false, s.getClassPath()));
        });

        summary.resulting.nonTree.forEach((x) -> {
            AbstractVariableReference ref = "ret".equals(x) ? res : getArgumentFromName(s, x, isStatic);
            s.getHeapAnnotations().setPossiblyNonTree(ref);
        });

        summary.resulting.cyclic.forEach((e) -> {
            AbstractVariableReference ref = "ret".equals(e.x) ? res : getArgumentFromName(s, e.x, isStatic);
            s.getHeapAnnotations().setPossiblyCyclic(ref, e.y);
        });

        summary.resulting.reachableTypes.forEach((e) -> {
            AbstractVariableReference ref = "ret".equals(e.x) ? res : getArgumentFromName(s, e.x, isStatic);
            Collection<AbstractType>
                    types =
                    e.y.stream()
                       .map(x -> new AbstractType(s.getClassPath(), createFuzzyTypeFromDotted(s, x)))
                       .collect(toSet());
            s.getHeapAnnotations().addReachableTypes(ref, types, s.getClassPath(), s.getJBCOptions());
        });
    }

    private static <T, R> void applyToDistinctPairs(List<List<T>> list, BiConsumer<R, R> f, Function<T, R> preprocess) {
        for (List<T> eqClass : list) {
            for (int i = 0; i < eqClass.size(); i++) {
                for (int j = i + 1; j < eqClass.size(); j++) {
                    f.accept(preprocess.apply(eqClass.get(i)), preprocess.apply(eqClass.get(j)));
                }
            }
        }
    }

    private static void addException(State s, ClassPath cp, String exceptionName) {
        s.getCurrentStackFrame().getOperandStack().getStack().clear();

        FuzzyClassType exceptionType = new FuzzyClassType(ClassName.fromDotted(exceptionName), false).toAbstract();

        AbstractVariableReference exceptionRef = new AbstractVariableReference("x", OperandType.ADDRESS);
        exceptionRef = AbstractVariableReference.create(exceptionRef);
        s.setAbstractType(exceptionRef, new AbstractType(cp, exceptionType));

        HeapAnnotations annotations = s.getHeapAnnotations();
        AbstractType allTypes = new AbstractType(cp, FuzzyClassType.FT_JAVA_LANG_OBJECT.toAbstract());
        annotations.addReachableTypes(exceptionRef, allTypes, cp, s.getJBCOptions());
        annotations.setMaybeExisting(exceptionRef);

        s.getCurrentStackFrame().setException(exceptionRef);
    }

    private AbstractVariableReference createReturnedValue() {
        FuzzyType returnType = mid.getDescriptor().getReturnType();
        if (returnType != null) {
            if (returnType instanceof FuzzyClassType) {
                returnType = ((FuzzyClassType) returnType).toAbstract();
            }
            AbstractVariableReference res = new AbstractVariableReference("x", returnType.getPrimitiveType());
            // hack to get a nice name for the reference
            return AbstractVariableReference.create(res);
        }
        return null;
    }

    private void addReturnedValue(State s, State newState, AbstractVariableReference res, ClassPath cp, PredefinedMethodEdge e, ComplexitySummary summary) {
        FuzzyType returnType = mid.getDescriptor().getReturnType();
        newState.getCurrentStackFrame().pushOperandStack(res);
        if (res.pointsToReferenceType()) {
            HeapAnnotations annotations = newState.getHeapAnnotations();
            newState.setAbstractType(res, new AbstractType(cp, returnType));
            AbstractType allTypes = new AbstractType(cp, FuzzyClassType.FT_JAVA_LANG_OBJECT.toAbstract());
            annotations.addReachableTypes(res, allTypes, cp, s.getJBCOptions());
            annotations.setMaybeExisting(res);
        } else if (res.pointsToAnyIntegerType()) {
            newState.addAbstractVariable(res, AbstractInt.getUnknown(IntegerType.UNBOUND));
        } else if (res.pointsToAnyFloatType()) {
            newState.addAbstractVariable(res, AbstractFloat.create());
        } else {
            throw new RuntimeException();
        }
        addSizeBound(s, e, res, summary.sizeBounds.getLowerBound("ret"), summary.sizeBounds.getUpperBound("ret"));
    }

    private void addSizeBounds(State s, PredefinedMethodEdge e, SideEffectApplication sfa, Map<AbstractVariableReference, AbstractVariableReference> refRenaming) {
        for (AbstractVariableReference r: sfa.getAbstractedInstances()) {
            if (refRenaming.containsKey(r)) {
                addSizeBound(s, e, refRenaming.get(r), sfa.getLowerBound(r), sfa.getUpperBound(r));
                refRenaming.remove(r);
            }
        }
    }

    private Map<AbstractVariableReference, AbstractVariableReference> computeRefRenaming(State newState, State abstractedState) {
        Map<AbstractVariableReference, AbstractVariableReference> refRenaming = new LinkedHashMap<>();
        HeapPositions heapPos = new HeapPositions(newState, true);
        HeapPositions heapPosAbstracted = new HeapPositions(abstractedState, true);
        for (AbstractVariableReference r: abstractedState.getReferences().keySet()) {
            Collection<StatePosition> positions = heapPosAbstracted.getPositionsForRef(r);
            Set<AbstractVariableReference> oldRefs = new LinkedHashSet<>();
            for (StatePosition sPos: positions) {
                if (heapPos.hasPosition(sPos)) {
                    oldRefs.add(heapPos.getReferenceForPos(sPos));
                }
            }
            assert oldRefs.size() == 1;
            refRenaming.put(oldRefs.iterator().next(), r);
        }
        return refRenaming;
    }

    private SideEffectApplication applySideEffects(State s, ComplexitySummary complexitySummary) {
        SideEffectApplication res = new SideEffectApplication(s);
        List<AbstractVariableReference> origStack = s.getCurrentStackFrame().getOperandStack().getStack();
        List<AbstractVariableReference> stack = new ArrayList<>(origStack).subList(origStack.size() - getArgCount(), origStack.size());
        List<String> args = getArgs().get();
        for (String arg: args) {
            AbstractVariableReference r = stack.remove(0);
            if (complexitySummary.modifies.contains(arg)) {
                if (r.pointsToReferenceType()) {
                    res.noteInstanceToAbstract(r, complexitySummary.sizeBounds.getLowerBound(arg), complexitySummary.sizeBounds.getUpperBound(arg));
                } else {
                    System.err.println("Method summary for " + mid + " wants to apply side-effects to primitives... This does not make sense.");
                }
            }
        }
        res.abstractInstances();
        return res;
    }

    public static MethodSummary defaultSummary(IMethod pm, HandlingMode goal, String reason) {
        List<String> args = new LinkedList<>();
        if (!pm.isStatic()) {
            args.add("this");
        }
        for (int i = 0; i < pm.getDescriptor().getArgumentCount(); i++) {
            args.add("arg" + i);
        }
        SimplePolynomial ub = SimplePolynomial.create("env");
        for (String arg: args) {
            ub = ub.plus(SimplePolynomial.create(arg));
        }
        SimplePolynomial lb = ub.negate();
        Set<String> modifies = new LinkedHashSet<>();
        SizeBounds sizeBounds = new SizeBounds();
        if (pm.isInstanceInitializer()) {
            modifies.add("this");
            sizeBounds.addLowerBound("this", SimplePolynomial.ONE);
            sizeBounds.addUpperBound("this", ub);
        }
        FuzzyType returnType = pm.getDescriptor().getReturnType();
        if (returnType != null) {
            sizeBounds.addUpperBound("ret", ub);
            if (returnType instanceof FuzzyPrimitiveType) {
                sizeBounds.addLowerBound("ret", lb);
            } else {
                sizeBounds.addLowerBound("ret", SimplePolynomial.ZERO);
            }
        }
        ComplexitySummary complexity;
        switch (goal) {
            case UserDefined:
                complexity = new ComplexitySummary(SimplePolynomial.ZERO, SimplePolynomial.ZERO, SimplePolynomial.ZERO, SimplePolynomial.ZERO, sizeBounds, modifies);
                break;
            default:
                complexity = new ComplexitySummary(SimplePolynomial.ONE, SimplePolynomial.ONE, SimplePolynomial.ZERO, SimplePolynomial.ZERO, sizeBounds, modifies);
        }
        MethodSummary res = new MethodSummary(pm.isStatic(), complexity, pm.getMethodIdentifier());
        res.isDefaultSummary = true;

        logger.info("created summary: Created default summary for " + pm.getMethodIdentifier() + ", reason: " + reason);
        return res;
    }

    public boolean isDefaultSummary() {
        return isDefaultSummary;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((complexity == null) ? 0 : complexity.hashCode());
        result = prime * result + (isDefaultSummary ? 1231 : 1237);
        result = prime * result + (isStatic ? 1231 : 1237);
        result = prime * result + ((mid == null) ? 0 : mid.hashCode());
        result = prime * result + ((complexity.modifies == null) ? 0 : complexity.modifies.hashCode());
        result = prime * result + ((complexity.sizeBounds == null) ? 0 : complexity.sizeBounds.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        MethodSummary other = (MethodSummary) obj;
        if (complexity == null) {
            if (other.complexity != null)
                return false;
        } else if (!complexity.equals(other.complexity))
            return false;
        if (isStatic != other.isStatic)
            return false;
        if (mid == null) {
            if (other.mid != null)
                return false;
        } else if (!mid.equals(other.mid))
            return false;
        if (complexity.modifies == null) {
            if (other.complexity.modifies != null)
                return false;
        } else if (!complexity.modifies.equals(other.complexity.modifies))
            return false;
        if (complexity.sizeBounds == null) {
            if (other.complexity.sizeBounds != null)
                return false;
        } else if (!complexity.sizeBounds.equals(other.complexity.sizeBounds))
            return false;
        return true;
    }

    public boolean equals(MethodSummary other, PolyComperator comperator) {
        if (this == other)
            return true;
        if (other == null)
            return false;
        if (complexity == null) {
            if (other.complexity != null)
                return false;
        } else if (!complexity.equals(other.complexity, comperator))
            return false;
        if (isStatic != other.isStatic)
            return false;
        if (mid == null) {
            if (other.mid != null)
                return false;
        } else if (!mid.equals(other.mid))
            return false;
        if (complexity.modifies == null) {
            if (other.complexity.modifies != null)
                return false;
        } else if (!complexity.modifies.equals(other.complexity.modifies))
            return false;
        if (complexity.sizeBounds == null) {
            if (other.complexity.sizeBounds != null)
                return false;
        } else if (!complexity.sizeBounds.equals(other.complexity.sizeBounds, comperator))
            return false;
        return true;
    }

    @Override
    public String toString() {
        return JSONUtil.storeAsJSON(Collections.singleton(this)).toString(4);
    }

    public String toString(Collection<String> comments) {
        String out = JSONUtil.storeAsJSON(Stream.of(new Pair<>(this, comments))).toString(4);
        return out;
    }

    /**
     * @param comments a collection of comments, all objects must be supported by the JSONArray constructor {@link JSONArray#JSONArray(Collection)}
     * @return
     */
    public JSONObject toJSON(Collection<String> comments) {
        JSONObject res = complexity.toJSON()
                                   .put(JSONKeys.Name.toString(), mid.getMethodName())
                                   .put(JSONKeys.Descriptor.toString(), mid.getDescriptor().toString())
                                   .put(JSONKeys.Static.toString(), isStatic);
        if (!comments.isEmpty()) {
            res.put(JSONKeys.Comments.toString(), new JSONArray(comments.toArray()));
        }
        if (!refinedComplexities.isEmpty()) {
            res.put(JSONKeys.Cases.toString(),
                    new JSONArray(refinedComplexities.stream().map(ComplexitySummary::toJSON).toArray(JSONObject[]::new)));
        }
        return res;
    }
}
