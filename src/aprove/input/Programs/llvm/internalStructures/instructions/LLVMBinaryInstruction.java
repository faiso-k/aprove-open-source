package aprove.input.Programs.llvm.internalStructures.instructions;

import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author Janine Repke, cryingshadow, Jera Hensel
 */
public class LLVMBinaryInstruction extends LLVMAssignmentInstruction {

    /**
     * @param state The current state.
     * @param var1 The term corresponding to the first operand.
     * @param var2 The term corresponding to the second operand.
     * @param newVar The symbolic variable assigned to the result program variable.
     * @param nodeNumber The current node number.
     * @return An abstract LLVM state where the result variable is set to a trap value if either of the operands has
     *         been a trap value before.
     * @throws UndefinedBehaviorException If both operands are different trap values.
     *                                    TODO This might be lifted to different trap values with the same condition.
     */
    private static LLVMAbstractState checkTrap(
        LLVMAbstractState state,
        LLVMSimpleTerm var1,
        LLVMSimpleTerm var2,
        LLVMSymbolicVariable newVar,
        int nodeNumber
    ) throws UndefinedBehaviorException {
        if (state.isPossiblyTrapValue(var1)) {
            if (state.isPossiblyTrapValue(var2)) {
                if (!var1.equals(var2)) {
                    throw new TrapValueException(
                        "Accessing two different trap values at node " + nodeNumber + "."
                    );
                }
            }
            return state.putTrapValue(newVar, state.getTrapValues().get(var1));
        } else if (state.isPossiblyTrapValue(var2)) {
            return state.putTrapValue(newVar, state.getTrapValues().get(var2));
        }
        return state;
    }

    /**
     * Enable poison values in special cases (only for udiv, sdiv, lshr, ashr).
     */
    private final boolean exact;

    /**
     * Enable poison values if a signed overflow occurs (not needed for fmul, fsub and others).
     */
    private final boolean nsw;

    /**
     * Enable poison values if an unsigned overflow occurs (not needed for fmul, fsub and others).
     */
    private final boolean nuw;

    /**
     * The value of the first operand.
     */
    private final LLVMLiteral operand1Value;

    /**
     * The value of the second operand.
     */
    private final LLVMLiteral operand2Value;

    /**
     * The type of the operator.
     */
    private final LLVMBinaryOpType operator;

    /**
     * @param id The variable to be assigned.
     * @param val1 The first operand.
     * @param val2 The second operand.
     * @param operationType The type of the operation.
     * @param setExact Special case poison values enabled?
     * @param setNsw Signed overflow poison values enabled?
     * @param setNuw Unsigned overflow poison values enabled?
     * @param debugLine The index of the line with debug information.
     */
    public LLVMBinaryInstruction(
        LLVMVariableLiteral id,
        LLVMLiteral val1,
        LLVMLiteral val2,
        LLVMBinaryOpType operationType,
        boolean setExact,
        boolean setNsw,
        boolean setNuw,
        int debugLine
    ) {
        super(id, debugLine);
        if (Globals.useAssertions) {
            assert (val1.getType().equals(val2.getType())) : "Both operands must have the same type!";
            //assert (val1.getType().isIntOrVecOfIntType()) : "Operands must be integers or vectors of integers!";
        }
        this.operand1Value = val1;
        this.operand2Value = val2;
        this.operator = operationType;
        this.exact = setExact;
        this.nsw = setNsw;
        this.nuw = setNuw;
    }

    @Override
    public void collectVariables(Collection<String> vars) {
        LLVMInstruction.collectVariable(vars, this.operand1Value);
        LLVMInstruction.collectVariable(vars, this.operand2Value);
    }
    
    public void collectUsedVariables(Collection<String> vars) {
    	collectVariables(vars);
    }

    @Override
    public LLVMLiteralRelation computeRelation() {
        switch (this.operator) {
        case ADD:
            return
                LLVMLiteralRelation.createAdditionRelation(
                    this.getIdentifier(),
                    this.operand1Value,
                    this.operand2Value
                );
        case MUL:
            return
                LLVMLiteralRelation.createMultiplicationRelation(
                    this.getIdentifier(),
                    this.operand1Value,
                    this.operand2Value
                );
        case SUB:
            return
                LLVMLiteralRelation.createSubtractionRelation(
                    this.getIdentifier(),
                    this.operand1Value,
                    this.operand2Value
                );
        case SHL:
            //       res = op1 << op2
            //  <=>  res = op1 * 2^op2
            if (this.operand2Value instanceof LLVMIntLiteral) {
                int op2Value = this.operand2Value.toInt();
                if (op2Value > 0 && op2Value <= 30) {
                    long newOp2Value = 1 << op2Value;
                    LLVMIntLiteral newOp2 = new LLVMRegularIntLiteral(this.operand2Value.getType(), newOp2Value, true);
                    // We ignore the case where op1 is negative (and turns positive by a shift), since we do not know
                    // anything about op1 at this position.
                    return
                        LLVMLiteralRelation.createMultiplicationRelation(
                            this.getIdentifier(),
                            this.operand1Value,
                            newOp2
                        );
                }
            }
            case LSHR:
                //       res = op1 >> op2
                //  <=>  res = op1 / 2^op2
                //  <=>  op1 = res * 2^op2
                if (this.operand2Value instanceof LLVMIntLiteral) {
                    int op2Value = this.operand2Value.toInt();
                    if (op2Value > 0 && op2Value <= 30) {
                        long divisorValue = 1 << op2Value;
                        LLVMIntLiteral divisor = new LLVMRegularIntLiteral(this.operand2Value.getType(), divisorValue, true);
                        // We ignore the case where op1 is negative (and turns positive by a shift), since we do not know
                        // anything about op1 at this position.
                        return
                            LLVMLiteralRelation.createMultiplicationRelation(
                                this.operand1Value,
                                this.getIdentifier(),
                                divisor
                            );
                    }
                }
        default:
            return null;
        }
    }

    @Override
    public Set<Pair<IntegerRelationSet, List<String>>> computeReturnConditions(
        LLVMProgramPosition pos,
        Set<Pair<IntegerRelationSet, List<String>>> conditions,
        LLVMParameters params
    ) {
        final LLVMRelationFactory relationFactory = params.SMTsolver.stateFactory.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        Set<Pair<IntegerRelationSet, List<String>>> res = new LinkedHashSet<Pair<IntegerRelationSet, List<String>>>();
        String name = this.getIdentifier().getName();
        LLVMHeuristicProgVarRef id = new LLVMHeuristicProgVarRef(name, name);
        final LLVMTerm left;
        if (this.operand1Value instanceof LLVMVariableLiteral) {
            String op1Name = ((LLVMVariableLiteral)this.operand1Value).getName();
            left = new LLVMHeuristicProgVarRef(op1Name, op1Name);
        } else if (this.operand1Value instanceof LLVMBigIntLiteral) {
            left = termFactory.constant(((LLVMBigIntLiteral)this.operand1Value).getValueAsBigInteger());
        } else if (this.operand1Value instanceof LLVMRegularIntLiteral) {
            left = termFactory.constant(((LLVMRegularIntLiteral)this.operand1Value).getValueAsBigInteger());
        } else {
            return res;
        }
        final LLVMTerm right;
        if (this.operand2Value instanceof LLVMVariableLiteral) {
            String op2Name = ((LLVMVariableLiteral)this.operand2Value).getName();
            right = new LLVMHeuristicProgVarRef(op2Name, op2Name);
        } else if (this.operand2Value instanceof LLVMBigIntLiteral) {
            right = termFactory.constant(((LLVMBigIntLiteral)this.operand2Value).getValueAsBigInteger());
        } else if (this.operand2Value instanceof LLVMRegularIntLiteral) {
            right = termFactory.constant(((LLVMRegularIntLiteral)this.operand2Value).getValueAsBigInteger());
        } else {
            return res;
        }
        final LLVMTerm replacement;
        switch (this.operator) {
            case ADD:
                replacement = termFactory.operation(ArithmeticOperationType.ADD, left, right);
                break;
            case SUB:
                replacement = termFactory.operation(ArithmeticOperationType.SUB, left, right);
                break;
            case MUL:
                replacement = termFactory.operation(ArithmeticOperationType.MUL, left, right);
                break;
            case SDIV:
                replacement = termFactory.operation(ArithmeticOperationType.TIDIV, left, right);
                break;
            case SREM:
                replacement = termFactory.operation(ArithmeticOperationType.TMOD, left, right);
                break;
            case UREM:
                replacement = termFactory.operation(ArithmeticOperationType.UREM, left, right);
                break;
            case AND:
                replacement = termFactory.operation(ArithmeticOperationType.AND, left, right);
                break;
            case OR:
                replacement = termFactory.operation(ArithmeticOperationType.OR, left, right);
                break;
            case XOR:
                replacement = termFactory.operation(ArithmeticOperationType.XOR, left, right);
                break;
            case SHL:
                replacement = termFactory.operation(ArithmeticOperationType.SHL, left, right);
                break;
            case ASHR:
                replacement = termFactory.operation(ArithmeticOperationType.SHR, left, right);
                break;
            case LSHR:
                if (params.useBoundedIntegers) {
                    replacement = termFactory.operation(ArithmeticOperationType.USHR, left, right);
                } else {
                    replacement = termFactory.operation(ArithmeticOperationType.SHR, left, right);
                }
                break;
            default:
                // TODO add other cases
                // not yet implemented
                throw new RuntimeException("Operator " + this.operator + " is not yet implemented!");
        }
        for (Pair<IntegerRelationSet, List<String>> pair : conditions) {
            IntegerRelationSet relSet = new IntegerRelationSet();
            for (IntegerRelation rel : pair.x) {
                relSet.add(rel.applySubstitution(id, replacement));
            }
            res.add(new Pair<IntegerRelationSet, List<String>>(relSet, pair.y));
        }
        return res;
    }

    @Override
    public Set<LLVMSymbolicEvaluationResult> evaluate(LLVMAbstractState state, int nodeNumber, boolean proveMemorySafety, LLVMMemoryChangeTracker memoryTracker, Abortion aborter)
    throws UndefinedBehaviorException {
        // TODO implement refinement for bounded case
        final LLVMParameters params = state.getStrategyParamters();
        final boolean useBoundedIntegers = params.useBoundedIntegers;
        final LLVMType operandType = this.operand1Value.getType();
        final LLVMSimpleTerm var1 = state.getSimpleTermForLiteral(this.operand1Value);
        final LLVMSimpleTerm var2 = state.getSimpleTermForLiteral(this.operand2Value);
        final LLVMRelationFactory relationFactory = state.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        final String varName = this.getIdentifier().getName();
        // TODO check trap values for shifts as soon as they are implemented
        final Pair<LLVMTerm, LLVMAbstractState> operationPair = this.operator.toLLVMTerm(state, var1, var2, nodeNumber, aborter);
        LLVMAbstractState res = operationPair.y;
        final LLVMTerm operation = operationPair.x;
        if (!useBoundedIntegers) {
            final Set<LLVMRelation> newRels = new LinkedHashSet<>();
            res = res.assign(varName, operation, operandType, newRels, aborter).incrementPC();
            final LLVMSymbolicVariable newVar = res.getSymbolicVariableForProgramVariable(varName);
            if (this.operator.equals(LLVMBinaryOpType.SREM)) {
                if (res.checkIfNonNegative(var2, aborter).x) {
                    LLVMRelation lessThan = relationFactory.lessThan(newVar, var2);
                    newRels.add(lessThan);
                    res = res.addRelation(lessThan, aborter);
                }
            }
            return
                Collections.singleton(
                    new LLVMSymbolicEvaluationResult(
                        LLVMBinaryInstruction.checkTrap(res, var1, var2, newVar, nodeNumber),
                        newRels
                    )
                );
        } else if (state instanceof LLVMHeuristicState) {
            // check if no overflow occurs at all -> use normal relation
            // check if a simple over-/underflow occurs -> refine
            boolean unsigned = false;
            if (state.getStrategyParamters().useBoundedIntegers) {
                unsigned = state.getModule().getUnsignedBitvectorVariables().contains(this.getIdentifier().getName());
            }
            final IntegerType intTypeOfResult = this.computeResultType(unsigned, useBoundedIntegers);
            final IntervalBound upperBound = intTypeOfResult.getUpper();
            final IntervalBound lowerBound = intTypeOfResult.getLower();
            final LLVMConstant upperLimit = upperBound.isFinite() ? termFactory.constant(upperBound.getConstant()) : null;
            final LLVMConstant lowerLimit = lowerBound.isFinite() ? termFactory.constant(lowerBound.getConstant()) : null;
            final LLVMTerm size = termFactory.add(termFactory.sub(upperLimit, lowerLimit), termFactory.constant(1));
            Pair<YNM,YNM> overflowPair = this.operator.checkBoundsForOverflow(state, intTypeOfResult, var1, var2);
            Pair<YNM,YNM> underflowPair = this.operator.checkBoundsForUnderflow(state, intTypeOfResult, var1, var2);
            // TODO check trap values for operations based on exact, nuw, and nsw
            if (upperLimit == null || overflowPair.x.equals(YNM.NO)
                || res.checkRelation(relationFactory.lessThanEquals(operation, upperLimit), aborter).x) {
                // no overflow
                if (lowerLimit == null || underflowPair.x.equals(YNM.NO)
                    || res.checkRelation(relationFactory.lessThanEquals(lowerLimit, operation), aborter).x) {
                    // no underflow
                    final Set<LLVMRelation> newRels = new LinkedHashSet<>();
                    res = res.assign(varName, operation, operandType, newRels, aborter).incrementPC();
                    final LLVMSymbolicVariable newVar = res.getSymbolicVariableForProgramVariable(varName);
                    return
                        Collections.singleton(
                            new LLVMSymbolicEvaluationResult(
                                LLVMBinaryInstruction.checkTrap(res, var1, var2, newVar, nodeNumber),
                                newRels
                            )
                        );
                } else if (underflowPair.x.equals(YNM.YES)
                    || res.checkRelation(relationFactory.lessThan(operation, lowerLimit), aborter).x) {
                    // certain underflow
                    final LLVMTerm simpleUnderflowOperation = termFactory.add(operation, size);
                    if (underflowPair.y.equals(YNM.YES)
                        || res.checkRelation(relationFactory.lessThanEquals(lowerLimit, simpleUnderflowOperation), aborter).x) {
                        final Set<LLVMRelation> newRels = new LinkedHashSet<>();
                        res = state.assign(varName, simpleUnderflowOperation, operandType, newRels, aborter).incrementPC();
                        final LLVMSymbolicVariable newVar = res.getSymbolicVariableForProgramVariable(varName);
                        return
                            Collections.singleton(
                                new LLVMSymbolicEvaluationResult(
                                    LLVMBinaryInstruction.checkTrap(res, var1, var2, newVar, nodeNumber),
                                    newRels
                                )
                            );
                    }
                } else {
                    // possible underflow -> refine
                    Set<LLVMSymbolicEvaluationResult> refRes = new LinkedHashSet<LLVMSymbolicEvaluationResult>();
                    LLVMRelation noUnderflowRelation = relationFactory.lessThanEquals(lowerLimit, operation);
                    refRes.add(
                        new LLVMSymbolicEvaluationResult(
                            state.addRelation(noUnderflowRelation, aborter),
                            Collections.singleton(noUnderflowRelation)
                        )
                    );
                    LLVMRelation underflowRelation = relationFactory.lessThan(operation, lowerLimit);
                    refRes.add(
                        new LLVMSymbolicEvaluationResult(
                            state.addRelation(underflowRelation, aborter),
                            Collections.singleton(underflowRelation)
                        )
                    );
                    return refRes;
                }
            } else if (overflowPair.x.equals(YNM.YES) || res.checkRelation(relationFactory.lessThan(upperLimit, operation), aborter).x) {
                // certain overflow
                final LLVMTerm simpleOverflowOperation = termFactory.sub(operation, size);
                if (overflowPair.y.equals(YNM.YES)
                    || res.checkRelation(relationFactory.lessThanEquals(simpleOverflowOperation, upperLimit), aborter).x) {
                    final Set<LLVMRelation> newRels = new LinkedHashSet<>();
                    res = state.assign(varName, simpleOverflowOperation, operandType, newRels, aborter).incrementPC();
                    final LLVMSymbolicVariable newVar = res.getSymbolicVariableForProgramVariable(varName);
                    return
                        Collections.singleton(
                            new LLVMSymbolicEvaluationResult(
                                LLVMBinaryInstruction.checkTrap(res, var1, var2, newVar, nodeNumber),
                                newRels
                            )
                        );
                }
            } else {
                // possible overflow
                if (lowerLimit == null || underflowPair.x.equals(YNM.NO)
                    || res.checkRelation(relationFactory.lessThanEquals(lowerLimit, operation), aborter).x) {
                    // no underflow -> refine
                    Set<LLVMSymbolicEvaluationResult> refRes = new LinkedHashSet<LLVMSymbolicEvaluationResult>();
                    LLVMRelation noOverflowRelation = relationFactory.lessThanEquals(operation, upperLimit);
                    refRes.add(
                        new LLVMSymbolicEvaluationResult(
                            state.addRelation(noOverflowRelation, aborter),
                            Collections.singleton(noOverflowRelation)
                        )
                    );
                    LLVMRelation overflowRelation = relationFactory.lessThan(upperLimit, operation);
                    refRes.add(
                        new LLVMSymbolicEvaluationResult(
                            state.addRelation(overflowRelation, aborter),
                            Collections.singleton(overflowRelation)
                        )
                    );
                    return refRes;
                } else if (underflowPair.x.equals(YNM.YES)
                    || res.checkRelation(relationFactory.lessThan(operation, lowerLimit), aborter).x) {
                    // certain underflow
                    if (Globals.useAssertions) {
                        assert(false) : "How is this possible?";
                    }
                } else {
                    // possible underflow -> double refine
                    Set<LLVMSymbolicEvaluationResult> refRes = new LinkedHashSet<LLVMSymbolicEvaluationResult>();
                    LLVMRelation noOverflowRelation = relationFactory.lessThanEquals(operation, upperLimit);
                    LLVMRelation noUnderflowRelation = relationFactory.lessThanEquals(lowerLimit, operation);
                    final Set<LLVMRelation> newRels1 = new LinkedHashSet<>();
                    newRels1.add(noOverflowRelation);
                    newRels1.add(noUnderflowRelation);
                    refRes.add(
                        new LLVMSymbolicEvaluationResult(
                            state.addRelation(noOverflowRelation, aborter).addRelation(noUnderflowRelation, aborter),
                            newRels1
                        )
                    );
                    LLVMRelation overflowRelation = relationFactory.lessThan(upperLimit, operation);
                    refRes.add(
                        new LLVMSymbolicEvaluationResult(
                            state.addRelation(overflowRelation, aborter),
                            Collections.singleton(overflowRelation)
                        )
                    );
                    LLVMRelation underflowRelation = relationFactory.lessThan(operation, lowerLimit);
                    refRes.add(
                        new LLVMSymbolicEvaluationResult(
                            state.addRelation(underflowRelation, aborter),
                            Collections.singleton(underflowRelation)
                        )
                    );
                    return refRes;
                }
            }
        }
        // TODO implement me
        throw new UnsupportedOperationException("Not implemented yet!");
//        final IntegerType intTypeOfResult = this.computeResultType(useBoundedIntegers);
//        final IntervalBound upperBound = intTypeOfResult.getUpper();
//        final IntervalBound lowerBound = intTypeOfResult.getLower();
//        final LLVMConstant upperLimit = upperBound.isFinite() ? termFactory.constant(upperBound.getConstant()) : null;
//        final LLVMConstant lowerLimit = lowerBound.isFinite() ? termFactory.constant(lowerBound.getConstant()) : null;
//        // TODO check trap values for operations based on exact, nuw, and nsw
//        if (upperLimit == null || res.checkRelation(relationFactory.lessThanEquals(operation, upperLimit))) {
//            // no overflow
//            if (lowerLimit == null || res.checkRelation(relationFactory.lessThanEquals(lowerLimit, operation))) {
//                // no underflow
//            } else if (res.checkRelation(relationFactory.lessThan(operation, lowerLimit))) {
//                // certain underflow
//            } else {
//                // possible underflow
//            }
//        } else if (res.checkRelation(relationFactory.lessThan(upperLimit, operation))) {
//            // certain overflow
//        } else {
//            // possible overflow
//            if (lowerLimit == null || res.checkRelation(relationFactory.lessThanEquals(lowerLimit, operation))) {
//                // no underflow
//            } else if (res.checkRelation(relationFactory.lessThan(operation, lowerLimit))) {
//                // certain underflow
//            } else {
//                // possible underflow
//            }
//        }
//        LLVMValue value1 = state.getValue(var1);
//        LLVMValue value2 = state.getValue(var2);
//        AbstractBoundedInt val1 = value1.getThisAsAbstractBoundedInt();
//        AbstractBoundedInt val2 = value2.getThisAsAbstractBoundedInt();
//        final boolean handleOverflows = useBoundedIntegers;
//        boolean refsAreEqual = var1.equals(var2);
//        AbstractBoundedInt result = null;
//        BigInteger innerUB = null;
//        BigInteger innerLB = null;
//        YNM posOverflow = this.checkPositiveOverflow(state, var1, var2, intTypeOfResult, params);
//        YNM negOverflow = this.checkNegativeOverflow(state, var1, var2, intTypeOfResult, params);
//        YNM unsignedOverflow = this.checkUnsignedOverflow(state, var1, var2, intTypeOfResult);
//        try {
//            switch (this.operator) {
//                case ADD:
//                    final Triple<AbstractBoundedInt, BigInteger, BigInteger> addResult =
//                        val1.add(val2, intTypeOfResult, handleOverflows, posOverflow, negOverflow);
//                    if (addResult.y == null || addResult.z == null) {
//                        if (Globals.useAssertions) {
//                            assert (addResult.y == null && addResult.z == null) :
//                                "Found addition result with only one inner bound.";
//                        }
//                    } else {
//                        // We have inner bounds for an interval, so we will add a new relation. E.g., an interval
//                        // [Minint, Maxint] with inner bounds -20 and -5 means x <= -20 or x >= -5.
//                        innerUB = addResult.y;
//                        innerLB = addResult.z;
//                    }
//                    result = addResult.x;
//                    break;
//                case SUB:
//                    BinaryInstruction.checkIntegerOperation(operandType, nodeNumber);
//                    final Triple<AbstractBoundedInt, BigInteger, BigInteger> subResult =
//                        val1.sub(
//                            val2,
//                            refsAreEqual,
//                            false,
//                            false,
//                            intTypeOfResult,
//                            handleOverflows,
//                            posOverflow,
//                            negOverflow
//                        );
//                    if (subResult.y == null || subResult.z == null) {
//                        if (Globals.useAssertions) {
//                            assert (subResult.y == null && subResult.z == null) :
//                                "Found subtraction result with only one inner bound.";
//                        }
//                    } else {
//                        // We have inner bounds for an interval, so we will add a new relation. E.g., an interval
//                        // [Minint, Maxint] with inner bounds -20 and -5 means x <= -20 or x >= -5.
//                        innerUB = subResult.y;
//                        innerLB = subResult.z;
//                    }
//                    result = subResult.x;
//                    break;
//                case MUL:
//                    BinaryInstruction.checkIntegerOperation(operandType, nodeNumber);
//                    final Triple<AbstractBoundedInt, BigInteger, BigInteger> mulResult =
//                        val1.mul(val2, intTypeOfResult, handleOverflows, posOverflow, negOverflow);
//                    if (mulResult.y == null || mulResult.z == null) {
//                        if (Globals.useAssertions) {
//                            assert (mulResult.y == null && mulResult.z == null) :
//                                "Found multiplication result with only one inner bound.";
//                        }
//                    } else {
//                        // We have inner bounds for an interval, so we will add a new relation. E.g., an interval
//                        // [Minint, Maxint] with inner bounds -20 and -5 means x <= -20 or x >= -5.
//                        innerUB = mulResult.y;
//                        innerLB = mulResult.z;
//                    }
//                    result = mulResult.x;
//                    break;
//                case SDIV:
//                    BinaryInstruction.checkIntegerOperation(operandType, nodeNumber);
//                    Triple<? extends AbstractBoundedInt, Boolean, Boolean> divRes =
//                        val1.div(val2, refsAreEqual, intTypeOfResult, handleOverflows);
//                    if (Globals.useAssertions) {
//                        assert (divRes.x != null || divRes.y) :
//                            "This should never happen. In theory, at least (node " + nodeNumber + ").";
//                    }
//                    if (divRes.y) {
//                        // dividing by zero => undefined behavior
//                        throw new UndefinedBehaviorException(nodeNumber);
//                    } else if (this.exact && divRes.z) {
//                        throw new UndefinedBehaviorException(
//                            "Rounding may occur despite the exact flag is set -> poison value (node "
//                            + nodeNumber
//                            + ")!"
//                        );
//                    } else if (posOverflow != YNM.NO){
//                        throw new UndefinedBehaviorException(
//                            "Overflow may occur for signed division operation (node "
//                            + nodeNumber
//                            + ")!"
//                        );
//                    }
//                    // dividing by a non-zero number, sign is the same as that of the first operand
//                    result = divRes.x;
//                    break;
//                case SREM:
//                    BinaryInstruction.checkIntegerOperation(operandType, nodeNumber);
//                    Pair<? extends AbstractBoundedInt, Boolean> remRes =
//                        val1.rem(val2, refsAreEqual, intTypeOfResult, handleOverflows);
//                    if (Globals.useAssertions) {
//                        assert (remRes.x != null || remRes.y) :
//                            "This should never happen. In theory, at least (node " + nodeNumber + ").";
//                    }
//                    if (remRes.y) {
//                        // dividing by zero => undefined behavior
//                        throw new UndefinedBehaviorException("Division by zero (" + nodeNumber + ")!");
//                    } else if (posOverflow != YNM.NO){
//                        throw new UndefinedBehaviorException(
//                            "Overflow may occur for signed remainder operation (node "
//                            + nodeNumber
//                            + ")!"
//                        );
//                    }
//                    // dividing by a non-zero number, sign is the same as that of the first operand
//                    result = remRes.x;
//                    break;
//                case UREM:
//                    BinaryInstruction.checkIntegerOperation(operandType, nodeNumber);
//                    Pair<? extends AbstractBoundedInt, Boolean> uremRes =
//                        val1.urem(val2, refsAreEqual, intTypeOfResult, handleOverflows);
//                    if (Globals.useAssertions) {
//                        assert (uremRes.x != null || uremRes.y) :
//                            "This should never happen. In theory, at least (node " + nodeNumber + ").";
//                    }
//                    if (uremRes.y) {
//                        // dividing by zero => undefined behavior
//                        throw new UndefinedBehaviorException("Division by zero (" + nodeNumber + ")!");
//                    } else if (posOverflow != YNM.NO){
//                        throw new UndefinedBehaviorException(
//                            "Overflow may occur for signed remainder operation (node "
//                            + nodeNumber
//                            + ")!"
//                        );
//                    }
//                    // dividing by a non-zero number, sign is the same as that of the first operand
//                    result = uremRes.x;
//                    break;
//                case AND:
//                    BinaryInstruction.checkIntegerOperation(operandType, nodeNumber);
//                    result = val1.and(val2, refsAreEqual, intTypeOfResult, !useBoundedIntegers);
//                    break;
//                case OR:
//                    BinaryInstruction.checkIntegerOperation(operandType, nodeNumber);
//                    result = val1.or(val2, refsAreEqual, intTypeOfResult, !useBoundedIntegers);
//                    break;
//                case XOR:
//                    BinaryInstruction.checkIntegerOperation(operandType, nodeNumber);
//                    result = val1.xor(val2, refsAreEqual, intTypeOfResult, !useBoundedIntegers);
//                    break;
//                case SHL:
//                    BinaryInstruction.checkIntegerOperation(operandType, nodeNumber);
//                    if (val2.isLiteral()) {
//                        BigInteger lit = val2.getLiteral();
//                        if (val2.isNegative() || lit.bitLength() >= operandType.size()) {
//                            throw new UndefinedBehaviorException(
//                               "Second operand for rightshift is too big! (node "
//                                + nodeNumber
//                                + ")!"
//                            );
//                        }
//                        AbstractBoundedInt resLiteral =
//                            AbstractBoundedInt.create(BigInteger.valueOf(2).pow(lit.intValue()));
//                        result = val1.mul(resLiteral, intTypeOfResult, useBoundedIntegers).x;
//                        if (useBoundedIntegers) {
//                            AbstractBoundedInt size =
//                                AbstractBoundedInt.create(BigInteger.valueOf(2).pow(operandType.size()));
//                            result = result.mod(size, result.equals(size), intTypeOfResult, useBoundedIntegers).x;
//                        }
//                    } else {
//                        if (val2.getLower().isNegative()
//                            || val2.getUpper().getConstant().bitLength() >= operandType.size()) {
//                            throw new UndefinedBehaviorException(
//                                "Second operand for rightshift is too big! (node "
//                                + nodeNumber
//                                + ")!"
//                            );
//                        }
//                        result = operandType.getInitializedIntValue(!useBoundedIntegers);
//                    }
//                    break;
//                case ASHR:
//                    BinaryInstruction.checkIntegerOperation(operandType, nodeNumber);
//                    if (val2.isLiteral()) {
//                        BigInteger lit = val2.getLiteral();
//                        if (val2.isNegative() || lit.bitLength() >= operandType.size()) {
//                            throw new UndefinedBehaviorException(
//                               "Second operand for rightshift is too big! (node "
//                                + nodeNumber
//                                + ")!"
//                            );
//                        }
//                        AbstractBoundedInt resLiteral =
//                            AbstractBoundedInt.create(BigInteger.valueOf(2).pow(lit.intValue()));
//                        Triple<? extends AbstractBoundedInt, Boolean, Boolean> triple;
//                        triple = val1.div(resLiteral, var1.equals(var2), intTypeOfResult, false);
//                        if (this.exact && triple.z) {
//                            throw new IllegalStateException("Rightshift would yield poison value!");
//                        }
//                        if (Globals.useAssertions) {
//                            assert (!triple.y) : "Division by zero with non-zero constant - how is this possible?";
//                        }
//                        result = triple.x;
//                    } else {
//                        if (val2.getLower().isNegative()
//                            || val2.getUpper().getConstant().bitLength() >= operandType.size()) {
//                            throw new UndefinedBehaviorException(
//                                "Second operand for rightshift is too big! (node "
//                                + nodeNumber
//                                + ")!"
//                            );
//                        }
//                        result = operandType.getInitializedIntValue(!useBoundedIntegers);
//                    }
//                    break;
//                case LSHR:
//                    BinaryInstruction.checkIntegerOperation(operandType, nodeNumber);
//                    if (val2.isLiteral()) {
//                        BigInteger lit = val2.getLiteral();
//                        if (val2.isNegative() || lit.bitLength() >= operandType.size()) {
//                            throw new UndefinedBehaviorException(
//                               "Second operand for rightshift is too big! (node "
//                                + nodeNumber
//                                + ")!"
//                            );
//                        }
//                        AbstractBoundedInt resLiteral =
//                            AbstractBoundedInt.create(BigInteger.valueOf(2).pow(lit.intValue()));
//                        Triple<? extends AbstractBoundedInt, Boolean, Boolean> triple;
//                        if (useBoundedIntegers && !val1.isNonNegative() && val2.isPositive()) {
//                            // negative values turn positive
//                            result = operandType.getInitializedIntValue(!useBoundedIntegers).onlyNonNegative();
//                        } else {
//                            triple = val1.div(resLiteral, var1.equals(var2), intTypeOfResult, false);
//                            if (this.exact && triple.z) {
//                                throw new IllegalStateException("Rightshift would yield poison value!");
//                            }
//                            if (Globals.useAssertions) {
//                                assert (!triple.y) : "Division by zero with non-zero constant - how is this possible?";
//                            }
//                            result = triple.x;
//                        }
//                    } else {
//                        if (val2.getLower().isNegative()
//                            || val2.getUpper().getConstant().bitLength() >= operandType.size()) {
//                            throw new UndefinedBehaviorException(
//                                "Second operand for rightshift is too big! (node "
//                                + nodeNumber
//                                + ")!"
//                            );
//                        }
//                        result = operandType.getInitializedIntValue(!useBoundedIntegers);
//                    }
//                    break;
//                default:
//                    // TODO add other cases
//                    // not yet implemented
//                    throw new RuntimeException(
//                        "Operator "
//                            + this.operator
//                            + " is not yet implemented (node "
//                            + nodeNumber
//                            + ")."
//                    );
//            }
//        } catch (OverflowException e) {
//            throw new IllegalStateException(
//                "This should only happen when working with bit-vector arithmetic (node " + nodeNumber + ")."
//            );
//        }
//        Collection<LLVMRelation> changeInformation = new LinkedHashSet<LLVMRelation>();
//        // if nsw is set, signed overflow results in a poison value
//        if (this.nsw && (posOverflow != YNM.NO || negOverflow != YNM.NO)) {
//            throw new UndefinedBehaviorException(
//                "A signed overflow may occur despite the nsw flag is set -> poison value (node "
//                + nodeNumber
//                + ")!"
//            );
//        }
//        // if nuw is set, unsigned overflow results in a poison value
//        if (this.nuw && unsignedOverflow != YNM.NO) {
//            throw new UndefinedBehaviorException(
//                "An unsigned overflow may occur despite the nuw flag is set -> poison value (node "
//                + nodeNumber
//                + ")!"
//            );
//        }
//        // the type of both arguments and the result must be the same - so just take the type of the first argument
//        Pair<LLVMAbstractState, LLVMHeuristicVariable> knowledge =
//            this.inferKnowledge(
//                state,
//                var1,
//                var2,
//                val1,
//                val2,
//                result,
//                intTypeOfResult,
//                changeInformation,
//                posOverflow,
//                negOverflow,
//                params
//            );
//        // set variable entry, increase the program counter by one, unset refinement flag (done within PC increment)
//        // and add the new relation
//        LLVMAbstractState res =
//            knowledge.x.setProgramVariable(this.getIdentifier().getName(), knowledge.y, operandType).incrementPC();
//        Collection<LLVMStateChangeInformation> resInfo =
//            new LinkedHashSet<LLVMStateChangeInformation>(changeInformation);
//        // if we have inner bounds, add a relation to keep the information we lost
//        if (innerUB != null && (posOverflow != YNM.NO || negOverflow != YNM.NO)) {
//            // innerLB and innerUB are inner bounds (overflow occurred)
//            Set<LLVMRelation> rels = new HashSet<LLVMRelation>();
//            LLVMRelation newRel = LLVMRelationFactory.createRelationForInnerBounds(knowledge.y, operandType, innerUB, innerLB);
//            rels.add(newRel);
//            changeInformation.add(newRel);
//            resInfo = new LinkedHashSet<LLVMStateChangeInformation>(changeInformation);
//            res = BinaryInstruction.addRelations(res, rels, resInfo, params);
//        }
//        if (value1 instanceof LLVMTrapValue) {
//            if (value2 instanceof LLVMTrapValue) {
//                if (!var1.equals(var2)) {
//                    throw new UndefinedBehaviorException(
//                        "Accessing two different trap values at node " + nodeNumber + "."
//                    );
//                }
//            }
//            if (knowledge.y.isConcrete()) {
//                throw new IllegalStateException("Cannot assign trap value to constant!");
//            }
//            res =
//                res.putTrapValue(
//                    knowledge.y,
//                    res.getValue(knowledge.y),
//                    ((LLVMTrapValue)value1).getAssociationDependency()
//                );
//        } else if (value2 instanceof LLVMTrapValue) {
//            if (knowledge.y.isConcrete()) {
//                throw new IllegalStateException("Cannot assign trap value to constant!");
//            }
//            res =
//                res.putTrapValue(
//                    knowledge.y,
//                    res.getValue(knowledge.y),
//                    ((LLVMTrapValue)value2).getAssociationDependency()
//                );
//        }
//        // check if the changes let us replace references
//        if (!changeInformation.isEmpty()) {
//            ReplacementResult replacement = IntegerUtils.resolveReferenceEqualities(res, params);
//            res = replacement.x;
//            resInfo.clear();
//            for (LLVMRelation rel : changeInformation) {
//                resInfo.add(rel.applySubstitution(replacement.y));
//            }
//        }
//        // finally return the state and its change information
//        return new Pair<LLVMAbstractState, Collection<LLVMStateChangeInformation>>(res, resInfo);
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder res = new StringBuilder();
        res.append(eu.tttext(this.getIdentifier().toString()));
        res.append(eu.tttext(" = "));
        res.append(eu.tttext(this.operator.toString().toLowerCase()));
        res.append(eu.tttext(" "));
        res.append(eu.tttext(this.operand1Value.toString()));
        res.append(eu.tttext(" "));
        res.append(eu.tttext(this.operand2Value.toString()));
        return res.toString();
    }

    @Override
    public Set<String> getInterestingVariables() {
        Set<String> vars = new LinkedHashSet<>();
        // without knowing more about the possible values of the variables,
        // we'll have to consider all operands interesting
        this.collectVariables(vars);
        return vars;
    }
    
    /**
     * @return The set of names of operands of this instruction.
     */
    public ImmutableSet<String> getOperandNames() {
        LinkedHashSet<String> res = new LinkedHashSet<String>();
        if (this.operand1Value instanceof LLVMVariableLiteral) {
            res.add(((LLVMVariableLiteral)this.operand1Value).getName());
        }
        if (this.operand2Value instanceof LLVMVariableLiteral) {
            res.add(((LLVMVariableLiteral)this.operand2Value).getName());
        }
        return ImmutableCreator.create(res);
    }

    /**
     * @return The set of operands of this instruction.
     */
    public ImmutableSet<LLVMLiteral> getOperands() {
        LinkedHashSet<LLVMLiteral> res = new LinkedHashSet<LLVMLiteral>();
        res.add(this.operand1Value);
        res.add(this.operand2Value);
        return ImmutableCreator.create(res);
    }
    
    /**
     * @return True iff this seems like an instruction on originally signed integers.
     */
    public boolean seemsSigned() {
        return this.nsw || this.operator.equals(LLVMBinaryOpType.ASHR);
    }
    
    /**
     * @return True iff this seems like an instruction on originally unsigned integers.
     */
    public boolean seemsUnsigned() {
        return (!this.nsw && (this.operator.equals(LLVMBinaryOpType.ADD) || this.operator.equals(LLVMBinaryOpType.SUB) ||
                this.operator.equals(LLVMBinaryOpType.MUL)));
    }

    /**
     * @return This instruction's operator
     */
    public LLVMBinaryOpType getOperator() {
        return this.operator;
    }

    @Override
    public boolean isOverapproximation(LLVMAbstractState state, Abortion aborter) {
        return operator.isOverapproximation();
    }

//    @Override
//    public Set<LLVMSymbolicEvaluationResult> refine(LLVMAbstractState state, int nodeNumber) {
//        if (!state.getStrategyParamters().useBoundedIntegers) {
//            return null;
//        }
//        final BasicType operandType = this.operand1Value.getType();
//        final LLVMTerm ref1 = state.getTermForLiteral(this.operand1Value);
//        final LLVMTerm ref2 = state.getTermForLiteral(this.operand2Value);
//        final LLVMValue value1 = state.getValue(ref1);
//        final LLVMValue value2 = state.getValue(ref2);
//        final AbstractBoundedInt val1 = value1.getThisAsAbstractBoundedInt();
//        final AbstractBoundedInt val2 = value2.getThisAsAbstractBoundedInt();
//        Set<RefinementResult> refSet = null;
//        switch (this.operator) {
//        case ADD:
//            if (operandType.isIntType()) {
//                final IntegerType intType = ((BasicIntType) operandType).getIntegerType();
//                YNM posOverflow = this.checkPositiveOverflow(state, ref1, ref2, intType, params);
//                YNM negOverflow = this.checkNegativeOverflow(state, ref1, ref2, intType, params);
//                if (posOverflow != YNM.MAYBE && negOverflow != YNM.MAYBE) {
//                    return null;
//                }
//                if (posOverflow == YNM.MAYBE) {
//                    if (val1.isIntLiteral()) {
//                        final BigInteger c = val1.getLiteral();
//                        refSet = IntegerUtils.refineIntegerValuesForRelation(
//                            state,
//                            ref2,
//                            IntegerRelationType.LE,
//                            new LLVMHeuristicConstRef(intType.getUpper().getConstant().subtract(c)),
//                            params
//                        );
//                    } else if (val2.isIntLiteral()) {
//                        final BigInteger c = val2.getLiteral();
//                        refSet = IntegerUtils.refineIntegerValuesForRelation(
//                            state,
//                            ref1,
//                            IntegerRelationType.LE,
//                            new LLVMHeuristicConstRef(intType.getUpper().getConstant().subtract(c)),
//                            params
//                        );
//                    } else if (ref1.equals(ref2)) {
//                        refSet = IntegerUtils.refineIntegerValuesForRelation(
//                            state,
//                            ref1,
//                            IntegerRelationType.LE,
//                            new LLVMHeuristicConstRef(intType.getUpper().getConstant().divide(BigInteger.valueOf(2))),
//                            params
//                        );
//                    } else {
//                        refSet = IntegerUtils.refineStateForBoundRelation(
//                            state,
//                            (LLVMOperation)termFactory.operation(ArithmeticOperationType.ADD, ref1, ref2),
//                            IntegerRelationType.LE,
//                            new LLVMHeuristicConstRef(intType.getUpper().getConstant()),
//                            params
//                        );
//                    }
//                } else if (negOverflow == YNM.MAYBE) {
//                    if (val1.isIntLiteral()) {
//                        final BigInteger c = val1.getLiteral();
//                        refSet = IntegerUtils.refineIntegerValuesForRelation(
//                            state,
//                            new LLVMHeuristicConstRef(intType.getLower().getConstant().subtract(c)),
//                            IntegerRelationType.LE,
//                            ref2,
//                            params
//                        );
//                    } else if (val2.isIntLiteral()) {
//                        final BigInteger c = val2.getLiteral();
//                        refSet = IntegerUtils.refineIntegerValuesForRelation(
//                            state,
//                            new LLVMHeuristicConstRef(intType.getLower().getConstant().subtract(c)),
//                            IntegerRelationType.LE,
//                            ref1,
//                            params
//                        );
//                    } else if (ref1.equals(ref2)) {
//                        refSet = IntegerUtils.refineIntegerValuesForRelation(
//                            state,
//                            new LLVMHeuristicConstRef(intType.getLower().getConstant().divide(BigInteger.valueOf(2))),
//                            IntegerRelationType.LE,
//                            ref1,
//                            params
//                        );
//                    } else {
//                        refSet = IntegerUtils.refineStateForBoundRelation(
//                            state,
//                            (LLVMOperation)termFactory.operation(ArithmeticOperationType.ADD, ref1, ref2),
//                            IntegerRelationType.LT,
//                            new LLVMHeuristicConstRef(intType.getLower().getConstant()),
//                            params
//                        );
//                    }
//                }
//            }
//            break;
//        case SUB:
//            if (operandType.isIntType()) {
//                final IntegerType intType = ((BasicIntType) operandType).getIntegerType();
//                YNM posOverflow = this.checkPositiveOverflow(state, ref1, ref2, intType, params);
//                YNM negOverflow = this.checkNegativeOverflow(state, ref1, ref2, intType, params);
//                if (posOverflow != YNM.MAYBE && negOverflow != YNM.MAYBE) {
//                    return null;
//                }
//                if (posOverflow == YNM.MAYBE) {
//                    if (val1.isIntLiteral()) {
//                        final BigInteger c = val1.getLiteral();
//                        refSet = IntegerUtils.refineIntegerValuesForRelation(
//                            state,
//                            new LLVMHeuristicConstRef(c.subtract(intType.getUpper().getConstant())),
//                            IntegerRelationType.LE,
//                            ref2,
//                            params
//                        );
//                    } else if (val2.isIntLiteral()) {
//                        final BigInteger c = val2.getLiteral();
//                        refSet = IntegerUtils.refineIntegerValuesForRelation(
//                            state,
//                            ref1,
//                            IntegerRelationType.LE,
//                            new LLVMHeuristicConstRef(intType.getUpper().getConstant().add(c)),
//                            params
//                        );
//                    } else {
//                        refSet = IntegerUtils.refineStateForBoundRelation(
//                            state,
//                            (LLVMOperation) termFactory.operation(ArithmeticOperationType.SUB, ref1, ref2),
//                            IntegerRelationType.LE,
//                            new LLVMHeuristicConstRef(intType.getUpper().getConstant()),
//                            params
//                        );
//                    }
//                } else if (negOverflow == YNM.MAYBE) {
//                    if (val1.isIntLiteral()) {
//                        final BigInteger c = val1.getLiteral();
//                        refSet = IntegerUtils.refineIntegerValuesForRelation(
//                            state,
//                            ref2,
//                            IntegerRelationType.LT,
//                            new LLVMHeuristicConstRef(c.subtract(intType.getLower().getConstant())),
//                            params
//                        );
//                    } else if (val2.isIntLiteral()) {
//                        final BigInteger c = val2.getLiteral();
//                        refSet = IntegerUtils.refineIntegerValuesForRelation(
//                            state,
//                            new LLVMHeuristicConstRef(intType.getLower().getConstant().add(c)),
//                            IntegerRelationType.LE,
//                            ref1,
//                            params
//                        );
//                    } else {
//                        refSet = IntegerUtils.refineStateForBoundRelation(
//                            state,
//                            (LLVMOperation) termFactory.operation(ArithmeticOperationType.SUB, ref1, ref2),
//                            IntegerRelationType.LT,
//                            new LLVMHeuristicConstRef(intType.getLower().getConstant()),
//                            params
//                        );
//                    }
//                }
//            }
//        case MUL:
//            if (operandType.isIntType()) {
//                final IntegerType intType = ((BasicIntType) operandType).getIntegerType();
//                YNM posOverflow = this.checkPositiveOverflow(state, ref1, ref2, intType, params);
//                YNM negOverflow = this.checkNegativeOverflow(state, ref1, ref2, intType, params);
//                if (posOverflow != YNM.MAYBE && negOverflow != YNM.MAYBE) {
//                    return null;
//                }
//                // special case: one operand is 2
//                // leads to very big graphs in some cases
////                if (posOverflow == YNM.MAYBE) {
////                    if (val1.isIntLiteral() && val1.getIntLiteralValue().equals(BigInteger.valueOf(2))) {
////                        refSet = LLVMIntegerUtils.refineIntegerValuesForRelation(
////                            state,
////                            ref2,
////                            IntegerRelationType.LE,
////                            new LLVMConstRef(
////                                intType.getUpper().getConstant().divide(BigInteger.valueOf(2)),
////                                ref2.getType()
////                            ),
////                            useSMT,
////                            aborter
////                        );
////                    } else if (val2.isIntLiteral() && val2.getIntLiteralValue().equals(BigInteger.valueOf(2))) {
////                        refSet = LLVMIntegerUtils.refineIntegerValuesForRelation(
////                            state,
////                            ref1,
////                            IntegerRelationType.LE,
////                            new LLVMConstRef(
////                                intType.getUpper().getConstant().divide(BigInteger.valueOf(2)),
////                                ref1.getType()
////                            ),
////                            useSMT,
////                            aborter
////                        );
////                    }
////                } else if (negOverflow == YNM.MAYBE) {
////                    if (val1.isIntLiteral() && val1.getIntLiteralValue().equals(BigInteger.valueOf(2))) {
////                        refSet = LLVMIntegerUtils.refineIntegerValuesForRelation(
////                            state,
////                            new LLVMConstRef(
////                                intType.getLower().getConstant().divide(BigInteger.valueOf(2)),
////                                ref2.getType()
////                            ),
////                            IntegerRelationType.LE,
////                            ref2,
////                            useSMT,
////                            aborter
////                        );
////                    } else if (val2.isIntLiteral() && val2.getIntLiteralValue().equals(BigInteger.valueOf(2))) {
////                        refSet = LLVMIntegerUtils.refineIntegerValuesForRelation(
////                            state,
////                            new LLVMConstRef(
////                                intType.getLower().getConstant().divide(BigInteger.valueOf(2)),
////                                ref1.getType()
////                            ),
////                            IntegerRelationType.LE,
////                            ref1,
////                            useSMT,
////                            aborter
////                        );
////                    }
////                }
//            }
//            break;
//        case SDIV:
//        default:
//        }
//        return refSet;
//    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("BinaryInstr ");
        strBuilder.append(" operator: " + this.operator);
        strBuilder.append(" identifier: " + this.getIdentifier());
        strBuilder.append(" nuw: " + this.nuw);
        strBuilder.append(" nsw: " + this.nsw);
        strBuilder.append(" exact: " + this.exact);
        strBuilder.append(" opType: " + this.operand1Value.getType());
        strBuilder.append(" op1Value: " + this.operand1Value);
        strBuilder.append(" op2Value: " + this.operand2Value);
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        StringBuilder res = new StringBuilder();
        res.append(this.getIdentifier().toDOTString());
        res.append(" = ");
        res.append(this.operator.toString().toLowerCase());
        res.append(" ");
        res.append(this.operand1Value.toDOTString());
        res.append(" ");
        res.append(this.operand2Value.toDOTString());
        return res.toString();
    }

    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        res.append(this.getIdentifier());
        res.append(" = ");
        res.append(this.operator.toString().toLowerCase());
        res.append(" ");
        res.append(this.operand1Value.getType());
        res.append(" ");
        res.append(this.operand1Value);
        res.append(", ");
        res.append(this.operand2Value);
        return res.toString();
    }

    @Override
    public String toLLVMIR() {
        StringBuilder res = new StringBuilder();
        res.append(this.getIdentifier());
        res.append(" = ");
        res.append(this.operator.toString().toLowerCase());
        res.append(" ");
        res.append(this.operand1Value.getType());
        res.append(" ");
        res.append(this.operand1Value);
        res.append(", ");
        res.append(this.operand2Value);
        return res.toString();
    }

//    /**
//     * @param val1 The first value.
//     * @param val2 The second value.
//     * @param intType The integer type of the references.
//     * @return True iff no overflow possible according to bounds.
//     */
//    private YNM checkBoundsForNegativeOverflow(
//        AbstractBoundedInt val1,
//        AbstractBoundedInt val2,
//        IntegerType intType
//    ) {
//        if (intType.equals(IntegerType.UNBOUND)) {
//            return YNM.NO;
//        }
//        switch (this.operator) {
//            case ADD:
//                if (val1.getLower().add(val2.getLower()).compareTo(intType.getLower()) >= 0) {
//                    return YNM.NO;
//                } else if (val1.getUpper().add(val2.getUpper()).compareTo(intType.getLower()) < 0) {
//                    return YNM.YES;
//                }
//                break;
//            case SUB:
//                if (val1.getLower().add(val2.getUpper().negate()).compareTo(intType.getLower()) >= 0) {
//                    return YNM.NO;
//                } else if (val1.getUpper().add(val2.getLower().negate()).compareTo(intType.getLower()) < 0) {
//                    return YNM.YES;
//                }
//                break;
//            case MUL:
//                if ((val1.isNonNegative() && val2.isNonNegative())
//                    || (val1.isNegative() && val2.isNonNegative()
//                        && (val1.getLower().mul(val2.getUpper()).compareTo(intType.getLower())) >= 0)
//                    || (val1.isNonNegative() && val2.isNegative()
//                        && (val1.getUpper().mul(val2.getLower()).compareTo(intType.getLower())) >= 0)) {
//                    return YNM.NO;
//                } else if ((val1.isNegative() && val2.isNonNegative()
//                        && (val1.getUpper().mul(val2.getLower()).compareTo(intType.getLower()) < 0))
//                    || (val1.isNonNegative() && val2.isNegative()
//                        && (val1.getLower().mul(val2.getUpper()).compareTo(intType.getLower()) < 0))){
//                    return YNM.YES;
//                } else {
//                    // TODO
//                    return YNM.MAYBE;
//                }
//            default:
//        }
//        return YNM.MAYBE;
//    }
//
//    /**
//     * @param val1 The first value.
//     * @param val2 The second value.
//     * @param intType The integer type of the references.
//     * @return True iff no overflow possible according to bounds.
//     */
//    private YNM checkBoundsForPositiveOverflow(
//        AbstractBoundedInt val1,
//        AbstractBoundedInt val2,
//        IntegerType intType
//    ) {
//        if (intType.equals(IntegerType.UNBOUND)) {
//            return YNM.NO;
//        }
//        switch (this.operator) {
//            case ADD:
//                if (val1.getUpper().add(val2.getUpper()).compareTo(intType.getUpper()) <= 0) {
//                    return YNM.NO;
//                } else if (val1.getLower().add(val2.getLower()).compareTo(intType.getUpper()) > 0) {
//                    return YNM.YES;
//                }
//                break;
//            case SUB:
//                if (val1.getUpper().add(val2.getLower().negate()).compareTo(intType.getUpper()) <= 0) {
//                    return YNM.NO;
//                } else if (val1.getLower().add(val2.getUpper().negate()).compareTo(intType.getUpper()) > 0) {
//                    return YNM.YES;
//                }
//                break;
//            case MUL:
//                if ((val1.getUpper().mul(val2.getUpper()).compareTo(intType.getUpper()) <= 0)
//                    && (val1.getLower().mul(val2.getLower()).compareTo(intType.getUpper()) <= 0)) {
//                    return YNM.NO;
//                } else if (val1.getLower().isPositive() && val2.getLower().isPositive()
//                    &&  (val1.getLower().mul(val2.getLower()).compareTo(intType.getUpper()) > 0)) {
//                    return YNM.YES;
//                }
//                break;
//            default:
//        }
//        return YNM.MAYBE;
//    }
//
//    /**
//     * @param state The current state.
//     * @param ref1 The first reference.
//     * @param ref2 The second reference.
//     * @param intType The integer type of the references.
//     * @param params Strategy parameters.
//     * @return YES if a negative overflow definitely occurs, NO if it does not occur, MAYBE if it may occur.
//     */
//    private YNM checkNegativeOverflow(
//        LLVMAbstractState state,
//        LLVMHeuristicVariable ref1,
//        LLVMHeuristicVariable ref2,
//        IntegerType intType,
//        LLVMParameters params
//    ) {
//        LLVMValue value1 = state.getValue(ref1);
//        LLVMValue value2 = state.getValue(ref2);
//        AbstractBoundedInt val1 = value1.getThisAsAbstractBoundedInt();
//        AbstractBoundedInt val2 = value2.getThisAsAbstractBoundedInt();
//        YNM negOverflow = this.checkBoundsForNegativeOverflow(val1, val2, intType);
//        if (negOverflow != YNM.MAYBE) {
//            return negOverflow;
//        }
//        switch (this.operator) {
//            case ADD:
//                negOverflow =
//                    IntegerUtils.truthValueOfRelation(
//                        state,
//                        termFactory.operation(ArithmeticOperationType.ADD, ref1, ref2),
//                        IntegerRelationType.LT,
//                        new LLVMHeuristicConstRef(intType.getLower().getConstant()),
//                        true,
//                        params
//                    );
//                break;
//            case SUB:
//                negOverflow =
//                    IntegerUtils.truthValueOfRelation(
//                        state,
//                        ref1,
//                        IntegerRelationType.LT,
//                        termFactory.operation(
//                            ArithmeticOperationType.ADD,
//                            new LLVMHeuristicConstRef(intType.getLower().getConstant()),
//                            ref2
//                        ),
//                        true,
//                        params
//                    );
//                break;
//            case MUL:
//                negOverflow =
//                    IntegerUtils.truthValueOfRelation(
//                        state,
//                        termFactory.operation(ArithmeticOperationType.MUL, ref1, ref2),
//                        IntegerRelationType.LT,
//                        new LLVMHeuristicConstRef(intType.getLower().getConstant()),
//                        true,
//                        params
//                    );
//                break;
//            case SHL:
//                // TODO
//                negOverflow =YNM.MAYBE;
//            default:
//                negOverflow = YNM.NO;
//        }
//        return negOverflow;
//    }
//
//    /**
//     * @param state The current state.
//     * @param ref1 The first reference.
//     * @param ref2 The second reference.
//     * @param intType The integer type of the references.
//     * @param params Strategy parameters.
//     * @return YES if a positive overflow definitely occurs, NO if it does not occur, MAYBE if it may occur.
//     */
//    private YNM checkPositiveOverflow(
//        LLVMAbstractState state,
//        LLVMHeuristicVariable ref1,
//        LLVMHeuristicVariable ref2,
//        IntegerType intType,
//        LLVMParameters params
//    ) {
//        LLVMValue value1 = state.getValue(ref1);
//        LLVMValue value2 = state.getValue(ref2);
//        AbstractBoundedInt val1 = value1.getThisAsAbstractBoundedInt();
//        AbstractBoundedInt val2 = value2.getThisAsAbstractBoundedInt();
//        YNM posOverflow = this.checkBoundsForPositiveOverflow(val1, val2, intType);
//        if (posOverflow != YNM.MAYBE) {
//            return posOverflow;
//        }
//        switch (this.operator) {
//            case ADD:
//                posOverflow =
//                    IntegerUtils.truthValueOfRelation(
//                        state,
//                        termFactory.operation(ArithmeticOperationType.ADD, ref1, ref2),
//                        IntegerRelationType.GT,
//                        new LLVMHeuristicConstRef(intType.getUpper().getConstant()),
//                        true,
//                        params
//                    );
//                break;
//            case SUB:
//                posOverflow =
//                    IntegerUtils.truthValueOfRelation(
//                        state,
//                        termFactory.operation(
//                            ArithmeticOperationType.ADD,
//                            new LLVMHeuristicConstRef(intType.getUpper().getConstant()),
//                            ref2
//                        ),
//                        IntegerRelationType.LT,
//                        ref1,
//                        true,
//                        params
//                    );
//                break;
//            case MUL:
//                posOverflow =
//                    IntegerUtils.truthValueOfRelation(
//                        state,
//                        termFactory.operation(ArithmeticOperationType.MUL, ref1, ref2),
//                        IntegerRelationType.GT,
//                        new LLVMHeuristicConstRef(intType.getUpper().getConstant()),
//                        true,
//                        params
//                    );
//                break;
//            case SDIV:
//            case SREM:
//                if (!(val1.getLower().equals(intType.getLower()) && val2.containsLiteral(-1))) {
//                    posOverflow = YNM.NO;
//                }
//                break;
//            case SHL:
//                // TODO
//                posOverflow =YNM.MAYBE;
//            default:
//                posOverflow = YNM.NO;
//        }
//        return posOverflow;
//    }
//
//    /**
//     * @param state The current state.
//     * @param ref1 The first reference.
//     * @param ref2 The second reference.
//     * @param intType The integer type of the references.
//     * @return YES if an unsigned overflow definitely occurs, NO if it does not occur, MAYBE if it may occur.
//     */
//    private YNM checkUnsignedOverflow(
//        LLVMAbstractState state,
//        LLVMHeuristicVariable ref1,
//        LLVMHeuristicVariable ref2,
//        IntegerType intType
//    ) {
//        if (intType.equals(IntegerType.UNBOUND)) {
//            return YNM.NO;
//        }
//        LLVMValue value1 = state.getValue(ref1);
//        LLVMValue value2 = state.getValue(ref2);
//        AbstractBoundedInt val1 = value1.getThisAsAbstractBoundedInt();
//        AbstractBoundedInt val2 = value2.getThisAsAbstractBoundedInt();
//        BigInteger typeSize = BigInteger.valueOf(2).pow(intType.getBitSize());
//        // determine maximum value of val1 in unsigned interpretation
//        final BigInteger val1unsignedMax;
//        if (val1.isNonNegative()) {
//            val1unsignedMax = val1.getUpper().getConstant();
//        } else {
//            val1unsignedMax = val1.getUpper().getConstant().mod(typeSize);
//        }
//        // determine maximum value of val2 in unsigned interpretation
//        final BigInteger val2unsignedMax;
//        if (val2.isNonNegative()) {
//            val2unsignedMax = val2.getUpper().getConstant().mod(typeSize);
//        } else {
//            val2unsignedMax = typeSize.subtract(BigInteger.ONE);
//        }
//        // determine minimum value of val1 (for subtraction)
//        final BigInteger val1unsignedMin;
//        if (val1.isNegative()) {
//            val1unsignedMin = val1.getLower().getConstant().mod(typeSize);
//        } else {
//            val1unsignedMin = val1.getLower().getConstant();
//        }
//        YNM unsignedOverflow = YNM.MAYBE;
//        switch (this.operator) {
//            case ADD:
//                if (val1unsignedMax.add(val2unsignedMax).compareTo(typeSize) < 0) {
//                    unsignedOverflow = YNM.NO;
//                }
//                break;
//            case SUB:
//                if (val1unsignedMin.subtract(val2unsignedMax).compareTo(BigInteger.ZERO) >= 0) {
//                    unsignedOverflow = YNM.NO;
//                }
//                break;
//            case MUL:
//                if (val1unsignedMax.multiply(val2unsignedMax).compareTo(typeSize) < 0) {
//                    unsignedOverflow = YNM.NO;
//                }
//                break;
//            case SHL:
//                // TODO
//                unsignedOverflow =YNM.MAYBE;
//            default:
//                unsignedOverflow = YNM.NO;
//        }
//        return unsignedOverflow;
//    }

    /**
     * @param unsigned
     * @param useBoundedIntegers
     * @return The integer type of the result.
     */
    private IntegerType computeResultType(boolean unsigned, boolean useBoundedIntegers) {
        if (!useBoundedIntegers) {
            return IntegerType.UNBOUND;
        }
        LLVMType type1 = this.operand1Value.getType();
        LLVMType type2 = this.operand2Value.getType();
        if (type1 instanceof LLVMIntType || type2 instanceof LLVMIntType) {
            if (Globals.useAssertions) {
                // both operand types have to be the same
                assert (type1 instanceof LLVMIntType && type2 instanceof LLVMIntType) :
                    "Binary instruction with undefined result type found.";
            }
            // define the corresponding IntegerTypes
            IntegerType intType1 = ((LLVMIntType)type1).getIntegerType(unsigned, true);
            IntegerType intType2 = ((LLVMIntType)type2).getIntegerType(unsigned, true);
            if (Globals.useAssertions) {
                // both operand types have to be the same integer type
                assert (intType1.equals(intType2)) : "Binary instruction with undefined result type found.";
            }
            return intType1;
        }
        throw new IllegalStateException("Binary instruction with undefined result type found.");
    }

//    /**
//     * @param relations The known relations.
//     * @param idRef The reference for the result.
//     * @param triple The new state, the inferred relations so far and a null pointer.
//     * @param refs The operand references.
//     * @param vals The values of the operand references.
//     * @param changeInformation The state change information.
//     * @param params Strategy parameters.
//     * @return The resulting state, the reference to the result, and the inferred new knowledge.
//     */
//    private Pair<LLVMAbstractState, LLVMHeuristicVariable> finalKnowledge(
//        IntegerRelationSet relations,
//        LLVMHeuristicVariable idRef,
//        Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable> triple,
//        Pair<LLVMHeuristicVariable, LLVMHeuristicVariable> refs,
//        Pair<AbstractBoundedInt, AbstractBoundedInt> vals,
//        Collection<LLVMRelation> changeInformation,
//        LLVMParameters params
//    ) {
//        LLVMHeuristicVariable ref1 = refs.x;
//        LLVMHeuristicVariable ref2 = refs.y;
//        AbstractBoundedInt val1 = vals.x;
//        AbstractBoundedInt val2 = vals.y;
//        Pair<LLVMAbstractState, IntegerRelationSet> res = triple.x.addRelations(triple.y, params);
//        changeInformation.addAll(res.y);
//        boolean ref2IsNotConcrete = !ref2.isConcrete();
//        if (this.operator == BinaryOpType.MUL || this.operator == BinaryOpType.SDIV) {
//            // add relations to one and -one if we do not have a constant
//            BinaryInstruction.addMultInfo(ref1, val1, changeInformation);
//            if (ref2IsNotConcrete) {
//                BinaryInstruction.addMultInfo(ref2, val2, changeInformation);
//            }
//        } else if (ref2IsNotConcrete) {
//            /*
//             * We have an operation with two variable operands. Save information about their sign in the state change
//             * information.
//             */
//            BinaryInstruction.addSignInfo(ref1, val1, changeInformation);
//            BinaryInstruction.addSignInfo(ref2, val2, changeInformation);
//        }
//        return new Pair<LLVMAbstractState, LLVMHeuristicVariable>(res.x, idRef);
//    }
//
//    /**
//     * @param newState The state in construction.
//     * @param opRef1 The first argument reference.
//     * @param opRef2 The second argument reference.
//     * @param opVal1 The first argument's value.
//     * @param opVal2 The second argument's value.
//     * @param result The result.
//     * @param intTypeOfResult The type of the result.
//     * @param changeInformation The state change information.
//     * @param posOverflow NO if we can exclude positive overflows, YES if we have a positive overflow for sure.
//     * @param negOverflow NO if we can exclude negative overflows, YES if we have a negative overflow for sure.
//     * @param params Strategy parameters.
//     * @return The resulting state, the reference to the result, and the inferred new knowledge.
//     */
//    private Pair<LLVMAbstractState, LLVMHeuristicVariable> inferKnowledge(
//        LLVMAbstractState newState,
//        LLVMHeuristicVariable opRef1,
//        LLVMHeuristicVariable opRef2,
//        AbstractBoundedInt opVal1,
//        AbstractBoundedInt opVal2,
//        AbstractBoundedInt result,
//        IntegerType intTypeOfResult,
//        Collection<LLVMRelation> changeInformation,
//        YNM posOverflow,
//        YNM negOverflow,
//        LLVMParameters params
//    ) {
//        BasicType type = this.getIdentifier().getType();
//        if (result.isIntLiteral()) {
//            // the computation is uniquely determined - just return the corresponding constant reference
//            return new Pair<LLVMAbstractState, LLVMHeuristicVariable>(newState, result.createLLVMRef());
//        }
//        // otherwise we must have at least one variable
//        LLVMHeuristicVariable idRef = result.createLLVMRef();
//        IntegerRelationSet relations = new IntegerRelationSet(newState.getRelations());
//        final LLVMHeuristicVariable ref1;
//        final LLVMHeuristicVariable ref2;
//        final AbstractBoundedInt val1;
//        final AbstractBoundedInt val2;
//        final boolean swapped;
//        // now let's try to infer some interesting (in)equalities from this
//        if (opRef1.isConcrete()) {
//            ref1 = opRef2;
//            ref2 = opRef1;
//            val1 = opVal2;
//            val2 = opVal1;
//            swapped = true;
//        } else {
//            ref1 = opRef1;
//            ref2 = opRef2;
//            val1 = opVal1;
//            val2 = opVal2;
//            swapped = false;
//        }
//        if (Globals.useAssertions) {
//            assert (!ref1.isConcrete()) : "We have two constants, but an ambiguous result - how is this possible?";
//        }
//        // ref1 is variable, ref2 can be constant or variable
//        final Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable> triple;
//        switch (this.operator) {
//        case ADD:
//            triple =
//                BinaryInstruction.knowledgeForAddition(
//                    newState,
//                    relations,
//                    idRef,
//                    ref1,
//                    ref2,
//                    type,
//                    val2,
//                    result,
//                    posOverflow,
//                    negOverflow
//                );
//            if (triple.z != null) {
//                return new Pair<LLVMAbstractState, LLVMHeuristicVariable>(triple.x, triple.z);
//            }
//            break;
//        case SUB:
//            triple =
//                swapped ?
//                    BinaryInstruction.knowledgeForSubtraction(
//                        newState,
//                        relations,
//                        idRef,
//                        ref2,
//                        ref1,
//                        type,
//                        val1,
//                        (IntervalBoundedInt) result,
//                        posOverflow,
//                        negOverflow,
//                        params
//                    ) :
//                        BinaryInstruction.knowledgeForSubtraction(
//                            newState,
//                            relations,
//                            idRef,
//                            ref1,
//                            ref2,
//                            type,
//                            val2,
//                            (IntervalBoundedInt) result,
//                            posOverflow,
//                            negOverflow,
//                            params
//                        );
//            if (triple.z != null) {
//                return new Pair<LLVMAbstractState, LLVMHeuristicVariable>(triple.x, triple.z);
//            }
//            break;
//        case MUL:
//            triple =
//                BinaryInstruction.knowledgeForMultiplication(
//                    newState,
//                    relations,
//                    idRef,
//                    ref1,
//                    ref2,
//                    type,
//                    val1,
//                    val2,
//                    result,
//                    changeInformation,
//                    posOverflow,
//                    negOverflow
//                );
//            if (triple.z != null) {
//                return new Pair<LLVMAbstractState, LLVMHeuristicVariable>(triple.x, triple.z);
//            }
//            break;
//        case SDIV:
//            triple =
//                swapped ?
//                    BinaryInstruction.knowledgeForDivision(newState, relations, idRef, ref2, ref1, val1, result) :
//                        BinaryInstruction.knowledgeForDivision(newState, relations, idRef, ref1, ref2, val2, result);
//            if (triple.z != null) {
//                return new Pair<LLVMAbstractState, LLVMHeuristicVariable>(triple.x, triple.z);
//            }
//            break;
//        case SREM:
//            triple =
//                swapped ?
//                    BinaryInstruction.knowledgeForRemainder(
//                        newState,
//                        relations,
//                        idRef,
//                        ref2,
//                        ref1,
//                        val2,
//                        val1,
//                        result
//                    ) :
//                        BinaryInstruction.knowledgeForRemainder(
//                            newState,
//                            relations,
//                            idRef,
//                            ref1,
//                            ref2,
//                            val1,
//                            val2,
//                            result
//                        );
//            if (triple.z != null) {
//                return new Pair<LLVMAbstractState, LLVMHeuristicVariable>(triple.x, triple.z);
//            }
//            break;
//        case AND:
//            triple =
//                BinaryInstruction.knowledgeForLogicalAnd(
//                    newState,
//                    relations,
//                    idRef,
//                    ref1,
//                    ref2,
//                    val1,
//                    val2,
//                    result
//                );
//            if (triple.z != null) {
//                return new Pair<LLVMAbstractState, LLVMHeuristicVariable>(triple.x, triple.z);
//            }
//            break;
//        case SHL:
//            triple =
//                swapped ?
//                    BinaryInstruction.knowledgeForLeftshift(
//                        newState,
//                        relations,
//                        idRef,
//                        ref2,
//                        ref1,
//                        val2,
//                        val1,
//                        result,
//                        changeInformation
//                    ) :
//                        BinaryInstruction.knowledgeForLeftshift(
//                            newState,
//                            relations,
//                            idRef,
//                            ref1,
//                            ref2,
//                            val1,
//                            val2,
//                            result,
//                            changeInformation
//                        );
//            if (triple.z != null) {
//                return new Pair<LLVMAbstractState, LLVMHeuristicVariable>(triple.x, triple.z);
//            }
//            break;
//        case ASHR:
//            triple =
//                swapped ?
//                    BinaryInstruction.knowledgeForArithmeticRightshift(
//                        newState,
//                        relations,
//                        idRef,
//                        ref2,
//                        ref1,
//                        val1,
//                        result
//                    ) :
//                        BinaryInstruction.knowledgeForArithmeticRightshift(
//                            newState,
//                            relations,
//                            idRef,
//                            ref1,
//                            ref2,
//                            val2,
//                            result
//                        );
//            if (triple.z != null) {
//                return new Pair<LLVMAbstractState, LLVMHeuristicVariable>(triple.x, triple.z);
//            }
//            break;
//        case LSHR:
//            triple =
//                swapped ?
//                    BinaryInstruction.knowledgeForLogicalRightshift(
//                        newState,
//                        relations,
//                        idRef,
//                        ref2,
//                        ref1,
//                        val2,
//                        val1,
//                        result
//                    ) :
//                        BinaryInstruction.knowledgeForLogicalRightshift(
//                            newState,
//                            relations,
//                            idRef,
//                            ref1,
//                            ref2,
//                            val1,
//                            val2,
//                            result
//                        );
//            if (triple.z != null) {
//                return new Pair<LLVMAbstractState, LLVMHeuristicVariable>(triple.x, triple.z);
//            }
//            break;
//        default:
//            // we could not find out anything more
//            triple =
//                new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//                    newState.setValue(idRef, result),
//                    Collections.<LLVMRelation>emptySet(),
//                    null
//                );
//        }
//        return this.finalKnowledge(
//            relations,
//            idRef,
//            triple,
//            new Pair<LLVMHeuristicVariable, LLVMHeuristicVariable>(ref1, ref2),
//            new Pair<AbstractBoundedInt, AbstractBoundedInt>(val1, val2),
//            changeInformation,
//            params
//        );
//    }
//
//   /**
//    * Adds the strongest greater relation between one and the specified reference or the strongest less relation
//    * between -one and the specified reference which can be inferred from the value of the reference respectively to
//    * the state change information.
//    * @param ref A reference.
//    * @param val The corresponding value.
//    * @param changeInformation The state change information.
//    */
//   private static void addMultInfo(
//       LLVMHeuristicVariable ref,
//       AbstractBoundedInt val,
//       Collection<LLVMRelation> changeInformation
//   ) {
//       if (val.isBiggerOne()) {
//           changeInformation.add(new LLVMRelation(HeuristicRelationType.LT, LLVMHeuristicTermFactory.ONE, ref));
//       } else if (val.isPositive()) {
//           changeInformation.add(new LLVMRelation(HeuristicRelationType.LT, LLVMHeuristicTermFactory.ZERO, ref));
//       } else if (val.isNonNegative()) {
//           changeInformation.add(new LLVMRelation(HeuristicRelationType.LE, LLVMHeuristicTermFactory.ZERO, ref));
//       } else if (val.isSmallerMinusOne()) {
//           changeInformation.add(
//               new LLVMRelation(HeuristicRelationType.LT, ref, LLVMHeuristicTermFactory.NEGONE)
//           );
//       } else if (val.isNegative()) {
//           changeInformation.add(new LLVMRelation(HeuristicRelationType.LT, ref, LLVMHeuristicTermFactory.ZERO));
//       } else if (val.isNonPositive()) {
//           changeInformation.add(new LLVMRelation(HeuristicRelationType.LE, ref, LLVMHeuristicTermFactory.ZERO));
//       }
//   }
//
//   /**
//    * @param newState The state currently in construction.
//    * @param newRels The relations to add.
//    * @param relationInfo Which relations are really added?
//    * @param params Strategy parameters.
//    * @return The resulting AbstractState.
//    */
//   private static LLVMAbstractState addRelations(
//       LLVMAbstractState newState,
//       Set<LLVMRelation> newRels,
//       Collection<LLVMStateChangeInformation> relationInfo,
//       LLVMParameters params
//   ) {
//       Pair<LLVMAbstractState, IntegerRelationSet> res = newState.addRelations(newRels, params);
//       relationInfo.addAll(res.y);
//       return res.x;
//   }
//
//   /**
//    * Adds the strongest relation between zero and the specified reference to the state change information which can
//    * be inferred from the value of the reference.
//    * @param ref A reference.
//    * @param val The corresponding value.
//    * @param changeInformation The state change information.
//    */
//   private static void addSignInfo(
//       LLVMHeuristicVariable ref,
//       AbstractBoundedInt val,
//       Collection<LLVMRelation> changeInformation
//   ) {
//       if (val.isPositive()) {
//           changeInformation.add(new LLVMRelation(HeuristicRelationType.LT, LLVMHeuristicTermFactory.ZERO, ref));
//       } else if (val.isNonNegative()) {
//           changeInformation.add(new LLVMRelation(HeuristicRelationType.LE, LLVMHeuristicTermFactory.ZERO, ref));
//       } else if (val.isNegative()) {
//           changeInformation.add(new LLVMRelation(HeuristicRelationType.LT, ref, LLVMHeuristicTermFactory.ZERO));
//       } else if (val.isNonPositive()) {
//           changeInformation.add(new LLVMRelation(HeuristicRelationType.LE, ref, LLVMHeuristicTermFactory.ZERO));
//       }
//   }
//
//   /**
//    * @param ref1 The first operand reference.
//    * @param ref2 The second operand reference.
//    * @param val1 The value of the first operand reference.
//    * @param val2 The value of the second operand reference.
//    * @param changeInformation The state change information.
//    */
//   private static void changeInfoForMultiplication(
//       LLVMHeuristicVariable ref1,
//       LLVMHeuristicVariable ref2,
//       AbstractBoundedInt val1,
//       AbstractBoundedInt val2,
//       Collection<LLVMRelation> changeInformation
//   ) {
//       if (val1.isBiggerOne()) {
//           changeInformation.add(
//               new LLVMRelation(HeuristicRelationType.LT, LLVMHeuristicTermFactory.ONE, ref1)
//           );
//       } else if (val1.isPositive()) {
//           changeInformation.add(
//               new LLVMRelation(HeuristicRelationType.LT, LLVMHeuristicTermFactory.ZERO, ref1)
//           );
//       } else if (val1.isNonNegative()) {
//           changeInformation.add(
//               new LLVMRelation(HeuristicRelationType.LE, LLVMHeuristicTermFactory.ZERO, ref1)
//           );
//       } else if (val1.isSmallerMinusOne()) {
//           changeInformation.add(
//               new LLVMRelation(HeuristicRelationType.LT, ref1, LLVMHeuristicTermFactory.NEGONE)
//           );
//       } else if (val1.isNegative()) {
//           changeInformation.add(
//               new LLVMRelation(HeuristicRelationType.LT, ref1, LLVMHeuristicTermFactory.ZERO)
//           );
//       } else if (val1.isNonPositive()) {
//           changeInformation.add(
//               new LLVMRelation(HeuristicRelationType.LE, ref1, LLVMHeuristicTermFactory.ZERO)
//           );
//       }
//       if (!val2.isLiteral()) {
//           if (val2.isBiggerOne()) {
//               changeInformation.add(
//                   new LLVMRelation(HeuristicRelationType.LT, LLVMHeuristicTermFactory.ONE, ref2)
//               );
//           } else if (val2.isPositive()) {
//               changeInformation.add(
//                   new LLVMRelation(HeuristicRelationType.LT, LLVMHeuristicTermFactory.ZERO, ref2)
//               );
//           } else if (val2.isNonNegative()) {
//               changeInformation.add(
//                   new LLVMRelation(HeuristicRelationType.LE, LLVMHeuristicTermFactory.ZERO, ref2)
//               );
//           } else if (val2.isSmallerMinusOne()) {
//               changeInformation.add(
//                   new LLVMRelation(HeuristicRelationType.LT, ref2, LLVMHeuristicTermFactory.NEGONE)
//               );
//           } else if (val2.isNegative()) {
//               changeInformation.add(
//                   new LLVMRelation(HeuristicRelationType.LT, ref2, LLVMHeuristicTermFactory.ZERO)
//               );
//           } else if (val2.isNonPositive()) {
//               changeInformation.add(
//                   new LLVMRelation(HeuristicRelationType.LE, ref2, LLVMHeuristicTermFactory.ZERO)
//               );
//           }
//       }
//   }
//
//   /**
//    * @param state The base state.
//    * @param relations The known relations.
//    * @param addRef The reference to the result.
//    * @param ref1 The first operand reference.
//    * @param ref2 The second operand reference.
//    * @param type The type of the references.
//    * @param val2 The value of the second operand reference.
//    * @param result The result of the addition.
//    * @param posOverflow NO if we can exclude positive overflows, YES if we have a positive overflow for sure.
//    * @param negOverflow NO if we can exclude negative overflows, YES if we have a negative overflow for sure.
//    * @return The resulting state, the relations to add, and an old reference representing the resulting value if we
//    *         can find such a reference - otherwise the third component is null. Note that the returned set of
//    *         relations might be immutable!
//    */
//   private static Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable> knowledgeForAddition(
//       LLVMAbstractState state,
//       IntegerRelationSet relations,
//       LLVMHeuristicVariable addRef,
//       LLVMHeuristicVariable ref1,
//       LLVMHeuristicVariable ref2,
//       BasicType type,
//       AbstractBoundedInt val2,
//       LLVMValue result,
//       YNM posOverflow,
//       YNM negOverflow
//   ) {
//       if (val2.isZero()) {
//           return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//               state,
//               Collections.<LLVMRelation>emptySet(),
//               ref1
//           );
//       }
//       LLVMRelation newRel;
//       if (posOverflow == YNM.NO && negOverflow == YNM.NO) {
//           newRel = LLVMRelationFactory.createAdditionRelation(addRef, ref1, ref2);
//       } else if (posOverflow == YNM.YES) {
//           newRel =
//               LLVMRelationFactory.createAdditionRelation(
//                   addRef,
//                   termFactory.operation(
//                       ArithmeticOperationType.ADD,
//                       new LLVMHeuristicConstRef(BigInteger.valueOf(2).pow(type.size()).negate()),
//                       ref1
//                   ),
//                   ref2
//               );
//       } else if (negOverflow == YNM.YES) {
//           newRel =
//               LLVMRelationFactory.createAdditionRelation(
//                   addRef,
//                   termFactory.operation(
//                       ArithmeticOperationType.ADD,
//                       new LLVMHeuristicConstRef(BigInteger.valueOf(2).pow(type.size())),
//                       ref1
//                   ),
//                   ref2
//               );
//       } else {
//           newRel = LLVMRelationFactory.createOverflowSafeRelation(ArithmeticOperationType.ADD, addRef, ref1, ref2, type);
//       }
//       LLVMHeuristicVariable oldRef =
//           LLVMHeuristicExpressionUtils.findReferenceForExpression(
//               state.getValues(),
//               relations,
//               newRel.getEqualExpression(addRef)
//           );
//       if (oldRef != null) {
//           return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//               state,
////               Collections.<Relation>singleton(Relation.createAdditionRelation(oldRef, ref1, ref2)),
//               Collections.<LLVMRelation>emptySet(),
//               oldRef
//           );
//       }
//       return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//           state.setValue(addRef, result),
//           Collections.<LLVMRelation>singleton(newRel),
//           null
//       );
//   }
//
//   /**
//    * @param state The base state.
//    * @param relations The known relations.
//    * @param divRef The reference to the result.
//    * @param ref1 The first operand reference.
//    * @param ref2 The second operand reference.
//    * @param val2 The value of the second operand reference.
//    * @param result The result of the division.
//    * @return The resulting state, the relations to add, and an old reference representing the resulting value if we
//    *         can find such a reference - otherwise the third component is null. Note that the returned set of
//    *         relations might be immutable!
//    */
//   private static Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable> knowledgeForDivision(
//       LLVMAbstractState state,
//       IntegerRelationSet relations,
//       LLVMHeuristicVariable divRef,
//       LLVMHeuristicVariable ref1,
//       LLVMHeuristicVariable ref2,
//       AbstractBoundedInt val2,
//       LLVMValue result
//   ) {
//       if (val2.isOne()) {
//           return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//               state,
//               Collections.<LLVMRelation>emptySet(),
//               ref1
//           );
//       }
//       LLVMRelation newRel = LLVMRelationFactory.createDivisionRelation(divRef, ref1, ref2);
//       LLVMHeuristicVariable oldRef =
//           LLVMHeuristicExpressionUtils.findReferenceForExpression(
//               state.getValues(),
//               relations,
//               newRel.getEqualExpression(divRef)
//           );
//       if (oldRef != null) {
//           return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//               state,
////               Collections.<Relation>singleton(Relation.createDivisionRelation(oldRef, ref1, ref2)),
//               Collections.<LLVMRelation>emptySet(),
//               oldRef
//           );
//       }
//       return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//           state.setValue(divRef, result),
//           Collections.<LLVMRelation>singleton(newRel),
//           null
//       );
//   }
//
//   /**
//    * @param state The base state.
//    * @param relations The known relations.
//    * @param leftShiftRef The reference to the result.
//    * @param ref1 The first operand reference.
//    * @param ref2 The second operand reference.
//    * @param val1 The value of the first operand reference.
//    * @param val2 The value of the first operand reference.
//    * @param result The result of the leftshift.
//    * @param changeInformation The state change information.
//    * @return The resulting state, the relations to add, and an old reference representing the resulting value if we
//    *         can find such a reference - otherwise the third component is null. Note that the returned set of
//    *         relations might be immutable!
//    */
//   private static Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable> knowledgeForLeftshift(
//       LLVMAbstractState state,
//       IntegerRelationSet relations,
//       LLVMHeuristicVariable leftShiftRef,
//       LLVMHeuristicVariable ref1,
//       LLVMHeuristicVariable ref2,
//       AbstractBoundedInt val1,
//       AbstractBoundedInt val2,
//       LLVMValue result,
//       Collection<LLVMRelation> changeInformation
//   ) {
//       if (val2.isZero()) {
//           return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//               state,
//               Collections.<LLVMRelation>emptySet(),
//               ref1
//           );
//       }
//       LLVMRelation newRel = LLVMRelationFactory.createLeftshiftRelation(leftShiftRef, ref1, ref2);
//       LLVMHeuristicVariable oldRef =
//           LLVMHeuristicExpressionUtils.findReferenceForExpression(
//               state.getValues(),
//               relations,
//               newRel.getEqualExpression(leftShiftRef)
//           );
//       if (oldRef != null) {
//           return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//               state,
////               Collections.<Relation>singleton(Relation.createLeftshiftRelation(oldRef, ref1, ref2)),
//               Collections.<LLVMRelation>emptySet(),
//               oldRef
//           );
//       }
//       BinaryInstruction.changeInfoForMultiplication(ref1, ref2, val1, val2, changeInformation);
//       return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//           state.setValue(leftShiftRef, result),
//           Collections.<LLVMRelation>singleton(newRel),
//           null
//       );
//   }
//
//   /**
//    * @param state The base state.
//    * @param relations The known relations.
//    * @param andRef The reference to the result.
//    * @param ref1 The first operand reference.
//    * @param ref2 The second operand reference.
//    * @param val1 The value of the first operand reference.
//    * @param val2 The value of the second operand reference.
//    * @param result The result of the logical conjunction.
//    * @return The resulting state, the relations to add, and an old reference representing the resulting value if we
//    *         can find such a reference - otherwise the third component is null. Note that the returned set of
//    *         relations might be immutable!
//    */
//   private static Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable> knowledgeForLogicalAnd(
//       LLVMAbstractState state,
//       IntegerRelationSet relations,
//       LLVMHeuristicVariable andRef,
//       LLVMHeuristicVariable ref1,
//       LLVMHeuristicVariable ref2,
//       AbstractBoundedInt val1,
//       AbstractBoundedInt val2,
//       LLVMValue result
//   ) {
//       LLVMRelation newRel1;
//       LLVMRelation newRel2;
//       Set<LLVMRelation> rels = new HashSet<LLVMRelation>();
//       if (val1.isNonNegative()) {
//           newRel1 = LLVMRelationFactory.createRelation(andRef, IntegerRelationType.LE, ref1);
//           rels.add(newRel1);
//       }
//       if (val2.isNonNegative()) {
//           newRel2 = LLVMRelationFactory.createRelation(andRef, IntegerRelationType.LE, ref2);
//           rels.add(newRel2);
//       }
//       return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//           state.setValue(andRef, result),
//           rels,
//           null
//       );
//   }
//
//   /**
//    * @param state The base state.
//    * @param relations The known relations.
//    * @param logicalRightShiftRef The reference to the result.
//    * @param ref1 The first operand reference.
//    * @param ref2 The second operand reference.
//    * @param val1 The value of the first operand reference.
//    * @param val2 The value of the second operand reference.
//    * @param result The result of the logical right shift.
//    * @return If val1 is nonnegative, we do the same as for arithmetic right shifts.
//    */
//   private static Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable> knowledgeForLogicalRightshift(
//       LLVMAbstractState state,
//       IntegerRelationSet relations,
//       LLVMHeuristicVariable logicalRightShiftRef,
//       LLVMHeuristicVariable ref1,
//       LLVMHeuristicVariable ref2,
//       AbstractBoundedInt val1,
//       AbstractBoundedInt val2,
//       LLVMValue result
//   ) {
//       if (val2.isZero()) {
//           return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//               state,
//               Collections.<LLVMRelation>emptySet(),
//               ref1
//           );
//       }
//       if (!val1.isNonNegative()) {
//           return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//               state.setValue(logicalRightShiftRef, result),
//               Collections.<LLVMRelation>emptySet(),
//               null
//           );
//       }
//       LLVMRelation newRel = LLVMRelationFactory.createArithmeticRightshiftRelation(logicalRightShiftRef, ref1, ref2);
//       LLVMHeuristicVariable oldRef =
//           LLVMHeuristicExpressionUtils.findReferenceForExpression(
//               state.getValues(),
//               relations,
//               newRel.getEqualExpression(logicalRightShiftRef)
//           );
//       if (oldRef != null) {
//           return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//               state,
////               Collections.<Relation>singleton(Relation.createLogicalRightshiftRelation(oldRef, ref1, ref2)),
//               Collections.<LLVMRelation>emptySet(),
//               oldRef
//           );
//       }
//       return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//           state.setValue(logicalRightShiftRef, result),
//           Collections.<LLVMRelation>singleton(newRel),
//           null
//       );
//   }
//
//   /**
//    * @param state The base state.
//    * @param relations The known relations.
//    * @param arithmeticRightShiftRef The reference to the result.
//    * @param ref1 The first operand reference.
//    * @param ref2 The second operand reference.
//    * @param val2 The value of the second operand reference.
//    * @param result The result of the arithmetic right shift.
//    * @return The resulting state, the relations to add, and an old reference representing the resulting value if we
//    *         can find such a reference - otherwise the third component is null. Note that the returned set of
//    *         relations might be immutable!
//    */
//   private static Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable> knowledgeForArithmeticRightshift(
//       LLVMAbstractState state,
//       IntegerRelationSet relations,
//       LLVMHeuristicVariable arithmeticRightShiftRef,
//       LLVMHeuristicVariable ref1,
//       LLVMHeuristicVariable ref2,
//       AbstractBoundedInt val2,
//       LLVMValue result
//   ) {
//       if (val2.isZero()) {
//           return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//               state,
//               Collections.<LLVMRelation>emptySet(),
//               ref1
//           );
//       }
//       LLVMRelation newRel = LLVMRelationFactory.createArithmeticRightshiftRelation(arithmeticRightShiftRef, ref1, ref2);
//       LLVMHeuristicVariable oldRef =
//           LLVMHeuristicExpressionUtils.findReferenceForExpression(
//               state.getValues(),
//               relations,
//               newRel.getEqualExpression(arithmeticRightShiftRef)
//           );
//       if (oldRef != null) {
//           return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//               state,
////               Collections.<Relation>singleton(Relation.createLogicalRightshiftRelation(oldRef, ref1, ref2)),
//               Collections.<LLVMRelation>emptySet(),
//               oldRef
//           );
//       }
//       return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//           state.setValue(arithmeticRightShiftRef, result),
//           Collections.<LLVMRelation>singleton(newRel),
//           null
//       );
//   }
//
//   /**
//    * @param state The base state.
//    * @param relations The known relations.
//    * @param mulRef The reference to the result.
//    * @param ref1 The first operand reference.
//    * @param ref2 The second operand reference.
//    * @param type The type of the references.
//    * @param val1 The value of the first operand reference.
//    * @param val2 The value of the first operand reference.
//    * @param result The result of the multiplication.
//    * @param changeInformation The state change information.
//    * @param posOverflow NO if we can exclude positive overflows, YES if we have a positive overflow for sure.
//    * @param negOverflow NO if we can exclude negative overflows, YES if we have a negative overflow for sure.
//    * @return The resulting state, the relations to add, and an old reference representing the resulting value if we
//    *         can find such a reference - otherwise the third component is null. Note that the returned set of
//    *         relations might be immutable!
//    */
//   private static Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable> knowledgeForMultiplication(
//       LLVMAbstractState state,
//       IntegerRelationSet relations,
//       LLVMHeuristicVariable mulRef,
//       LLVMHeuristicVariable ref1,
//       LLVMHeuristicVariable ref2,
//       BasicType type,
//       AbstractBoundedInt val1,
//       AbstractBoundedInt val2,
//       LLVMValue result,
//       Collection<LLVMRelation> changeInformation,
//       YNM posOverflow,
//       YNM negOverflow
//   ) {
//       if (Globals.useAssertions) {
//           assert (!val1.isZero()) : "The result must be constant and we should not reach this point!";
//           assert (!val2.isZero()) : "The result must be constant and we should not reach this point!";
//       }
//       if (val2.isOne()) {
//           return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//               state,
//               Collections.<LLVMRelation>emptySet(),
//               ref1
//           );
//       }
//       LLVMRelation newRel;
//       // special cases: no overflow occurs or a simple (!) overflow definitely occurs (for multiplication with 2)
//       if (posOverflow == YNM.NO && negOverflow == YNM.NO) {
//           newRel = LLVMRelationFactory.createMultiplicationRelation(mulRef, ref1, ref2);
//       } else if (posOverflow == YNM.YES
//           && ((val1.isIntLiteral() && val1.getIntLiteralValue().equals(BigInteger.valueOf(2)))
//               || (val2.isIntLiteral() && val2.getIntLiteralValue().equals(BigInteger.valueOf(2))))) {
//           newRel = LLVMRelationFactory.createAdditionRelation(
//                   mulRef,
//                   termFactory.operation(
//                       ArithmeticOperationType.MUL,
//                       ref1,
//                       ref2
//                   ),
//                   new LLVMHeuristicConstRef(BigInteger.valueOf(2).pow(type.size()).negate())
//               );
//       } else if (negOverflow == YNM.YES
//           && ((val1.isIntLiteral() && val1.getIntLiteralValue().equals(BigInteger.valueOf(2)))
//               || (val2.isIntLiteral() && val2.getIntLiteralValue().equals(BigInteger.valueOf(2))))) {
//           newRel = LLVMRelationFactory.createAdditionRelation(
//               mulRef,
//               termFactory.operation(
//                   ArithmeticOperationType.MUL,
//                   ref1,
//                   ref2
//               ),
//               new LLVMHeuristicConstRef(BigInteger.valueOf(2).pow(type.size()))
//           );
//       } else {
//           newRel = LLVMRelationFactory.createOverflowSafeRelation(ArithmeticOperationType.MUL, mulRef, ref1, ref2, type);
//       }
//       LLVMHeuristicVariable oldRef =
//           LLVMHeuristicExpressionUtils.findReferenceForExpression(
//               state.getValues(),
//               relations,
//               newRel.getEqualExpression(mulRef)
//           );
//       if (oldRef != null) {
//           return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//               state,
////               Collections.<Relation>singleton(Relation.createMultiplicationRelation(oldRef, ref1, ref2)),
//               Collections.<LLVMRelation>emptySet(),
//               oldRef
//           );
//       }
//       BinaryInstruction.changeInfoForMultiplication(ref1, ref2, val1, val2, changeInformation);
//       return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//           state.setValue(mulRef, result),
//           Collections.<LLVMRelation>singleton(newRel),
//           null
//       );
//   }
//
//   /**
//    * @param state The base state.
//    * @param relations The known relations.
//    * @param remRef The reference to the result.
//    * @param ref1 The first operand reference.
//    * @param ref2 The second operand reference.
//    * @param val1 The value of the first operand reference.
//    * @param val2 The value of the first operand reference.
//    * @param result The result of the remainder calculation.
//    * @return The resulting state, the relations to add, and an old reference representing the resulting value if we
//    *         can find such a reference - otherwise the third component is null. Note that the returned set of
//    *         relations might be immutable!
//    */
//   private static Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable> knowledgeForRemainder(
//       LLVMAbstractState state,
//       IntegerRelationSet relations,
//       LLVMHeuristicVariable remRef,
//       LLVMHeuristicVariable ref1,
//       LLVMHeuristicVariable ref2,
//       AbstractBoundedInt val1,
//       AbstractBoundedInt val2,
//       LLVMValue result
//   ) {
//       if (val2.getLower().compareTo(val1.getUpper()) > 0) {
//           return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//               state,
//               Collections.<LLVMRelation>emptySet(),
//               ref1
//           );
//       }
//       LLVMRelation newRel = LLVMRelationFactory.createRemainderRelation(remRef, ref1, ref2);
//       LLVMHeuristicVariable oldRef =
//           LLVMHeuristicExpressionUtils.findReferenceForExpression(
//               state.getValues(),
//               relations,
//               newRel.getEqualExpression(remRef)
//           );
//       if (oldRef != null) {
//           return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//               state,
////               Collections.<Relation>singleton(Relation.createRemainderRelation(oldRef, ref1, ref2)),
//               Collections.<LLVMRelation>emptySet(),
//               oldRef
//           );
//       }
//       return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//           state.setValue(remRef, result),
//           Collections.<LLVMRelation>singleton(newRel),
//           null
//       );
//   }
//
//   /**
//    * @param state The base state.
//    * @param relations The known relations.
//    * @param subRef The reference to the result.
//    * @param ref1 The first operand reference.
//    * @param ref2 The second operand reference.
//    * @param type The type of the references.
//    * @param val2 The value of the second operand reference.
//    * @param result The result of the subtraction.
//    * @param posOverflow NO if we can exclude positive overflows, YES if we have a positive overflow for sure.
//    * @param negOverflow NO if we can exclude negative overflows, YES if we have a negative overflow for sure.
//    * @param params Strategy parameters.
//    * @return The resulting state, the relations to add, and an old reference representing the resulting value if we
//    *         can find such a reference - otherwise the third component is null. Note that the returned set of
//    *         relations might be immutable!
//    */
//   private static Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable> knowledgeForSubtraction(
//       LLVMAbstractState state,
//       IntegerRelationSet relations,
//       LLVMHeuristicVariable subRef,
//       LLVMHeuristicVariable ref1,
//       LLVMHeuristicVariable ref2,
//       BasicType type,
//       AbstractBoundedInt val2,
//       IntervalBoundedInt result,
//       YNM posOverflow,
//       YNM negOverflow,
//       LLVMParameters params
//   ) {
//       // we have subRef = ref1 - ref2
//       if (val2.isZero()) {
//           return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//               state,
//               Collections.<LLVMRelation>emptySet(),
//               ref1
//           );
//       }
//       LLVMRelation newRel;
//       if (posOverflow == YNM.NO && negOverflow == YNM.NO) {
//           newRel = LLVMRelationFactory.createSubtractionRelation(subRef, ref1, ref2);
//       } else if (posOverflow == YNM.YES) {
//           newRel =
//               LLVMRelationFactory.createSubtractionRelation(
//                   subRef,
//                   termFactory.operation(
//                       ArithmeticOperationType.ADD,
//                       new LLVMHeuristicConstRef(BigInteger.valueOf(2).pow(type.size()).negate()),
//                       ref1
//                   ),
//                   ref2
//               );
//       } else if (negOverflow == YNM.YES) {
//           newRel =
//               LLVMRelationFactory.createSubtractionRelation(
//                   subRef,
//                   termFactory.operation(
//                       ArithmeticOperationType.ADD,
//                       new LLVMHeuristicConstRef(BigInteger.valueOf(2).pow(type.size())),
//                       ref1
//                   ),
//                   ref2
//               );
//       } else {
//           newRel = LLVMRelationFactory.createOverflowSafeRelation(ArithmeticOperationType.SUB, subRef, ref1, ref2, type);
//       }
//       LLVMHeuristicVariable oldRef =
//           LLVMHeuristicExpressionUtils.findReferenceForExpression(
//               state.getValues(),
//               relations,
//               newRel.getEqualExpression(subRef)
//           );
//       if (oldRef != null) {
//           return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//               state,
////               Collections.<Relation>singleton(Relation.createSubtractionRelation(oldRef, ref1, ref2)),
//               Collections.<LLVMRelation>emptySet(),
//               oldRef
//           );
//       }
//       final AbstractBoundedInt newValue;
//       if (!ref1.isConcrete() && !ref2.isConcrete()) {
//           Set<LLVMRelation> info = new LinkedHashSet<LLVMRelation>();
//           IntervalBoundedInt reduced = result;
//           for (LLVMRelation inequality : relations.getDirectedInequalities()) {
//               Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = inequality.getLhs().toLinear();
//               Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = inequality.getRhs().toLinear();
//               if (lhsLinear.x == null || rhsLinear.x == null) {
//                   continue;
//               }
//               if (ref2.equals(lhsLinear.x)) {
//                   if (
//                       !ref1.equals(rhsLinear.x)
//                       || lhsLinear.z.compareTo(rhsLinear.z) != 0
//                       || lhsLinear.z.compareTo(BigInteger.ZERO) <= 0
//                   ) {
//                       continue;
//                   }
//                   // z * ref2 + lhsLinear.y <= z * ref1 + rhsLinear.y with z > 0
//                   // implies (lhsLinear.y - rhsLinear.y) / z <= ref1 - ref2
//                   // z * ref2 + lhsLinear.y < z * ref1 + rhsLinear.y with z > 0
//                   // implies (lhsLinear.y - rhsLinear.y) / z + 1 <= ref1 - ref2
//                   BigInteger offset =
//                       lhsLinear.y.subtract(
//                           rhsLinear.y
//                       ).divide(
//                           lhsLinear.z
//                       ).add(
//                           inequality.getRelationType() == HeuristicRelationType.LT ? BigInteger.ONE : BigInteger.ZERO
//                       );
//                   AbstractBoundedInt next = reduced;
//                   if (posOverflow == YNM.NO && negOverflow == YNM.NO) {
//                       if (IntervalBound.create(offset).compareTo(reduced.getLower()) > 0) {
//                           info.add(new LLVMRelation(HeuristicRelationType.LE, new LLVMHeuristicConstRef(offset), subRef));
//                           next = reduced.setLower(IntervalBound.create(offset));
//                       }
//                   }
//                   if (next.isIntLiteral()) {
//                       return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//                           state,
//                           Collections.<LLVMRelation>emptySet(),
//                           new LLVMHeuristicConstRef(next.getIntLiteralValue())
//                       );
//                   }
//                   reduced = (IntervalBoundedInt)next;
//                   continue;
//               } else if (ref2.equals(rhsLinear.x)) {
//                   if (
//                       !ref1.equals(lhsLinear.x)
//                       || lhsLinear.z.compareTo(rhsLinear.z) != 0
//                       || lhsLinear.z.compareTo(BigInteger.ZERO) <= 0
//                   ) {
//                       continue;
//                   }
//                   // z * ref1 + lhsLinear.y <= z * ref2 + rhsLinear.y with z > 0
//                   // implies ref1 - ref2 <= (rhsLinear.y - lhsLinear.y) / z + 1
//                   // z * ref1 + lhsLinear.y < z * ref2 + rhsLinear.y with z > 0
//                   // implies ref1 - ref2 <= (rhsLinear.y - lhsLinear.y) / z
//                   BigInteger offset =
//                       rhsLinear.y.subtract(
//                           lhsLinear.y
//                       ).divide(
//                           lhsLinear.z
//                       ).add(
//                           inequality.getRelationType() == HeuristicRelationType.LT ? BigInteger.ZERO : BigInteger.ONE
//                       );
//                   AbstractBoundedInt next = reduced;
//                   if (posOverflow == YNM.NO && negOverflow == YNM.NO) {
//                       if (IntervalBound.create(offset).compareTo(reduced.getUpper()) < 0) {
//                           info.add(new LLVMRelation(HeuristicRelationType.LE, subRef, new LLVMHeuristicConstRef(offset)));
//                           next = reduced.setUpper(IntervalBound.create(offset));
//                       }
//                   }
//                   if (next.isIntLiteral()) {
//                       return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//                           state,
//                           Collections.<LLVMRelation>emptySet(),
//                           new LLVMHeuristicConstRef(next.getIntLiteralValue())
//                       );
//                   }
//                   reduced = (IntervalBoundedInt) next;
//                   continue;
//               }
//           }
//           if (!info.isEmpty()) {
//               info.add(newRel);
//               return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//                   state.setValue(subRef, reduced),
//                   info,
//                   null
//               );
//           }
//           switch (
//               IntegerUtils.truthValueOfRelation(state, ref1, IntegerRelationType.LT, ref2, true, params)
//           ) {
//               case YES:
//                   if (negOverflow == YNM.NO) {
//                       newValue = result.onlyNegative();
//                   } else {
//                       newValue = result;
//                   }
//                   break;
//               case NO:
//                   if (
//                       IntegerUtils.truthValueOfRelation(
//                           state,
//                           ref1,
//                           IntegerRelationType.GT,
//                           ref2,
//                           true,
//                           params
//                       ) == YNM.YES
//                   ) {
//                       if (posOverflow == YNM.NO) {
//                           newValue = result.onlyPositive();
//                       } else {
//                           newValue = result;
//                       }
//                   } else {
//                       if (posOverflow == YNM.NO) {
//                           newValue = result.onlyNonNegative();
//                       } else {
//                           newValue = result;
//                       }
//                   }
//                   break;
//               default:
//                   switch (
//                       IntegerUtils.truthValueOfRelation(
//                           state,
//                           ref1,
//                           IntegerRelationType.LE,
//                           ref2,
//                           true,
//                           params
//                       )
//                   ) {
//                       case YES:
//                           if (negOverflow == YNM.NO) {
//                               newValue = result.onlyNonPositive();
//                           } else {
//                               newValue = result;
//                           }
//                           break;
//                       case NO:
//                           if (posOverflow == YNM.NO) {
//                               newValue = result.onlyPositive();
//                           } else {
//                               newValue = result;
//                           }
//                           break;
//                       default:
//                           // we cannot infer anything
//                           newValue = result;
//                   }
//           }
//       } else {
//           newValue = result;
//       }
//       return new Triple<LLVMAbstractState, Set<LLVMRelation>, LLVMHeuristicVariable>(
//           state.setValue(subRef, newValue),
//           Collections.<LLVMRelation>singleton(newRel),
//           null
//       );
//   }

}
