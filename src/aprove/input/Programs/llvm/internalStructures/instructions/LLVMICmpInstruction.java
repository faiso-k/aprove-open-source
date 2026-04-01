package aprove.input.Programs.llvm.internalStructures.instructions;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Instruction for integer comparison.
 * @author Janine Repke, cryingshadow
 */
public class LLVMICmpInstruction extends LLVMAssignmentInstruction {

    /**
     * The code for the type of comparison, e.g., eq.
     */
    private final LLVMIntCmpOpType comparisonCode;

    /**
     * The first literal to be compared.
     */
    private final LLVMLiteral operand1Value;

    /**
     * The second literal to be compared.
     */
    private final LLVMLiteral operand2Value;

    /**
     * @param id The variable to assign the comparison result to.
     * @param code The code for the type of comparison.
     * @param value1 The first literal to be compared.
     * @param value2 The second literal to be compared.
     * @param debugLine The index of the line with debug information.
     */
    public LLVMICmpInstruction(
        LLVMVariableLiteral id,
        LLVMIntCmpOpType code,
        LLVMLiteral value1,
        LLVMLiteral value2,
        int debugLine
    ) {
        super(id, debugLine);
        if (Globals.useAssertions) {
            assert (value1.getType().equals(value2.getType())) : "The values must have the same type!";
        }
        this.comparisonCode = code;
        this.operand1Value = value1;
        this.operand2Value = value2;
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
        switch (this.comparisonCode) {
            case SLT:
            case ULT:
                return
                    new LLVMLiteralRelation(
                        IntegerRelationType.LT,
                        this.operand1Value,
                        this.operand2Value
                    );
            case SGT:
            case UGT:
                return
                    new LLVMLiteralRelation(
                        IntegerRelationType.LT,
                        this.operand2Value,
                        this.operand1Value
                    );
            case SLE:
            case ULE:
                return
                    new LLVMLiteralRelation(
                        IntegerRelationType.LE,
                        this.operand1Value,
                        this.operand2Value
                    );
            case SGE:
            case UGE:
                return
                    new LLVMLiteralRelation(
                        IntegerRelationType.LE,
                        this.operand2Value,
                        this.operand1Value
                    );
            case EQ:
                return
                    new LLVMLiteralRelation(
                            IntegerRelationType.EQ,
                            this.operand2Value,
                            this.operand1Value
                        );
            case NE:
                return
                    new LLVMLiteralRelation(
                            IntegerRelationType.NE,
                            this.operand2Value,
                            this.operand1Value
                        );
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
        final LLVMSimpleTerm left;
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
        final LLVMSimpleTerm right;
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
        IntegerRelationSet toAddTrue = new IntegerRelationSet();
        IntegerRelationSet toAddFalse = new IntegerRelationSet();
        switch (this.comparisonCode) {
            case ULT:
            case UGE:
            case UGT:
            case ULE:
                // unsigned cases: both arguments have to be non-negative
                toAddTrue.add(relationFactory.nonNegative(left));
                toAddTrue.add(relationFactory.nonNegative(right));
                toAddFalse.add(relationFactory.nonNegative(left));
                toAddFalse.add(relationFactory.nonNegative(right));
                // fall through
            case EQ:
            case NE:
            case SGT:
            case SGE:
            case SLE:
            case SLT:
                toAddTrue.add(relationFactory.createRelation(this.comparisonCode.getIntegerRelationType(), left, right));
                toAddFalse.add(
                    relationFactory.createRelation(this.comparisonCode.getIntegerRelationType().invert(), left, right)
                );
        }
        outer: for (Pair<IntegerRelationSet, List<String>> pair : conditions) {
            IntegerRelationSet relSet = new IntegerRelationSet();
            for (IntegerRelation rel : pair.x) {
                if (rel.getVariables().contains(id)) {
                    FunctionalIntegerExpression lhs = rel.getLhs();
                    FunctionalIntegerExpression rhs = rel.getRhs();
                    if (
                        !rel.isEquation()
                        || !(
                            (lhs.equals(id) && rhs instanceof LLVMConstant)
                            || (lhs instanceof LLVMConstant && rhs.equals(id))
                        )
                    ) {
                        continue outer;
                    }
                    final BigInteger constant;
                    if (lhs.equals(id)) {
                        constant = ((LLVMConstant)rhs).getIntegerValue();
                    } else {
                        constant = ((LLVMConstant)lhs).getIntegerValue();
                    }
                    if (Globals.useAssertions) {
                        assert (constant.compareTo(BigInteger.ZERO) == 0 || constant.compareTo(BigInteger.ONE) == 0) :
                            "Found non-boolean relation for boolean variable!";
                    }
                    if (constant.compareTo(BigInteger.ZERO) == 0) {
                        relSet.addAll(toAddFalse);
                    } else {
                        relSet.addAll(toAddTrue);
                    }
                } else {
                    relSet.add(rel);
                }
            }
            res.add(new Pair<IntegerRelationSet, List<String>>(relSet, pair.y));
        }
        return res;
    }

    /**
     * Evaluates the given state to a set of new state that are either more refined or in which the
     * The program counter has been incremented
     *
     * In particular the following cases may happen:
     * <ul>
     * <li> There is enough information available that the result of the comparison can be evaluated:
     *        A singleton set with a state that contains the comparison result and an incremented
     *        program counter is returned
     * <li> There is not enough information available to decide on the result of the comparison:
     *        A set containing two states is returned. Neither of the states increments the program
     *        counter but each states adds an additional relation that will provide enough information
     *        to be able to decide on the result of the comparison when is it called the next time
     * </ul>
     */
    @Override
    public Set<LLVMSymbolicEvaluationResult> evaluate(LLVMAbstractState state, int nodeNumber, boolean proveMemorySafety, LLVMMemoryChangeTracker memoryTracker, Abortion aborter)
    throws UndefinedBehaviorException {
        final LLVMRelationFactory relationFactory = state.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        final LLVMParameters params = state.getStrategyParamters();
        // determine the terms for the literals (each can be a variable or a constant)
        LLVMSimpleTerm ref1 = state.getSimpleTermForLiteral(this.operand1Value);
        LLVMSimpleTerm ref2 = state.getSimpleTermForLiteral(this.operand2Value);
        LLVMAbstractState newState = state;
        Pair<Boolean, ? extends LLVMAbstractState> check;
        if (params.analyzeC && this.operand1Value.getType().isPointerType()) {
            if (!(this.comparisonCode == LLVMIntCmpOpType.EQ || this.comparisonCode == LLVMIntCmpOpType.NE)) {
                newState = this.checkDirectedComparisonOfPointersInC(newState, ref1, ref2, nodeNumber, proveMemorySafety, aborter);
            } else {
                check = newState.checkRelation(relationFactory.equalTo(ref1, termFactory.zero()), aborter);
                newState = check.y;
                if (!check.x) {
                    check = newState.checkRelation(relationFactory.equalTo(ref2, termFactory.zero()), aborter);
                    newState = check.y;
                    if (!check.x) {
                        newState = this.checkDirectedComparisonOfPointersInC(newState, ref1, ref2, nodeNumber, proveMemorySafety, aborter);
                    }
                }
            }
        }
        if (newState.isPossiblyTrapValue(ref1) || newState.isPossiblyTrapValue(ref2)) {
            throw new TrapValueException(nodeNumber);
        }
        boolean greater = false;
        switch (this.comparisonCode) {
            case UGE:
            case UGT:
                greater = true;
            case ULE:
            case ULT:
                final LLVMRelation nonnegRel1 = relationFactory.nonNegative(ref1);
                final LLVMRelation negRel1 = relationFactory.negative(ref1);
                final LLVMRelation nonnegRel2 = relationFactory.nonNegative(ref2);
                final LLVMRelation negRel2 = relationFactory.negative(ref2);
                // use Booleans to minimize number of relation checks
                Boolean nonneg1 = null;
                Boolean nonneg2 = null;
                Boolean neg1 = null;
                Boolean neg2 = null;
                // for unbounded integers, both values have to be nonnegative
                if (!params.useBoundedIntegers) {
                    check = newState.checkRelation(nonnegRel1, aborter);
                    newState = check.y;
                    nonneg1 = check.x;
                    if (!nonneg1) {
                        throw
                            new UndefinedBehaviorException(
                                "Trying to do unsigned comparison for unbounded negative values (node "
                                + nodeNumber
                                + ")."
                            );
                    }
                    check = newState.checkRelation(nonnegRel2, aborter);
                    newState = check.y;
                    nonneg2 = check.x;
                    if (!nonneg2) {
                        throw
                            new UndefinedBehaviorException(
                                "Trying to do unsigned comparison for unbounded negative values (node "
                                + nodeNumber
                                + ")."
                            );
                    }
                }
                // Handle cases that one variable is negative and the other is positive
                if (nonneg1 == null) {
                    check = newState.checkRelation(nonnegRel1, aborter);
                    newState = check.y;
                    nonneg1 = check.x;
                }
                if (nonneg1) {
                    check = newState.checkRelation(negRel2, aborter);
                    newState = check.y;
                    neg2 = check.x;
                    if (neg2) {
                        // Handle ref1 >= 0 && ref2 < 0
                        // pos < neg in unsigned interpretation
                        if (greater) {
                            return this.falseResult(newState, aborter);
                        } else {
                            return this.trueResult(newState, aborter);
                        }
                    }
                }
                if (nonneg2 == null) {
                    check = newState.checkRelation(nonnegRel2, aborter);
                    newState = check.y;
                    nonneg2 = check.x;
                }
                if (nonneg2) {
                    check = newState.checkRelation(negRel1, aborter);
                    newState = check.y;
                    neg1 = check.x;
                    if (neg1) {
                        // Handle ref2 >= 0 && ref1 < 0
                        // neg > pos in unsigned interpretation
                        if (greater) {
                            return this.trueResult(newState, aborter);
                        } else {
                            return this.falseResult(newState, aborter);
                        }
                    }
                }
                if (!nonneg1 || !nonneg2) { // (ref1 < 0 or unknown) || (ref2 < 0 or unknown)
                    // Perform relation checks if this hasn't been done yet
                    if (neg1 == null) {
                        check = newState.checkRelation(negRel1, aborter);
                        newState = check.y;
                        neg1 = check.x;
                    }
                    if (neg2 == null) {
                        check = newState.checkRelation(negRel2, aborter);
                        newState = check.y;
                        neg2 = check.x;
                    }
                    if (!neg1 || !neg2) { // (ref1 >= 0 or unknown) && (ref2 >= 0 or unknown)
                        // Handle cases that the sign of one variable is known but the other is unknown
                        Set<LLVMSymbolicEvaluationResult> res = new LinkedHashSet<LLVMSymbolicEvaluationResult>();
                        if (!(nonneg1 || neg1)) {
                            // Handle: Value of ref1 is unknown
                            // Refine: ref1 is either negative or not
                            res.add(
                                new LLVMSymbolicEvaluationResult(
                                    newState.addRelation(nonnegRel1, aborter),
                                    Collections.singleton(nonnegRel1)
                                )
                            );
                            res.add(
                                new LLVMSymbolicEvaluationResult(
                                    newState.addRelation(negRel1, aborter),
                                    Collections.singleton(negRel1)
                                )
                            );
                        } else {
                            // Value of ref2 is unknown
                            if (Globals.useAssertions) {
                                assert (!(nonneg2 || neg2)) : "This case should have been caught before!";
                            }
                            // Refine: ref1 is either negative or not
                            res.add(
                                new LLVMSymbolicEvaluationResult(
                                    newState.addRelation(nonnegRel2, aborter),
                                    Collections.singleton(nonnegRel2)
                                )
                            );
                            res.add(
                                new LLVMSymbolicEvaluationResult(
                                    newState.addRelation(negRel2, aborter),
                                    Collections.singleton(negRel2)
                                )
                            );
                        }
                        return res;
                    }
                }
                //$FALL-THROUGH$ -- if both are (non-)negative, the normal comparisons can be executed
            case EQ:
            case NE:
            case SGT:
            case SGE:
            case SLE:
            case SLT:
                LLVMRelation trueRel =
                    relationFactory.createRelation(this.comparisonCode.getIntegerRelationType(), ref1, ref2);
                LLVMRelation falseRel =
                    relationFactory.createRelation(this.comparisonCode.getIntegerRelationType().invert(), ref1, ref2);
                check = newState.checkRelation(trueRel, aborter);
                newState = check.y;
                if (check.x) {
                    return this.trueResult(newState, aborter);
                } else {
                    check = newState.checkRelation(falseRel, aborter);
                    newState = check.y;
                    if (check.x) {
                        return this.falseResult(newState, aborter);
                    } else {
                        // Refine: Either the relationship holds or it doesn't
                        Set<LLVMSymbolicEvaluationResult> res = new LinkedHashSet<LLVMSymbolicEvaluationResult>();
                        if (!params.useBoundedIntegers) {
                            if (((this.operand1Value instanceof LLVMIntLiteral) && (
                                (((LLVMIntLiteral)this.operand1Value).getValueAsLong() >= 1073741820L) ||
                                (((LLVMIntLiteral)this.operand1Value).getValueAsLong() <= -1073741820L) ||
                                (((LLVMIntLiteral)this.operand1Value).getValueAsLong() == 268435455L) ||
                                (((LLVMIntLiteral)this.operand1Value).getValueAsLong() == -268435455L) ||
                                (((LLVMIntLiteral)this.operand1Value).getValueAsLong() == 1048575L) ||
                                (((LLVMIntLiteral)this.operand1Value).getValueAsLong() == -1048575L) ||
                                (((LLVMIntLiteral)this.operand1Value).getValueAsLong() == 524287L) ||
                                (((LLVMIntLiteral)this.operand1Value).getValueAsLong() == -524287L) ||
                                (((LLVMIntLiteral)this.operand1Value).getValueAsLong() == 65535L) ||
                                (((LLVMIntLiteral)this.operand1Value).getValueAsLong() == -65535L) ||
                                (((LLVMIntLiteral)this.operand1Value).getValueAsLong() == 65534L) ||
                                (((LLVMIntLiteral)this.operand1Value).getValueAsLong() == -65534L) ||
                                (((LLVMIntLiteral)this.operand1Value).getValueAsLong() == 46340L) ||
                                (((LLVMIntLiteral)this.operand1Value).getValueAsLong() == -46340L)))
                            || ((this.operand2Value instanceof LLVMIntLiteral) && (
                                (((LLVMIntLiteral)this.operand2Value).getValueAsLong() >= 1073741820L) ||
                                (((LLVMIntLiteral)this.operand2Value).getValueAsLong() <= -1073741820L) ||
                                (((LLVMIntLiteral)this.operand2Value).getValueAsLong() == 268435455L) ||
                                (((LLVMIntLiteral)this.operand2Value).getValueAsLong() == -268435455L) ||
                                (((LLVMIntLiteral)this.operand2Value).getValueAsLong() == 1048575L) ||
                                (((LLVMIntLiteral)this.operand2Value).getValueAsLong() == -1048575L) ||
                                (((LLVMIntLiteral)this.operand2Value).getValueAsLong() == 524287L) ||
                                (((LLVMIntLiteral)this.operand2Value).getValueAsLong() == -524287L) ||
                                (((LLVMIntLiteral)this.operand2Value).getValueAsLong() == 65535L) ||
                                (((LLVMIntLiteral)this.operand2Value).getValueAsLong() == -65535L) ||
                                (((LLVMIntLiteral)this.operand2Value).getValueAsLong() == 65534L) ||
                                (((LLVMIntLiteral)this.operand2Value).getValueAsLong() == -65534L) ||
                                (((LLVMIntLiteral)this.operand2Value).getValueAsLong() == 46340L) ||
                                (((LLVMIntLiteral)this.operand2Value).getValueAsLong() == -46340L)))
                            ) {
                                res.add(
                                    new LLVMSymbolicEvaluationResult(
                                        trueResult(newState, aborter).iterator().next().x,
                                        Collections.singleton(trueRel)
                                    )
                                );
                                res.add(
                                    new LLVMSymbolicEvaluationResult(
                                        falseResult(newState, aborter).iterator().next().x,
                                        Collections.singleton(falseRel)
                                    )
                                );
                                return res;
                            }
                        }
                        LLVMAbstractState newStateTrue;
                        LLVMAbstractState newStateFalse;
                        try {
                            if (this.comparisonCode.equals(LLVMIntCmpOpType.NE)) {
                                if (newState.checkRelation(trueRel.getLhs(), IntegerRelationType.LE, trueRel.getRhs(), aborter).x) {
                                    trueRel = relationFactory.lessThan(trueRel.getLhs(), trueRel.getRhs());
                                } else if (newState.checkRelation(trueRel.getLhs(), IntegerRelationType.GE, trueRel.getRhs(), aborter).x) {
                                    trueRel = relationFactory.lessThan(trueRel.getRhs(), trueRel.getLhs());
                                }
                            }
                            newStateTrue = newState.addRelation(trueRel, aborter);
                        } catch (InconsistentStateException e) {
                            newStateTrue = new LLVMInconsistentState(
                                    state.getModule(),
                                    state.getProgramPosition(),
                                    state.getStrategyParamters(),
                                    aborter
                                );
                        }
                        try {
                            newStateFalse = newState.addRelation(falseRel, aborter);
                        } catch (InconsistentStateException e) {
                            newStateFalse = new LLVMInconsistentState(
                                    state.getModule(),
                                    state.getProgramPosition(),
                                    state.getStrategyParamters(),
                                    aborter
                                );
                        }
                        for (LLVMMemoryRange memRange : newStateTrue.getMemory().keySet()) {
                            if (memRange instanceof LLVMMemoryRecursiveRange) {
                                continue;
                            }
                            if (memRange.getFromRef().equals(memRange.getToRef())) {
                                if (newStateTrue.getDereferencedAccess(memRange, aborter).x.equals(ref1)) {
                                    newStateTrue = newStateTrue.findAndCreateInvariantsForAccess(memRange, aborter);
                                }
                            }
                        }
                        for (LLVMMemoryRange memRange : newStateFalse.getMemory().keySet()) {
                            if (memRange instanceof LLVMMemoryRecursiveRange) {
                                continue;
                            }
                            if (memRange.getFromRef().equals(memRange.getToRef())) {
                                if (newStateFalse.getDereferencedAccess(memRange, aborter).x.equals(ref1)) {
                                    newStateFalse = newStateFalse.findAndCreateInvariantsForAccess(memRange, aborter);
                                }
                            }
                        }
                        res.add(
                            new LLVMSymbolicEvaluationResult(
                                newStateTrue,
                                Collections.singleton(trueRel)
                            )
                        );
                        res.add(
                            new LLVMSymbolicEvaluationResult(
                                newStateFalse,
                                Collections.singleton(falseRel)
                            )
                        );
                        return res;
                    }
                }
            default:
                // should not be reached
                throw new IllegalStateException(
                    "The comparison " + this.comparisonCode + " is not supported yet."
                );
        }
    }

    @Override
    public boolean isOverapproximation(LLVMAbstractState state, Abortion aborter) {
        return false;
    }

    /**
     * @param state The abstract LLVM state.
     * @param ref1 The first variable.
     * @param ref2 The second variable.
     * @param nodeNumber The current node number.
     * @return The specified state possibly updated during checks.
     * @throws UndefinedBehaviorException If we cannot prove that the specified variables point to the same allocation.
     */
    private LLVMAbstractState checkDirectedComparisonOfPointersInC(
        LLVMAbstractState state,
        LLVMSimpleTerm ref1,
        LLVMSimpleTerm ref2,
        int nodeNumber,
        boolean proveMemorySafety,
        Abortion aborter
    ) throws UndefinedBehaviorException {
        // directed comparison of two pointers is undefined behavior in C if both pointers do not point to
        // the same allocation or one cell thereafter
        // invariant here: both operands must have the same type
        Pair<LLVMAssociationIndex, LLVMAbstractState> index =
            state.getAssociatedAllocationIndex(
                ref1,
                this.operand1Value.getType().getThisAsPointerType(),
                true,
                aborter
            );
        LLVMAbstractState newState = index.y;
        if (proveMemorySafety && index.x == null) {
            throw
                new UndefinedBehaviorException(
                    "Invalid comparison of two pointers at node " + nodeNumber + "."
                );
        }
        Pair<LLVMAssociationIndex, LLVMAbstractState> otherIndex =
            newState.getAssociatedAllocationIndex(
                ref2,
                this.operand2Value.getType().getThisAsPointerType(),
                true,
                aborter
            );
        newState = otherIndex.y;
        if (proveMemorySafety && !index.x.equals(otherIndex.x)) {
            throw
                new UndefinedBehaviorException(
                    "Invalid comparison of two pointers at node " + nodeNumber + "."
                );
        }
        return newState;
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder res = new StringBuilder();
        res.append(eu.tttext(this.getIdentifier().toString()));
        res.append(eu.tttext(" = icmp "));
        res.append(eu.tttext(this.comparisonCode.toString()));
        res.append(eu.tttext(" "));
        res.append(eu.tttext(this.operand1Value.toString()));
        res.append(eu.tttext(" "));
        res.append(eu.tttext(this.operand2Value.toString()));
        return res.toString();
    }

    @Override
    public Set<String> getInterestingVariables() {
        Set<String> vars = new LinkedHashSet<>();
        // either operand may cause refinement, so we'll have to consider
        // both interesting
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
     * @return True iff this is a signed comparison (SGE, SGT, SLE, SLT).
     */
    public boolean isSigned() {
        return this.comparisonCode == LLVMIntCmpOpType.SGE
            || this.comparisonCode == LLVMIntCmpOpType.SGT
            || this.comparisonCode == LLVMIntCmpOpType.SLE
            || this.comparisonCode == LLVMIntCmpOpType.SLT;
    }

    /**
     * @return True iff this is neither a signed nor an unsigned comparison (EQ, NE).
     */
    public boolean isSignNeutral() {
        return this.comparisonCode == LLVMIntCmpOpType.EQ
            || this.comparisonCode == LLVMIntCmpOpType.NE;
    }

    /**
     * @return True iff this is a unsigned comparison (UGE, UGT, ULE, ULT).
     */
    public boolean isUnsigned() {
        return this.comparisonCode == LLVMIntCmpOpType.UGE
            || this.comparisonCode == LLVMIntCmpOpType.UGT
            || this.comparisonCode == LLVMIntCmpOpType.ULE
            || this.comparisonCode == LLVMIntCmpOpType.ULT;
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("IntCmpInstr ");
        strBuilder.append(" cmp: ");
        strBuilder.append(this.comparisonCode);
        strBuilder.append(" identifier: ");
        strBuilder.append(this.getIdentifier());
        strBuilder.append(" opType: ");
        strBuilder.append(this.operand1Value.getType());
        strBuilder.append(" op1Value: ");
        strBuilder.append(this.operand1Value);
        strBuilder.append(" op2Value: ");
        strBuilder.append(this.operand2Value);
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        StringBuilder res = new StringBuilder();
        res.append(this.getIdentifier().toDOTString());
        res.append(" = icmp ");
        res.append(this.comparisonCode);
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
        res.append(" = icmp ");
        res.append(this.comparisonCode);
        res.append(" ");
        res.append(this.operand1Value);
        res.append(" ");
        res.append(this.operand2Value);
        return res.toString();
    }

    @Override
    public String toLLVMIR() {
        StringBuilder res = new StringBuilder();
        res.append(this.getIdentifier().toLLVMIR());
        res.append(" = icmp ");
        res.append(this.comparisonCode);
        res.append(" ");
        res.append(this.operand1Value.getType().toLLVMIR());
        res.append(" ");
        res.append(this.operand1Value.toLLVMIR());
        res.append(", ");
        res.append(this.operand2Value.toLLVMIR());
        return res.toString();
    }

    /**
     * @param state The base state.
     * @return An abstract state emerging from the base state by setting the result variable for the comparison to
     *         false and incrementing the PC.
     */
    private Set<LLVMSymbolicEvaluationResult> falseResult(LLVMAbstractState state, Abortion aborter) {
        Set<LLVMRelation> newRels = new LinkedHashSet<>();
        LLVMAbstractState newState = state.assign(
                                                  this.getIdentifier().getName(),
                                                  state.getRelationFactory().getTermFactory().zero(),
                                                  LLVMIntType.I1,
                                                  newRels,
                                                  aborter
                );
        newState = newState.incrementPC();
        return Collections.singleton(new LLVMSymbolicEvaluationResult(newState, newRels));
    }

    /**
     * @param state The base state.
     * @return An abstract state emerging from the base state by setting the result variable for the comparison to
     *         true and incrementing the PC.
     */
    private Set<LLVMSymbolicEvaluationResult> trueResult(LLVMAbstractState state, Abortion aborter) {
        Set<LLVMRelation> newRels = new LinkedHashSet<>();
        LLVMAbstractState newState = state.assign(
                                                  this.getIdentifier().getName(),
                                                  state.getRelationFactory().getTermFactory().one(),
                                                  LLVMIntType.I1,
                                                  newRels,
                                                  aborter
                );
        newState = newState.incrementPC();

        return Collections.singleton(new LLVMSymbolicEvaluationResult(newState, newRels));
    }

}
