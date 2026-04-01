package aprove.input.Programs.llvm.internalStructures.instructions;

import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Selects one of two values based on a boolean value.
 * @author Janine Repke, CryingShadow
 */
public class LLVMSelectInstruction extends LLVMAssignmentInstruction {

    /**
     * The condition (type must be i1 or vector of i1).
     */
    private final LLVMLiteral conditionLiteral;

    /**
     * The first value.
     */
    private final LLVMLiteral value1Literal;

    /**
     * The second value.
     */
    private final LLVMLiteral value2Literal;

    /**
     * @param id The variable to assign the selected value to.
     * @param condition The condition (type must be i1 or vector of i1).
     * @param val1 The first value.
     * @param val2 The second value.
     * @param debugLine The index of the line with debug information.
     */
    public LLVMSelectInstruction(LLVMVariableLiteral id, LLVMLiteral condition, LLVMLiteral val1, LLVMLiteral val2, int debugLine) {
        super(id, debugLine);
        if (Globals.useAssertions) {
            assert (val1.getType().equals(val2.getType())) : "Both values must have the same type.";
        }
        this.conditionLiteral = condition;
        this.value1Literal = val1;
        this.value2Literal = val2;
    }

    @Override
    public final void collectVariables(Collection<String> vars) {
        LLVMInstruction.collectVariable(vars, this.conditionLiteral);
        LLVMInstruction.collectVariable(vars, this.value1Literal);
        LLVMInstruction.collectVariable(vars, this.value2Literal);
    }

    @Override
	public void collectUsedVariables(Collection<String> vars) {
    	collectVariables(vars);
    }

    @Override
    public LLVMLiteralRelation computeRelation() {
        return null;
    }

    @Override
    public Set<Pair<IntegerRelationSet, List<String>>> computeReturnConditions(
        LLVMProgramPosition pos,
        Set<Pair<IntegerRelationSet, List<String>>> conditions,
        LLVMParameters params
    ) {
        // TODO
        return new LinkedHashSet<Pair<IntegerRelationSet, List<String>>>();
    }

    @Override
    public Set<LLVMSymbolicEvaluationResult> evaluate(LLVMAbstractState state, int nodeNumber, boolean proveMemorySafety, LLVMMemoryChangeTracker memoryTracker, Abortion aborter)
    throws UndefinedBehaviorException {
        if (!this.conditionLiteral.getType().isBooleanType()) {
            throw new UnsupportedOperationException(
                "Can only handle boolean types. Vector types are not implemented yet."
            );
        }
        // determine value of condition
        LLVMSimpleTerm condValRef = state.getSimpleTermForLiteral(this.conditionLiteral);
        if (state.isPossiblyTrapValue(condValRef)) {
            throw new TrapValueException(nodeNumber);
        }
        final LLVMRelationFactory relationFactory = state.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        final LLVMRelation trueRel = relationFactory.equalTo(condValRef, termFactory.one());
        final LLVMRelation falseRel = relationFactory.equalTo(condValRef, termFactory.zero());
        final LLVMAbstractState incremented = state.incrementPC();
        final String varName = this.getIdentifier().getName();
        LLVMAbstractState newState = state;
        Pair<Boolean, ? extends LLVMAbstractState> check = newState.checkRelation(trueRel, aborter);
        newState = check.y;
        if (check.x) {
            Set<LLVMRelation> newRels = new LinkedHashSet<>();
            final LLVMAbstractState assignedState = incremented.assign(
                                                                       varName,
                                                                       incremented.getSimpleTermForLiteral(this.value1Literal),
                                                                       this.value1Literal.getType(),
                                                                       newRels,
                                                                       aborter
                                                                   );
            final LLVMSymbolicEvaluationResult evaluationResult = new LLVMSymbolicEvaluationResult(assignedState, newRels);
            return Collections.singleton(evaluationResult);
        } else {
            check = newState.checkRelation(falseRel, aborter);
            newState = check.y;
            if (check.x) {
                Set<LLVMRelation> newRels = new LinkedHashSet<>();
                final LLVMAbstractState assignedState = incremented.assign(
                                                                           varName,
                                                                           incremented.getSimpleTermForLiteral(this.value2Literal),
                                                                           this.value2Literal.getType(),
                                                                           newRels,
                                                                           aborter
                                                                       );
                final LLVMSymbolicEvaluationResult evaluationResult = new LLVMSymbolicEvaluationResult(assignedState, newRels);
                return Collections.singleton(evaluationResult);
            }
        }
        // else refine
        Set<LLVMSymbolicEvaluationResult> res = new LinkedHashSet<LLVMSymbolicEvaluationResult>();
        res.add(new LLVMSymbolicEvaluationResult(newState.addRelation(trueRel, aborter), Collections.singleton(trueRel)));
        res.add(new LLVMSymbolicEvaluationResult(newState.addRelation(falseRel, aborter), Collections.singleton(falseRel)));
        return res;
    }

    @Override
    public boolean isOverapproximation(LLVMAbstractState state, Abortion aborter) {
        return false;
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder res = new StringBuilder();
        res.append(eu.tttext(this.getIdentifier().toString()));
        res.append(eu.tttext(" = select "));
        res.append(eu.tttext(this.conditionLiteral.toString()));
        res.append(eu.tttext(", "));
        res.append(eu.tttext(this.value1Literal.toString()));
        res.append(eu.tttext(", "));
        res.append(eu.tttext(this.value2Literal.toString()));
        return res.toString();
    }

    /**
     * @return The condition.
     */
    public LLVMLiteral getConditionLiteral() {
        return this.conditionLiteral;
    }

    @Override
    public Set<String> getInterestingVariables() {
        Set<String> vars = new LinkedHashSet<>();
        // the condition variable is interesting because it causes refinement
        LLVMInstruction.collectVariable(vars, this.conditionLiteral);
        return vars;
    }

    /**
     * @return The first value.
     */
    public LLVMLiteral getValue1Literal() {
        return this.value1Literal;
    }

    /**
     * @return The second value.
     */
    public LLVMLiteral getValue2Literal() {
        return this.value2Literal;
    }

    /**
     * @return The set of names of the two values of this instruction.
     */
    public ImmutableSet<String> getValueNames() {
        LinkedHashSet<String> res = new LinkedHashSet<String>();
        if (this.value1Literal instanceof LLVMVariableLiteral) {
            res.add(((LLVMVariableLiteral)this.value1Literal).getName());
        }
        if (this.value2Literal instanceof LLVMVariableLiteral) {
            res.add(((LLVMVariableLiteral)this.value2Literal).getName());
        }
        return ImmutableCreator.create(res);
    }

    /**
     * @return The set of the two values of this instruction.
     */
    public ImmutableSet<LLVMLiteral> getValues() {
        LinkedHashSet<LLVMLiteral> res = new LinkedHashSet<LLVMLiteral>();
        res.add(this.value1Literal);
        res.add(this.value2Literal);
        return ImmutableCreator.create(res);
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("SelectInstr ");
        strBuilder.append(" identifier: " + this.getIdentifier());
        strBuilder.append(" cond: " + this.conditionLiteral.getType());
        strBuilder.append(" condLit: " + this.conditionLiteral);
        strBuilder.append(" valueType: " + this.value1Literal.getType());
        strBuilder.append(" value1Lit: " + this.value1Literal);
        strBuilder.append(" value2Lit: " + this.value2Literal);
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        StringBuilder res = new StringBuilder(this.getIdentifier().toDOTString());
        res.append(" = select ");
        res.append(this.conditionLiteral.toDOTString());
        res.append(", ");
        res.append(this.value1Literal.toDOTString());
        res.append(", ");
        res.append(this.value2Literal.toDOTString());
        return res.toString();
    }

    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        res.append(this.getIdentifier());
        res.append(" = select ");
        res.append(this.conditionLiteral);
        res.append(", ");
        res.append(this.value1Literal);
        res.append(", ");
        res.append(this.value2Literal);
        return res.toString();
    }

    @Override
    public String toLLVMIR() {
        StringBuilder res = new StringBuilder();
        res.append(this.getIdentifier());
        res.append(" = select ");
        res.append(this.conditionLiteral.getType().toLLVMIR());
        res.append(" ");
        res.append(this.conditionLiteral.toLLVMIR());
        res.append(", ");
        res.append(this.value1Literal.getType().toLLVMIR());
        res.append(" ");
        res.append(this.value1Literal);
        res.append(", ");
        res.append(this.value2Literal.getType().toLLVMIR());
        res.append(" ");
        res.append(this.value2Literal);
        return res.toString();
    }

}
