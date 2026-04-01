package aprove.input.Programs.llvm.internalStructures.instructions;

import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.tracker.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Jump to one of several labels based on an integer comparison with constants.
 * @author Janine Repke, CryingShadow
 */
public class LLVMSwitchInstruction extends LLVMBranchInstruction {

    /**
     * The value to use for the switch (must be of some integer type).
     */
    private final LLVMLiteral compareValue;

    /**
     * The default destination to branch to if no switch value is met.
     */
    private final String defaultLabel;

    /**
     * A list of constant switch values and corresponding labels to branch to if the compareValue equals the respective
     * switch value.
     */
    private final ImmutableList<ImmutablePair<LLVMLiteral, String>> jumpEntries;

    /**
     * @param value The value to use for the switch (must be of some integer type).
     * @param label The default destination to branch to if no switch value is met.
     * @param jumps A list of switch values and corresponding labels to branch to if the compareValue equals the
     *              respective switch value.
     * @param debugLine The index of the line with debug information.
     */
    public LLVMSwitchInstruction(
        LLVMLiteral value,
        String label,
        ImmutableList<ImmutablePair<LLVMLiteral, String>> jumps,
        int debugLine
    ) {
        super(debugLine);
        this.compareValue = value;
        this.defaultLabel = label;
        this.jumpEntries = jumps;
    }

    @Override
    public void addConeVariables(Set<String> coneVars) {
        LLVMInstruction.collectVariable(coneVars, this.compareValue);
    }

    @Override
    public final void collectVariables(Collection<String> vars) {
        LLVMInstruction.collectVariable(vars, this.compareValue);
        /* it's all constants, so no jumpValues need to be added
            Set<String> vars = new LinkedHashSet<String>();
            this.addVariable(vars, this.compareValue);
            for (JumpEntry entry : this.jumpEntries) {
                this.addVariable(vars, entry.jumpValue);
            }
            return vars;*/
    }
    
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
        final LLVMRelationFactory relationFactory = params.SMTsolver.stateFactory.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        Set<Pair<IntegerRelationSet, List<String>>> res = new LinkedHashSet<Pair<IntegerRelationSet, List<String>>>();
        if (!(this.compareValue instanceof LLVMVariableLiteral)) {
            return res;
        }
        String name = ((LLVMVariableLiteral)this.compareValue).getName();
        Set<LLVMRelation> newRels = new LinkedHashSet<LLVMRelation>();
        final LLVMHeuristicProgVarRef var = new LLVMHeuristicProgVarRef(name, name);
        if (pos.y.equals(this.defaultLabel)) {
            for (ImmutablePair<LLVMLiteral, String> jump : this.jumpEntries) {
                newRels.add(relationFactory.notEqualTo(var, termFactory.constant(jump.x.evaluate())));
            }
        } else {
            LLVMConstant constant = null;
            for (ImmutablePair<LLVMLiteral, String> jump : this.jumpEntries) {
                if (pos.y.equals(jump.y)) {
                    constant = termFactory.constant(jump.x.evaluate());
                    break;
                }
            }
            if (Globals.useAssertions) {
                assert (constant != null) : "Found a successor which is no successor!";
            }
            newRels.add(relationFactory.equalTo(var, constant));
        }
        for (Pair<IntegerRelationSet, List<String>> pair : conditions) {
            if (pair.y.contains(pos.y)) {
                // do not follow loops
                continue;
            }
            IntegerRelationSet relSet = new IntegerRelationSet(pair.x);
            relSet.addAll(newRels);
            List<String> path = new ArrayList<String>(pair.y);
            path.add(pos.y);
            res.add(new Pair<IntegerRelationSet, List<String>>(relSet, path));
        }
        return res;
    }

    @Override
    public Set<LLVMSymbolicEvaluationResult> evaluate(LLVMAbstractState state, int nodeNumber, boolean proveMemorySafety, LLVMMemoryChangeTracker memoryTracker, Abortion aborter)
    throws UndefinedBehaviorException {
        final LLVMRelationFactory relationFactory = state.getRelationFactory();
        // determine the term for the literal (can be a variable or a constant)
        LLVMSimpleTerm term = state.getSimpleTermForLiteral(this.compareValue);
        if (state.isPossiblyTrapValue(term)) {
            throw new TrapValueException(nodeNumber);
        }
        // determine target block
        String target = this.defaultLabel;
        LLVMAbstractState newState = state;
        for (ImmutablePair<LLVMLiteral, String> jump : this.jumpEntries) {
            final LLVMSimpleTerm otherTerm = newState.getSimpleTermForLiteral(jump.x);
            final LLVMRelation trueRel = relationFactory.equalTo(term, otherTerm);
            final LLVMRelation falseRel = relationFactory.notEqualTo(term, otherTerm);
            Pair<Boolean, ? extends LLVMAbstractState> check = newState.checkRelation(trueRel, aborter);
            newState = check.y;
            if (check.x) {
                target = jump.y;
                break;
            } else {
                check = newState.checkRelation(falseRel, aborter);
                newState = check.y;
                if (!check.x) {
                    // refine
                    Set<LLVMSymbolicEvaluationResult> res =
                        new LinkedHashSet<LLVMSymbolicEvaluationResult>();
                    res.add(
                        new LLVMSymbolicEvaluationResult(newState.addRelation(trueRel, aborter), Collections.singleton(trueRel))
                    );
                    res.add(
                        new LLVMSymbolicEvaluationResult(
                            newState.addRelation(falseRel, aborter),
                            Collections.singleton(falseRel)
                        )
                    );
                    return res;
                }
            }
        }
        // branch to target block
        Set<LLVMRelation> newRels = new LinkedHashSet<>();
        newState = newState.branchToBlock(target, nodeNumber, newRels, aborter);
        
        LLVMSymbolicEvaluationResult evaluationResult = new LLVMSymbolicEvaluationResult(newState, newRels); 
        return Collections.singleton(evaluationResult);
    }
    
    @Override
    public boolean isOverapproximation(LLVMAbstractState state, Abortion aborter) {
        return false;
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder res = new StringBuilder();
        res.append(eu.tttext("switch "));
        res.append(eu.tttext(this.compareValue.toString()));
        res.append(eu.tttext(", %"));
        res.append(eu.tttext(this.defaultLabel));
        res.append(eu.tttext(" ["));
        boolean first = true;
        for (ImmutablePair<LLVMLiteral, String> jump : this.jumpEntries) {
            if (first) {
                first = false;
            } else {
                res.append(eu.tttext(" "));
            }
            res.append(eu.tttext(jump.x.toString()));
            res.append(eu.tttext(", %"));
            res.append(eu.tttext(jump.y));
        }
        res.append(eu.tttext("]"));
        return res.toString();
    }

    /**
     * @return The value to use for the switch (must be of some integer type).
     */
    public LLVMLiteral getCompareValue() {
        return this.compareValue;
    }

    /**
     * @return The default destination to branch to if no switch value is met.
     */
    public String getDefaultLabel() {
        return this.defaultLabel;
    }

    @Override
    public Set<String> getInterestingVariables() {
        Set<String> vars = new LinkedHashSet<>();
        // the condition is interesting because it causes refinement
        LLVMInstruction.collectVariable(vars, this.compareValue);
        return vars;
    }

    @Override
    public String getProducedVariable() {
        return null;
    }

    @Override
    public List<LLVMProgramPosition> getSuccessors(LLVMProgramPosition pos, LLVMModule module) {
        List<LLVMProgramPosition> poss = new ArrayList<LLVMProgramPosition>();
        for (ImmutablePair<LLVMLiteral, String> label : this.jumpEntries) {
            poss.add(new LLVMProgramPosition(pos.x, label.y, 0));
        }
        poss.add(new LLVMProgramPosition(pos.x, this.defaultLabel, 0));
        return poss;
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("SwitchInstr ");
        strBuilder.append(" CmpType: " + this.compareValue.getType());
        strBuilder.append(" CmpValue: " + this.compareValue);
        strBuilder.append(" DefaultLabel: " + this.defaultLabel);
        strBuilder.append(" JmpEntries: (");
        boolean first = true;
        for (ImmutablePair<LLVMLiteral, String> entry : this.jumpEntries) {
            if (first) {
                first = false;
            } else {
                strBuilder.append(", ");
            }
            strBuilder.append(" " + entry);
        }
        strBuilder.append(")");
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        StringBuilder strBuilder =
            new StringBuilder("switch " + this.compareValue.toDOTString() + ", %" + this.defaultLabel + " [");
        boolean first = true;
        for (ImmutablePair<LLVMLiteral, String> entry : this.jumpEntries) {
            if (first) {
                first = false;
            } else {
                strBuilder.append(" ");
            }
            strBuilder.append(entry.x.toDOTString() + ", %" + entry.y);
        }
        strBuilder.append("]");
        return strBuilder.toString();
    }

    @Override
    public String toString() {
        StringBuilder strBuilder =
            new StringBuilder("switch " + this.compareValue + ", %" + this.defaultLabel + " [");
        boolean first = true;
        for (ImmutablePair<LLVMLiteral, String> entry : this.jumpEntries) {
            if (first) {
                first = false;
            } else {
                strBuilder.append(" ");
            }
            strBuilder.append(entry.x + ", %" + entry.y);
        }
        strBuilder.append("]");
        return strBuilder.toString();
    }

}
