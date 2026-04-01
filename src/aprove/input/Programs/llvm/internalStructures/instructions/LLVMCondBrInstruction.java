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

/**
 * This is a conditional branch. If the condition value is true, control flows to the 'iftrue' label argument. If the
 * condition is false, control flows to the 'iffalse' label argument.
 * @author Janine Repke, cryingshadow
 */
public class LLVMCondBrInstruction extends LLVMBranchInstruction {

    /**
     * The literal representing the condition. If this is a true value, we will go to <code>ifTrueLabel</code>,
     * otherwise <code>ifFalseLabel</code>.
     */
    private final LLVMLiteral conditionLit;

    /**
     * Target for the case that <code>conditionLit</code> is false.
     */
    private final String ifFalseLabel;

    /**
     * Target for the case that <code>conditionLit</code> is true.
     */
    private final String ifTrueLabel;

    /**
     * @param condition The literal representing the condition.
     * @param trueLabel Target for the case that <code>condition</code> is true.
     * @param falseLabel Target for the case that <code>condition</code> is false.
     * @param debugLine The index of the line with debug information.
     */
    public LLVMCondBrInstruction(LLVMLiteral condition,String trueLabel, String falseLabel, int debugLine) {
        super(debugLine);
        this.conditionLit = condition;
        this.ifTrueLabel = trueLabel;
        this.ifFalseLabel = falseLabel;
    }

    @Override
    public void addConeVariables(Set<String> coneVars) {
        LLVMInstruction.collectVariable(coneVars, this.conditionLit);
    }

    @Override
    public void collectVariables(Collection<String> vars) {
        LLVMInstruction.collectVariable(vars, this.conditionLit);
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
        if (!(this.conditionLit instanceof LLVMVariableLiteral)) {
            return res;
        }
        String name = ((LLVMVariableLiteral)this.conditionLit).getName();
        LLVMRelation rel;
        if (pos.y.equals(this.ifFalseLabel)) {
            rel = relationFactory.equalTo(new LLVMHeuristicProgVarRef(name, name), termFactory.zero());
        } else {
            if (Globals.useAssertions) {
                assert (pos.y.equals(this.ifTrueLabel)) : "Found a successor which is no successor!";
            }
            rel = relationFactory.equalTo(new LLVMHeuristicProgVarRef(name, name), termFactory.one());
        }
        for (Pair<IntegerRelationSet, List<String>> pair : conditions) {
            if (pair.y.contains(pos.y)) {
                // do not follow loops
                continue;
            }
            IntegerRelationSet relSet = new IntegerRelationSet(pair.x);
            relSet.add(rel);
            List<String> path = new ArrayList<String>(pair.y);
            path.add(pos.y);
            res.add(new Pair<IntegerRelationSet, List<String>>(relSet, path));
        }
        return res;
    }

    @Override
    public Set<LLVMSymbolicEvaluationResult> evaluate(LLVMAbstractState state, int nodeNumber, boolean proveMemorySafety, LLVMMemoryChangeTracker memoryTracker, Abortion aborter)
    throws UndefinedBehaviorException {
        // determine the value of the literal (can be a variable or a constant)
        final LLVMSimpleTerm term = state.getSimpleTermForLiteral(this.conditionLit);
        if (state.isPossiblyTrapValue(term)) {
            throw new TrapValueException(nodeNumber);
        }
        final LLVMRelationFactory relationFactory = state.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        final LLVMRelation trueRel = relationFactory.equalTo(term, termFactory.one());
        final LLVMRelation falseRel = relationFactory.equalTo(term, termFactory.zero());
        final String label;
        Pair<Boolean, ? extends LLVMAbstractState> check = state.checkRelation(trueRel, aborter);
        LLVMAbstractState newState = check.y;
        if (check.x) {
            label = this.ifTrueLabel;
        } else {
            check = newState.checkRelation(falseRel, aborter);
            newState = check.y;
            if (check.x) {
                label = this.ifFalseLabel;
            } else {
                Set<LLVMSymbolicEvaluationResult> res = new LinkedHashSet<LLVMSymbolicEvaluationResult>();
                res.add(
                    new LLVMSymbolicEvaluationResult(newState.addRelation(trueRel, aborter), Collections.singleton(trueRel))
                );
                res.add(
                    new LLVMSymbolicEvaluationResult(newState.addRelation(falseRel, aborter), Collections.singleton(falseRel))
                );
                return res;
            }
        }
        // branch to target block and unset refinement flag
        
        Set<LLVMRelation> newRels = new LinkedHashSet<>();
        newState = newState.branchToBlock(label, nodeNumber, newRels, aborter);
        
        return
            Collections.singleton(
                new LLVMSymbolicEvaluationResult(newState, newRels)
            );
    }

    @Override
    public boolean isOverapproximation(LLVMAbstractState state, Abortion aborter) {
        return false;
    }
    
    @Override
    public String export(Export_Util eu) {
        StringBuilder res = new StringBuilder();
        res.append(eu.tttext("br "));
        res.append(eu.tttext(this.conditionLit.toString()));
        res.append(eu.tttext(", %"));
        res.append(eu.tttext(this.ifTrueLabel));
        res.append(eu.tttext(", %"));
        res.append(eu.tttext(this.ifFalseLabel));
        return res.toString();
    }
    
    public String getIfFalseLabel() {
        return this.ifFalseLabel;
    }
    
    public String getIfTrueLabel() {
        return this.ifTrueLabel;
    }

    @Override
    public Set<String> getInterestingVariables() {
        Set<String> vars = new LinkedHashSet<>();
        // the condition is interesting because it causes refinement
        LLVMInstruction.collectVariable(vars, this.conditionLit);
        return vars;
    }

    @Override
    public String getProducedVariable() {
        return null;
    }

    @Override
    public List<LLVMProgramPosition> getSuccessors(LLVMProgramPosition pos, LLVMModule module) {
        return
            new ListPair<LLVMProgramPosition>(
                new LLVMProgramPosition(pos.x, this.ifTrueLabel, 0),
                new LLVMProgramPosition(pos.x, this.ifFalseLabel, 0)
            );
    }

    @Override
    public String toDebugString() {
        StringBuilder strBuilder = new StringBuilder("CondBrInstr ");
        strBuilder.append(" condLit: " + this.conditionLit);
        strBuilder.append(" ifTrueLabel: " + this.ifTrueLabel);
        strBuilder.append(" ifFalseLabel: " + this.ifFalseLabel);
        return strBuilder.toString();
    }

    @Override
    public String toDOTString() {
        StringBuilder res = new StringBuilder();
        res.append("br ");
        res.append(this.conditionLit.toDOTString());
        res.append(", %");
        res.append(this.ifTrueLabel);
        res.append(", %");
        res.append(this.ifFalseLabel);
        return res.toString();
    }

    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        res.append("br ");
        res.append(this.conditionLit);
        res.append(", %");
        res.append(this.ifTrueLabel);
        res.append(", %");
        res.append(this.ifFalseLabel);
        return res.toString();
    }

}
