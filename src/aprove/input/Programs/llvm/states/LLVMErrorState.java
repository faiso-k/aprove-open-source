package aprove.input.Programs.llvm.states;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Set;
import java.util.TreeSet;

import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.IntegerReasoning.smt.*;
import immutables.*;

public class LLVMErrorState extends LLVMAbstractState {

    public LLVMErrorState(
        LLVMModule newModule,
        LLVMProgramPosition newProgPos,
        LLVMParameters params,
        Abortion aborter)
    {
        super(
            newModule,
            ImmutableCreator.create(Collections.emptyMap()),
            ImmutableCreator.create(new TreeSet<Integer>()),
            newProgPos,
            ImmutableCreator.create(new ArrayDeque<LLVMReturnInformation>()),
            false,
            new LLVMDefaultIntegerState(
                new PlainIntegerRelationState(params.SMTsolver.smtSolverFactory, params.SMTsolver.smtLogic),
                ImmutableCreator.create(Collections.emptyList()),
                ImmutableCreator.create(Collections.emptyMap()),
                ImmutableCreator.create(Collections.emptyMap()),
                ImmutableCreator.create(Collections.emptySet()),
                params, 
                aborter
            ),
            false,
            ImmutableCreator.create(new TreeSet<Integer>()),
            ImmutableCreator.create(Collections.emptyMap()),
            params,
            null,
            null
        );
    }
    
    @Override
    public boolean isErrorState() {
        return true;
    }
    
    @Override
   public LLVMSymbolicEvaluationResult postProcessAfterEvaluation(Set<? extends LLVMRelation> rels, boolean removeNonLiveVariables, Abortion aborter) {
       return new LLVMSymbolicEvaluationResult(this, Collections.emptySet());
   }
    
    public LLVMErrorState setVarToEntryStateVarsMap(ImmutableMap<LLVMSymbolicVariable,ImmutableSet<LLVMSymbolicVariable>> entryStateVarCorrespondenceMap) {
    	//does not actually change the entryStateVarCorrespondenceMap, but makes sure the returned state is an LLVMErrorState
    	return this;
    }

}
