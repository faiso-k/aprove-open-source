package aprove.input.Programs.llvm.internalStructures;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.states.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.SMT.Solver.SMTLIB.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * A witness that starts a nonterminating loop.
 * @author Hermann Walth, cryingshadow
 */
public class LLVMAssignmentWitness extends LLVMWitness {

    /**
     * Specify a value for each nondeterministic instruction, organised by the node where nondeterminism originates.
     * If a nondeterministic value is relevant to termination, it needs to be documented in the witness.
     * Nondeterminism arises from the following sources:
     * - Function calls to declared functions
     * - Uninitialised memory, which rarely contributes to nontermination
     *   but must be kept track of regardless in case it does
     */
    private Map<Node<LLVMAbstractState>, LLVMConstant> nondetValues;

    /**
     * A mapping that specifies constant values for the witness state's references
     */
    private Map<LLVMSymbolicVariable, LLVMConstant> startReferences;

    /**
     * The node in the SE graph that starts a nonterminating loop
     */
    private Node<LLVMAbstractState> witnessNode;

    /**
     * Create a witness from an SMT model
     * @param witnessNode The node in the SE graph that starts a nonterminating loop
     * @param witnessModel An SMT model specifying values for the node's references
     */
    public LLVMAssignmentWitness(String graphmlPath, Node<LLVMAbstractState> witnessNode, Model witnessModel) {
        super(graphmlPath);
        this.witnessNode = witnessNode;
        this.startReferences = new LinkedHashMap<>();
        LLVMAbstractState state = witnessNode.getObject();
        LLVMTermFactory termFactory = state.getRelationFactory().getTermFactory();
        for (LLVMSymbolicVariable reference : state.getSymbolicVariables()) {
            SMTExpression<SInt> exp = reference.toSMTExp();
            if (!(exp instanceof Symbol<?>)) {
                continue;
            }
            SMTExpression<?> refValueSMT = witnessModel.get((Symbol<?>)exp);
            if (refValueSMT == null) {
                continue;
            }
            LLVMConstant newRef = termFactory.constant(refValueSMT.accept(new ConstantEvalVisitor()));
            this.startReferences.put(reference, newRef);
        }
    }

    /**
     * Create a witness from an SMT model and a mapping for declared function calls
     * @param witnessNode The node in the SE graph that starts a nonterminating loop
     * @param witnessModel An SMT model specifying values for the node's references
     * @param nondetValues A mapping specifying values for nondeterministic instructions
     */
    public LLVMAssignmentWitness(
        String graphmlPath,             
        Node<LLVMAbstractState> witnessNode,
        Model witnessModel,
        Map<Node<LLVMAbstractState>, LLVMConstant> nondetValues
    ) {
        this(graphmlPath, witnessNode, witnessModel);
        this.nondetValues = new LinkedHashMap<>(nondetValues);
    }

    /**
     * @return The witness node.
     */
    public Node<LLVMAbstractState> getNode() {
        return this.witnessNode;
    }

    /**
     * @return A mapping specifying a value for each nondeterministic function call.
     */
    public Map<Node<LLVMAbstractState>, LLVMConstant> getNondeterministicCalls() {
        if (this.nondetValues != null) {
            return new LinkedHashMap<>(this.nondetValues);
        } else {
            return new LinkedHashMap<>();
        }
    }

    /**
     * @return A mapping that specifies constant values for the witness state's references
     */
    public Map<LLVMSymbolicVariable, LLVMConstant> getStartReferences() {
        return new LinkedHashMap<>(this.startReferences);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(
            String.format(
                "State #%d with references set to %s.\n",
                this.witnessNode.getNodeNumber(),
                this.startReferences
            )
        );
        if (this.nondetValues != null) {
            for (Map.Entry<Node<LLVMAbstractState>, LLVMConstant> call : this.nondetValues.entrySet()) {
                sb.append(
                    String.format(
                        "Nondeterministic instruction %s in node #%d yields value %s.\n",
                        call.getKey().getObject().getCurrentInstruction().toString(),
                        call.getKey().getNodeNumber(),
                        call.getValue()
                    )
                );
            }
        }
        return sb.toString();
    }

}
