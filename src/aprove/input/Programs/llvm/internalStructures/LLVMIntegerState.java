package aprove.input.Programs.llvm.internalStructures;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Wraps an integer state with an allocation list and memory information to construct the formula set &lt;a&gt; which
 * contains disjunctions.
 * @author cryingshadow
 * @version $Id$
 */
public abstract class LLVMIntegerState implements IntegerState {

    /**
     * Stores start and end point of separately allocated memory. This is a list to make the elements accessible via an
     * index. However, this list should otherwise behave like a set (even worse, it should not contain any reference
     * twice).
     */
    private final ImmutableList<LLVMAllocation> allocations;

    /**
     * The formula &lt;a&gt; (i.e., the integer state enriched by relations from the allocations and memory
     * information) or null.
     */
    private final SMTExpression<SBool> formula;

    /**
     * Represents the memory with dereferenced values.
     */
    private final ImmutableMap<LLVMMemoryRange, LLVMMemoryInvariant> memory;

    /**
     * The wrapped integer state.
     */
    private final IntegerState state;

    /**
     * @param iState The integer state to wrap.
     * @param allocs The allocation list.
     * @param memoryParam The memory information.
     * @param form The formula &lt;a&gt; (i.e., the integer state enriched by relations from the allocations and memory
     *             information).
     */
    protected LLVMIntegerState(
        IntegerState iState,
        List<LLVMAllocation> allocs,
        Map<LLVMMemoryRange, LLVMMemoryInvariant> memoryParam,
        SMTExpression<SBool> form
    ) {
        this.state = iState;
        this.allocations = ImmutableCreator.create(allocs);
        this.memory = ImmutableCreator.create(memoryParam);
        this.formula = form;
    }

    @Override
    public abstract LLVMIntegerState addRelation(IntegerRelation relation, Abortion aborter);

    @Override
    public abstract LLVMIntegerState addRelationSet(Iterable<? extends IntegerRelation> relations, Abortion aborter);

    /**
     * @return An SMT expression that encodes that the memory blocks are disjoint, have a length of at least 0, and
     *         start at an address greater than 0.
     */
    public List<SMTExpression<SBool>> allocationInformationToSMTExp() {
        final LLVMTermFactory termFactory = this.getRelationFactory().getTermFactory();
        final ImmutableList<LLVMAllocation> allocatedMemory = this.getAllocations();
        List<SMTExpression<SBool>> subformulas = new LinkedList<SMTExpression<SBool>>();
        // 3 things to represent:
        // 1. 1 <= first element
        // 2. first element <= second element
        for (LLVMAllocation block : allocatedMemory) {
            subformulas.add(Ints.lessEqual(termFactory.one().toSMTExp(), block.x.toSMTExp()));
            subformulas.add(Ints.lessEqual(block.x.toSMTExp(), block.y.toSMTExp()));
        }
        // 3. the memory blocks are disjoint:
        int size = this.getAllocations().size();
        for (int i = 0; i < size; ++i) {
            LLVMAllocation block1 = allocatedMemory.get(i);
            for (int j = i + 1; j < size; ++j) {
                LLVMAllocation block2 = allocatedMemory.get(j);
                // two possibilities: block1.max < block2.min or block2.max < block1.min
                subformulas.add(
                    Core.or(
                        Ints.less(block1.y.toSMTExp(), block2.x.toSMTExp()),
                        Ints.less(block2.y.toSMTExp(), block1.x.toSMTExp())
                    )
                );
            }
        }
        return subformulas;
    }

    /**
     * @param pointer The pointer.
     * @param type The type of the pointer.
     * @param index The index of the allocation.
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @param aborter For abortions.
     * @return The state where the specified pointer of the specified type is associated to the allocation at the
     *         specified index.
     */
    public LLVMIntegerState associateAccess(
        LLVMSymbolicVariable pointer,
        LLVMPointerType type,
        Integer index,
        Set<LLVMRelation> newRels,
        Abortion aborter
    ) {
        final LLVMRelationFactory relationFactory = this.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        final LLVMAllocation allocation = this.getAllocations().get(index);
        final BigInteger offset = type.toOffset();
        LLVMIntegerState res = this;
        if (!allocation.x.equals(pointer)) {
            LLVMRelation lowerBoundRel = relationFactory.lessThanEquals(allocation.x, pointer);
            res = res.addRelation(lowerBoundRel, aborter);
            if (newRels != null) {
                newRels.add(lowerBoundRel);
            }
        }
        
        LLVMRelation upperBoundRel = relationFactory.lessThanEquals(termFactory.add(pointer, termFactory.constant(offset)), allocation.y);
        res = res.addRelation(upperBoundRel, aborter);
        if (newRels != null) {
            newRels.add(upperBoundRel);
        }
        
        return res;
    }

    @Override
    public Pair<Boolean, ? extends LLVMIntegerState> checkRelation(IntegerRelation rel, Abortion aborter) {
        if (Globals.useAssertions) {
            assert (this.getFormula() != null) : "Tried to check implication on integer state with null formula!";
        }
        return
            new Pair<Boolean, LLVMIntegerState>(
                PlainIntegerRelationState.checkRelationWithSMTSolver(this.getFormula(), rel, this.getSolver(aborter)),
                this
            );
    }

    /**
     * @return The allocations.
     */
    public ImmutableList<LLVMAllocation> getAllocations() {
        return this.allocations;
    }

    /**
     * @param term Some simple term (variable or constant).
     * @param type The target type of the term.
     * @param oneMore Is one byte after the allocation ok?
     * @param aborter For abortions.
     * @return The index of the allocation to which the specified term is associated to, a flag whether the specified
     *         address is exactly one cell behind the allocation, and the integer state after this check. The first
     *         component is null if there is no such allocation.
     */
    public Pair<LLVMAssociationIndex, ? extends LLVMIntegerState> getAssociatedAllocationIndex(
        LLVMTerm term,
        LLVMPointerType type,
        boolean oneMore,
        Abortion aborter
    ) {
        final LLVMRelationFactory relationFactory = this.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        final LLVMConstant offset = termFactory.constant(type.toOffset());
        int i = 0;
        Iterator<LLVMAllocation> it = this.getAllocations().iterator();
        LLVMIntegerState res = this;
        while (it.hasNext()) {
            LLVMAllocation allocation = it.next();
            Pair<Boolean, ? extends LLVMIntegerState> lower =
                res.checkRelation(relationFactory.lessThanEquals(allocation.x, term), aborter);
            res = lower.y;
            if (lower.x) {
                Pair<Boolean, ? extends LLVMIntegerState> upper =
                    res.checkRelation(
                        relationFactory.lessThanEquals(termFactory.add(term, offset), allocation.y),
                        aborter
                    );
                res = upper.y;
                if (upper.x) {
                    return new Pair<LLVMAssociationIndex, LLVMIntegerState>(new LLVMAssociationIndex(i, false), res);
                }
                if (oneMore) {
                    Pair<Boolean, ? extends LLVMIntegerState> behind =
                        res.checkRelation(
                            relationFactory.lessThanEquals(term, termFactory.add(allocation.y, termFactory.one())),
                            aborter
                        );
                    res = behind.y;
                    if (behind.x) {
                        return new Pair<LLVMAssociationIndex, LLVMIntegerState>(new LLVMAssociationIndex(i, true), res);
                    }
                }
            }
            i++;
        }
        return new Pair<LLVMAssociationIndex, LLVMIntegerState>(null, res);
    }

    /**
     * @param term Some simple term (variable or constant).
     * @param oneMore Is one byte after the allocation ok?
     * @param aborter For abortions.
     * @return The indices of all allocations to which the specified term may be associated, a flag whether the specified
     *         address is exactly one cell behind the allocation, and the integer state after this check. The first
     *         component is null if there is no such allocation.
     */
    public Pair<Set<Integer>, ? extends LLVMIntegerState> getAssociatedAllocationIndices(
        LLVMTerm term,
        Abortion aborter
    ) {
        final LLVMRelationFactory relationFactory = this.getRelationFactory();
        int i = 0;
        Iterator<LLVMAllocation> it = this.getAllocations().iterator();
        LLVMIntegerState res = this;
        Set<Integer> allocIndices = new HashSet<Integer>();
        while (it.hasNext()) {
            LLVMAllocation allocation = it.next();
            Pair<Boolean, ? extends LLVMIntegerState> lower =
                res.checkRelation(relationFactory.lessThanEquals(allocation.x, term), aborter);
            res = lower.y;
            if (lower.x) {
                Pair<Boolean, ? extends LLVMIntegerState> upper =
                    res.checkRelation(
                        relationFactory.lessThanEquals(term, allocation.y),
                        aborter
                    );
                res = upper.y;
                if (upper.x) {
                    allocIndices.add(i);
                }
            }
            i++;
        }
        return new Pair<Set<Integer>, LLVMIntegerState>(allocIndices, res);
    }

    /**
     * @return The wrapped integer state.
     */
    public IntegerState getIntegerState() {
        return this.state;
    }

    /**
     * @return The memory information.
     */
    public ImmutableMap<LLVMMemoryRange, LLVMMemoryInvariant> getMemory() {
        return this.memory;
    }

    /**
     * @param allocs The new allocations.
     * @return This state where the allocations have been set to the specified ones.
     */
    public abstract LLVMIntegerState setAllocations(List<LLVMAllocation> allocs);

    /**
     * @param newMemory The new memory information.
     * @return This state where the heap has been set to the specified one.
     */
    public abstract LLVMIntegerState setMemory(Map<LLVMMemoryRange, LLVMMemoryInvariant> newMemory);

    @Override
    public String toDOTString() {
        return this.getIntegerState().toDOTString();
    }

    @Override
    public Object toJSON() {
        return this.getIntegerState().toJSON();
    }

    @Override
    public IntegerRelationSet toRelationSet() {
        return this.getIntegerState().toRelationSet();
    }

    @Override
    public String toString() {
        return this.getIntegerState().toString();
    }

    /**
     * @return The formula &lt;a&gt; (i.e., the integer state enriched by relations from the allocations and memory
     *         information) or null.
     */
    protected SMTExpression<SBool> getFormula() {
        return this.formula;
    }

    /**
     * @return The relation factory used to build relations for this state.
     */
    protected abstract LLVMRelationFactory getRelationFactory();

    /**
     * @return The SMTSolver used to check implications.
     */
    protected abstract SMTSolver getSolver(Abortion aborter);

}
