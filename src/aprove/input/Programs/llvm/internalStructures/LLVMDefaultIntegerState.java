package aprove.input.Programs.llvm.internalStructures;

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
 * The default wrapper integer state for LLVM.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMDefaultIntegerState extends LLVMIntegerState {

    /**
     * @param iState An integer state.
     * @param allocs The allocations.
     * @param heapParam The memory information.
     * @param relations A set of relations known to hold.
     * @param parameters Strategy parameters.
     * @return An integer state, an SMT formula, and a set of relations all encoding the specified knowledge.
     */
    private static Triple<IntegerState, SMTExpression<SBool>, IntegerRelationSet> createFormula(
        IntegerState iState,
        List<LLVMAllocation> allocs,
        Map<LLVMMemoryRange, LLVMMemoryInvariant> heapParam,
        Set<IntegerRelation> relations,
        LLVMParameters parameters,
        Abortion aborter
    ) {
        final LLVMRelationFactory relationFactory = parameters.SMTsolver.stateFactory.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        List<SMTExpression<SBool>> ors = new ArrayList<SMTExpression<SBool>>();
        IntegerRelationSet relSet = iState.toRelationSet();
        for (LLVMAllocation allocation : allocs) {
            relSet.add(relationFactory.lessThanEquals(termFactory.one(), allocation.x));
            relSet.add(relationFactory.lessThanEquals(allocation.x, allocation.y));
            for (LLVMAllocation otherAlloc : allocs) {
                if (allocation == otherAlloc) {
                    continue;
                }
                ors.add(
                    Core.or(
                        relationFactory.lessThan(allocation.y, otherAlloc.x).toSMTExp(),
                        relationFactory.lessThan(otherAlloc.y, allocation.x).toSMTExp()
                    )
                );
            }
        }
        for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> entry : heapParam.entrySet()) {
            LLVMMemoryRange range = entry.getKey();
            relSet.add(relationFactory.lessThanEquals(termFactory.one(), range.getFromRef()));
            if (!range.isPointwise()) {
                relSet.add(relationFactory.lessThanEquals(range.getFromRef(), range.getToRef()));
            }
        }
        SMTExpression<SBool> formula = Core.and(Core.and(ors), relSet.toSMTExp());
        LLVMDefaultIntegerState nextState =
            new LLVMDefaultIntegerState(
                allocs,
                heapParam,
                ImmutableCreator.create(Collections.emptyMap()),
                parameters,
                new Triple<IntegerState, SMTExpression<SBool>, IntegerRelationSet>(iState, formula, relSet)
            );
        IntegerRelationSet newRels = new IntegerRelationSet();
        do {
            for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> entry : heapParam.entrySet()) {
                LLVMMemoryRange range = entry.getKey();
                if (!range.isPointwise()) {
                    continue;
                }
                // TODO currently, only simple invariants are supported here
                final LLVMSimpleTerm toRef = ((LLVMSimpleMemoryInvariant)entry.getValue()).getPointedToValue();
                for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> other : heapParam.entrySet()) {
                    if (entry == other) {
                        continue;
                    }
                    LLVMMemoryRange otherRange = other.getKey();
                    if (!otherRange.isPointwise()) {
                        continue;
                    }
                    final LLVMSimpleTerm otherToRef = ((LLVMSimpleMemoryInvariant)other.getValue()).getPointedToValue();
                    final Pair<Boolean, ? extends LLVMIntegerState> equal =
                        nextState.checkRelation(
                            relationFactory.equalTo(range.getFromRef(), otherRange.getFromRef()),
                            aborter
                        );
                    nextState = (LLVMDefaultIntegerState)equal.y;
                    if (equal.x) {
                        newRels.add(relationFactory.equalTo(toRef, otherToRef));
                    } else {
                        final Pair<Boolean, ? extends LLVMIntegerState> unequal =
                            nextState.checkRelation(relationFactory.notEqualTo(toRef, otherToRef), aborter);
                        nextState = (LLVMDefaultIntegerState)unequal.y;
                        if (unequal.x) {
                            newRels.add(relationFactory.notEqualTo(range.getFromRef(), otherRange.getFromRef()));
                        }
                    }
                }
            }
            newRels.removeAll(relSet);
            if (relSet.addAll(newRels)) {
                formula = Core.and(Core.and(ors), relSet.toSMTExp());
                nextState =
                    new LLVMDefaultIntegerState(
                        allocs,
                        heapParam,
                        ImmutableCreator.create(Collections.emptyMap()),
                        parameters,
                        new Triple<IntegerState, SMTExpression<SBool>, IntegerRelationSet>(iState, formula, relSet)
                    );
            }
        } while (!newRels.isEmpty());
        relSet.addAll(relations);
        return
            new Triple<IntegerState, SMTExpression<SBool>, IntegerRelationSet>(
                iState.addRelationSet(relSet, aborter),
                formula,
                relSet
            );
    }

    /**
     * The cached associations. Not necessarily complete.
     */
    private final ImmutableMap<LLVMSimpleMemoryAccess, LLVMAssociationIndex> cachedAssociations;

    /**
     * Strategy parameters.
     */
    private final LLVMParameters params;

    /**
     * The cached set of relations encoding the knowledge in this integer state. Checked relations will be added as
     * soon as they are proven.
     */
    private final ImmutableSet<IntegerRelation> rels;

    /**
     * Is the formula updated?
     */
    private final boolean updated;

    /**
     * @param iState The wrapped integer state.
     * @param allocs The allocations.
     * @param heapParam The memory information.
     * @param assocs The cached associations.
     * @param relations A set of relations known to hold.
     * @param parameters Strategy parameters.
     */
    public LLVMDefaultIntegerState(
        IntegerState iState,
        List<LLVMAllocation> allocs,
        Map<LLVMMemoryRange, LLVMMemoryInvariant> heapParam,
        Map<LLVMSimpleMemoryAccess, LLVMAssociationIndex> assocs,
        Set<IntegerRelation> relations,
        LLVMParameters parameters,
        Abortion aborter
    ) {
        this(
            allocs,
            heapParam,
            assocs,
            parameters,
            LLVMDefaultIntegerState.createFormula(iState, allocs, heapParam, relations, parameters, aborter)
        );
    }

    /**
     * @param iState The wrapped integer state.
     * @param allocs The allocations.
     * @param heapParam The memory information.
     * @param assocs The cached associations.
     * @param relations The cached relations.
     * @param formula The SMT formula.
     * @param up Is the formula updated?
     * @param parameters Strategy parameters.
     */
    private LLVMDefaultIntegerState(
        IntegerState iState,
        List<LLVMAllocation> allocs,
        Map<LLVMMemoryRange, LLVMMemoryInvariant> heapParam,
        Map<LLVMSimpleMemoryAccess, LLVMAssociationIndex> assocs,
        Set<IntegerRelation> relations,
        SMTExpression<SBool> formula,
        boolean up,
        LLVMParameters parameters
    ) {
        super(iState, allocs, heapParam, formula);
        this.params = parameters;
        this.rels = ImmutableCreator.create(relations);
        this.cachedAssociations = ImmutableCreator.create(assocs);
        this.updated = up;
    }

    /**
     * @param allocs The allocations.
     * @param heapParam The memory information.
     * @param assocs The cached associations.
     * @param parameters Strategy parameters.
     * @param triple The wrapped integer state, the constructed SMT formula, and the cached set of relations.
     */
    private LLVMDefaultIntegerState(
        List<LLVMAllocation> allocs,
        Map<LLVMMemoryRange, LLVMMemoryInvariant> heapParam,
        Map<LLVMSimpleMemoryAccess, LLVMAssociationIndex> assocs,
        LLVMParameters parameters,
        Triple<IntegerState, SMTExpression<SBool>, IntegerRelationSet> triple
    ) {
        this(triple.x, allocs, heapParam, assocs, triple.z, triple.y, true, parameters);
    }

    @Override
    public LLVMDefaultIntegerState addRelation(IntegerRelation relation, Abortion aborter) {
        final Boolean trivial;
        try {
            trivial = IntegerUtils.solveTrivially(relation);
        } catch (DivisionByZeroException e) {
            throw new IllegalArgumentException("Tried to add a relation containing a division by zero!");
        }
        if (trivial != null) {
            if (trivial) {
                return this;
            } else {
                throw new IllegalArgumentException("Tried to add contradictive relation!");
            }
        }
        if (this.rels.contains(relation)) {
            return this;
        }
        return
            new LLVMDefaultIntegerState(
                this.getIntegerState().addRelation(relation, aborter),
                this.getAllocations(),
                this.getMemory(),
                this.getCachedAssociations(),
                this.rels,
                this.getFormula(),
                false,
                this.params
            );
    }

    @Override
    public LLVMDefaultIntegerState addRelationSet(Iterable<? extends IntegerRelation> relations, Abortion aborter) {
        boolean noChange = true;
        for (IntegerRelation rel : relations) {
            final Boolean trivial;
            try {
                trivial = IntegerUtils.solveTrivially(rel);
            } catch (DivisionByZeroException e) {
                throw new IllegalArgumentException("Tried to add a relation containing a division by zero!");
            }
            if (trivial == null) {
                if (!this.rels.contains(rel)) {
                    noChange = false;
                    break;
                }
            } else if (!trivial) {
                throw new IllegalArgumentException("Tried to add contradictive relation!");
            }
        }
        if (noChange) {
            return this;
        }
        return
            new LLVMDefaultIntegerState(
                this.getIntegerState().addRelationSet(relations, aborter),
                this.getAllocations(),
                this.getMemory(),
                this.getCachedAssociations(),
                this.rels,
                this.getFormula(),
                false,
                this.params
            );
    }

    @Override
    public LLVMIntegerState associateAccess(
        LLVMSymbolicVariable pointer,
        LLVMPointerType type,
        Integer index,
        Set<LLVMRelation> newRels,
        Abortion aborter
    ) {
        LLVMSimpleMemoryAccess key = new LLVMSimpleMemoryAccess(pointer, type);
        if (this.getCachedAssociations().containsKey(key)) {
            if (Globals.useAssertions) {
                assert (key.equals(this.getCachedAssociations().get(key))) :
                    "Tried to associate a term to a different allocation than before!";
            }
            return this;
        }
        Map<LLVMSimpleMemoryAccess, LLVMAssociationIndex> newAssocs =
            new LinkedHashMap<LLVMSimpleMemoryAccess, LLVMAssociationIndex>(this.getCachedAssociations());
        
        newAssocs.put(key, new LLVMAssociationIndex(index, false));
        
        LLVMDefaultIntegerState res = (LLVMDefaultIntegerState)super.associateAccess(pointer, type, index, newRels, aborter);
        res = res.setCachedAssociations(newAssocs);
        
        return res;
    }

    @Override
    public Pair<Boolean, ? extends LLVMIntegerState> checkRelation(IntegerRelation rel, Abortion aborter) {
        final Boolean trivial;
        try {
            trivial = IntegerUtils.solveTrivially(rel);
        } catch (DivisionByZeroException e) {
            System.err.println("Checked a relation containing a division by zero...");
            return new Pair<Boolean, LLVMDefaultIntegerState>(false, this);
        }
        if (trivial != null) {
            return new Pair<Boolean, LLVMIntegerState>(trivial, this);
        }
        if (this.rels.contains(rel)) {
            return new Pair<Boolean, LLVMDefaultIntegerState>(true, this);
        }
        Pair<Boolean, ? extends LLVMIntegerState> res = super.checkRelation(rel, aborter);
        if (res.x) {
            return
                new Pair<Boolean, LLVMDefaultIntegerState>(true, ((LLVMDefaultIntegerState)res.y).cacheRelation(rel));
        }
        return res;
    }

    @Override
    public Pair<LLVMAssociationIndex, ? extends LLVMIntegerState> getAssociatedAllocationIndex(
        LLVMTerm term,
        LLVMPointerType type,
        boolean oneMore,
        Abortion aborter
    ) {
        final LLVMSimpleMemoryAccess key = new LLVMSimpleMemoryAccess(term, type);
        final ImmutableMap<LLVMSimpleMemoryAccess, LLVMAssociationIndex> assocs = this.getCachedAssociations();
        if (assocs.containsKey(key)) {
            final LLVMAssociationIndex index = assocs.get(key);
            if (!oneMore && index.y) {
                return new Pair<LLVMAssociationIndex, LLVMDefaultIntegerState>(null, this);
            }
            return new Pair<LLVMAssociationIndex, LLVMDefaultIntegerState>(index, this);
        }
        Pair<LLVMAssociationIndex, ? extends LLVMIntegerState> res =
            super.getAssociatedAllocationIndex(term, type, oneMore, aborter);
        if (res.x == null) {
            return res;
        }
        Map<LLVMSimpleMemoryAccess, LLVMAssociationIndex> newAssocs =
            new LinkedHashMap<LLVMSimpleMemoryAccess, LLVMAssociationIndex>(assocs);
        newAssocs.put(key, res.x);
        return
            new Pair<LLVMAssociationIndex, LLVMDefaultIntegerState>(
                res.x,
                ((LLVMDefaultIntegerState)res.y).setCachedAssociations(newAssocs)
            );
    }

    @Override
    public LLVMDefaultIntegerState setAllocations(List<LLVMAllocation> allocs) {
        ImmutableList<LLVMAllocation> oldAllocs = this.getAllocations();
        boolean ok = oldAllocs.size() <= allocs.size();
        for (int i = 0; ok && i < oldAllocs.size(); i++) {
            ok &= oldAllocs.get(i).equals(allocs.get(i));
        }
        return
            new LLVMDefaultIntegerState(
                this.getIntegerState(),
                ImmutableCreator.create(allocs),
                this.getMemory(),
                ok ? this.getCachedAssociations() : ImmutableCreator.create(Collections.emptyMap()),
                this.rels,
                this.getFormula(),
                false,
                this.params
            );
    }

    @Override
    public LLVMDefaultIntegerState setMemory(Map<LLVMMemoryRange, LLVMMemoryInvariant> newMemory) {
        return
            new LLVMDefaultIntegerState(
                this.getIntegerState(),
                this.getAllocations(),
                ImmutableCreator.create(newMemory),
                this.getCachedAssociations(),
                this.rels,
                this.getFormula(),
                false,
                this.params
            );
    }

    /**
     * @return This state with an updated formula.
     */
    public Pair<LLVMDefaultIntegerState, Set<LLVMRelation>> updateFormula(Abortion aborter) {
        final LLVMDefaultIntegerState iState =
            new LLVMDefaultIntegerState(
                this.getIntegerState(),
                this.getAllocations(),
                this.getMemory(),
                this.getCachedAssociations(),
                this.rels,
                this.params,
                aborter
            );
        final IntegerRelationSet set = iState.toRelationSet();
        set.removeAll(this.rels);
        final LLVMRelationFactory relationFactory = this.getRelationFactory();
        final Set<LLVMRelation> relations = new LinkedHashSet<LLVMRelation>();
        for (IntegerRelation rel : set) {
            relations.add(relationFactory.createRelation(rel));
        }
        return new Pair<LLVMDefaultIntegerState, Set<LLVMRelation>>(iState, relations);
    }

    /**
     * @param rel The relation to cache.
     * @return This state where the specified relation is cached to hold.
     */
    protected LLVMDefaultIntegerState cacheRelation(IntegerRelation rel) {
        Set<IntegerRelation> newSet = new LinkedHashSet<IntegerRelation>(this.rels);
        if (newSet.add(rel)) {
            return
                new LLVMDefaultIntegerState(
                    this.getIntegerState(),
                    this.getAllocations(),
                    this.getMemory(),
                    this.getCachedAssociations(),
                    newSet,
                    this.getFormula(),
                    this.updated,
                    this.params
                );
        }
        return this;
    }

    /**
     * @return The cached associations. Not necessarily complete.
     */
    protected ImmutableMap<LLVMSimpleMemoryAccess, LLVMAssociationIndex> getCachedAssociations() {
        return this.cachedAssociations;
    }

    @Override
    protected LLVMRelationFactory getRelationFactory() {
        return this.params.SMTsolver.stateFactory.getRelationFactory();
    }

    @Override
    protected SMTSolver getSolver(Abortion aborter) {
        return this.params.SMTsolver.smtSolverFactory.getSMTSolver(this.params.SMTsolver.smtLogic, aborter);
    }

    /**
     * @param newAssocs The cached associations.
     * @return This state with the specified cached associations.
     */
    protected LLVMDefaultIntegerState setCachedAssociations(
        Map<LLVMSimpleMemoryAccess, LLVMAssociationIndex> newAssocs
    ) {
        return
            new LLVMDefaultIntegerState(
                this.getIntegerState(),
                this.getAllocations(),
                this.getMemory(),
                ImmutableCreator.create(newAssocs),
                this.rels,
                this.getFormula(),
                this.updated,
                this.params
            );
    }

}
