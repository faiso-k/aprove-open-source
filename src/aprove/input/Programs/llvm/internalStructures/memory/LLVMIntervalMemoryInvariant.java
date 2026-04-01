package aprove.input.Programs.llvm.internalStructures.memory;

import java.math.BigInteger;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * An interval invariant stores the information that a value lies between two values.
 * @author Cornelius Aschermann, cryingshadow
 * @version $Id$
 */
public class LLVMIntervalMemoryInvariant implements LLVMMemoryInvariant {

    private final int hashCode = 1093;

    private static LLVMIntervalMemoryInvariant ensure_proper_inv(LLVMIntervalMemoryInvariant a) {
        if (a.isConstrained()) {
            return a;
        }
        return null;
    }

    /**
     * The lower bound of the interval. Null means no bound.
     */
    private final LLVMConstant lower;

    /**
     * The upper bound of the interval. Null means no bound.
     */
    private final LLVMConstant upper;

    /**
     * @param low The lower bound of the interval. Null means no bound.
     * @param up The upper bound of the interval. Null means no bound.
     */
    public LLVMIntervalMemoryInvariant(LLVMConstant low, LLVMConstant up) {
        this.lower = low;
        this.upper = up;
    }

    /**
     * @param interval The interval.
     */
    public LLVMIntervalMemoryInvariant(Pair<LLVMConstant, LLVMConstant> interval) {
        this.lower = interval.x;
        this.upper = interval.y;
    }
    
    @Override
    public boolean equals(Object object) {
        if (object instanceof LLVMIntervalMemoryInvariant) {
            LLVMIntervalMemoryInvariant other = (LLVMIntervalMemoryInvariant) object;
            if (this.lower == null) {
                if (other.lower != null) return false;
                return this.upper == null ? other.upper == null : this.upper.equals(other.upper);
            }
            if (this.upper == null) {
                return other.upper == null ? this.lower.equals(other.lower) : false;
            }
            boolean t = this.lower.equals(other.lower) && this.upper.equals(other.upper);
            return t;
        }
        return false;
    }

    @Override
    public Set<LLVMSymbolicVariable> getUsedReferences() {
        return new LinkedHashSet<LLVMSymbolicVariable>();
    }

    /**
     * @return True if at least one bound is set.
     */
    public boolean isConstrained() {
        return this.lower != null || this.upper != null;
    }

    @Override
    public boolean isSimple() {
        return false;
    }

    public Pair<LLVMMemoryInvariant, ? extends LLVMAbstractState> join_interval_invariant(
        LLVMAbstractState other_state,
        LLVMIntervalMemoryInvariant other
    ) {
        LLVMMemoryInvariant res = null;
        if (other != null) {
            res =
                LLVMIntervalMemoryInvariant.ensure_proper_inv(
                    new LLVMIntervalMemoryInvariant(
                        IntegerUtils.union(this.lower, this.upper, other.lower, other.upper)
                    )
                );
        }
        return new Pair<LLVMMemoryInvariant, LLVMAbstractState>(res, other_state);
    }

    @Override
    public Pair<LLVMMemoryInvariant, ? extends LLVMAbstractState> joinInvariant(
        LLVMAbstractState other_state,
        LLVMMemoryInvariant other,
        Abortion aborter
    ) {
        LLVMIntervalMemoryInvariant other_inv = null;
        if (other instanceof LLVMIntervalMemoryInvariant) {
            other_inv = (LLVMIntervalMemoryInvariant)other;
        } else if (other instanceof LLVMSimpleMemoryInvariant) {
            other_inv = ((LLVMSimpleMemoryInvariant)other).to_interval_invariant(other_state);
        } else {
            throw new IllegalStateException("Someone found a new kind of memory invariant!");
        }
        return this.join_interval_invariant(other_state, other_inv);
    }

    @Override
    public Pair<LLVMSimpleTerm, LLVMAbstractState> load(
        LLVMAbstractState state,
        LLVMSimpleTerm ptr,
        LLVMType targetType,
        boolean unsigned,
        Abortion aborter
    ) {
        final LLVMRelationFactory relationFactory = state.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        LLVMSymbolicVariable pointedToRef = termFactory.freshVariable();
        LLVMAbstractState res = state;
        if (this.lower != null) {
            res = res.addRelation(relationFactory.lessThanEquals(this.lower, pointedToRef), aborter);
        }
        if (this.upper != null) {
            res = res.addRelation(relationFactory.lessThanEquals(pointedToRef, this.upper), aborter);
        }
        return
            new Pair<LLVMSimpleTerm, LLVMAbstractState>(
                pointedToRef,
                res.setSimpleHeapEntry(ptr, targetType, unsigned, pointedToRef, aborter)
            );
    }

    @Override
    public Pair<Boolean, ? extends LLVMAbstractState> mayShareWith(LLVMMemoryInvariant other, LLVMAbstractState state, Abortion aborter) {
        final LLVMTermFactory termFactory = state.getRelationFactory().getTermFactory();
        if (other instanceof LLVMIntervalMemoryInvariant) {
            LLVMIntervalMemoryInvariant other_inv = (LLVMIntervalMemoryInvariant)other;
            return
                new Pair<Boolean, LLVMAbstractState>(
                    IntegerUtils.intersection(this.lower, this.upper, other_inv.lower, other_inv.upper) != null,
                    state
                );
        }
        if (other instanceof LLVMSimpleMemoryInvariant) {
            return this.mayShareWith(((LLVMSimpleMemoryInvariant)other).to_interval_invariant(state), state, aborter);
        }
        return new Pair<Boolean, LLVMAbstractState>(true, state);
    }

    @Override
    public LLVMMemoryInvariant replaceReference(LLVMSimpleTerm old_ref, LLVMSimpleTerm new_ref) {
        return null;
    }

    @Override
    public LLVMMemoryInvariant replaceReferences(Map<? extends LLVMSimpleTerm, ? extends LLVMSimpleTerm> replacements) {
        return this;
    }
    
    /**
     * @return True iff the given interval is a subset of this invariant.
     */
    public boolean subset(IntervalBound subLower, IntervalBound subUpper) {
        boolean checkLower = subLower.isFinite() ?
            (this.lower == null || this.lower.getIntegerValue().compareTo(subLower.getConstant()) <= 0) :
                this.lower == null;
        boolean checkUpper = subUpper.isFinite() ?
            (this.upper == null || this.upper.getIntegerValue().compareTo(subUpper.getConstant()) >= 0) :
                this.upper == null;
        return checkLower && checkUpper;
    }

    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        res.append("IInv[");
        res.append(this.lower == null ? "-inf" : this.lower);
        res.append(", ");
        res.append(this.upper == null ? "+inf" : this.upper);
        res.append("]");
        return res.toString();
    }

    @Override
    public boolean usesReference(LLVMSimpleTerm other) {
        return false;
    }

    @Override
    public int hashCode() {
        return hashCode;
    }

}
