package aprove.input.Programs.llvm.internalStructures.memory;

import java.math.BigInteger;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.states.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * This class represents a range on the heap (used to describe where a given invariant holds).
 * Note that a MemoryRange [fromRef,toRef] imlies that at toRef, a pointer is stored.
 * Thus, a MemoryRange [fromRef,toRef] must be contained in a allocation at least of the dimension [fromRef,toRef+pointer size-1]
 * @author Cornelius Aschermann, cryingshadow
 */
public class LLVMMemoryRange implements DOTStringAble, Immutable {

    /**
     * @param state
     * @param a
     * @param b
     * @return A memory range and a state. The memory range is [a.min,b.max] if range a is left of b and are adjacent
     *         and of the same type and null otherwise. The state is the specified one possibly updated during the
     *         association checks.
     */
    public static Pair<LLVMMemoryRange, LLVMAbstractState> mergeLeft(
        LLVMAbstractState state,
        LLVMMemoryRange a,
        LLVMMemoryRange b,
        Abortion aborter
    ) {
        return LLVMMemoryRange.merge(LLVMMemoryRange.isCompatible(state, a, b, aborter), a, b, aborter);
    }

    /**
     * @param state
     * @param a
     * @param b
     * @return A memory range and a state. The memory range is [a.min,b.max] if range a is right of b and are adjacent
     *         and of the same type and null otherwise. The state is the specified one possibly updated during the
     *         association checks.
     */
    public static Pair<LLVMMemoryRange, LLVMAbstractState> mergeRight(
        LLVMAbstractState state,
        LLVMMemoryRange a,
        LLVMMemoryRange b,
        Abortion aborter
    ) {
        return LLVMMemoryRange.merge(LLVMMemoryRange.isCompatible(state, a, b, aborter), b, a, aborter);
    }

    /**
     * @param state
     * @param a
     * @param b
     * @return true if we can prove that in the given state the upper bound of a is equal to the lower bound of b
     */
    private static Pair<Boolean, ? extends LLVMAbstractState> isAtLeftBorderOf(
        LLVMAbstractState state,
        LLVMMemoryRange a,
        LLVMMemoryRange b,
        Abortion aborter
    ) {
        final LLVMRelationFactory relationFactory = state.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        final Pair<Boolean, ? extends LLVMAbstractState> equalBounds =
            state.checkRelation(relationFactory.equalTo(a.toRef, b.fromRef), aborter);
        if (equalBounds.x) {
            return equalBounds;
        }
        BigInteger bytesize = BigInteger.valueOf(IntegerUtils.bitsToBytes(a.getType().size()));
        return
            equalBounds.y.checkRelation(
                relationFactory.equalTo(termFactory.add(a.toRef, termFactory.constant(bytesize)), b.fromRef),
                aborter
            );
    }

    /**
     * @param state
     * @param a
     * @param b
     * @return A flag and a state. The flag is true if a and b are both different heap ranges from the same allocation
     *         and have the same type. The state is the specified state possibly updated during the association checks.
     */
    private static Pair<Boolean, LLVMAbstractState> isCompatible(
        LLVMAbstractState state,
        LLVMMemoryRange a,
        LLVMMemoryRange b,
        Abortion aborter
    ) {
        if (a == b || !a.getType().equals(b.getType())) {
            return new Pair<Boolean, LLVMAbstractState>(false, state);
        }
        final Pair<LLVMAssociationIndex, LLVMAbstractState> indexPair =
            state.getAssociatedAllocationIndex(
                a.fromRef,
                LLVMPointerType.i8star(state.getModule().getPointerSize()),
                false,
                aborter
            );
        if (indexPair.x == null) {
            return new Pair<Boolean, LLVMAbstractState>(false, indexPair.y);
        }
        final Pair<LLVMAssociationIndex, LLVMAbstractState> secondIndexPair =
            indexPair.y.getAssociatedAllocationIndex(
                b.fromRef,
                LLVMPointerType.i8star(state.getModule().getPointerSize()),
                false,
                aborter
            );
        if (secondIndexPair.x == null) {
            return new Pair<Boolean, LLVMAbstractState>(false, secondIndexPair.y);
        }
        return new Pair<Boolean, LLVMAbstractState>(indexPair.x.x.equals(secondIndexPair.x.x), secondIndexPair.y);
    }

    /**
     * @param compatible
     * @param a
     * @param b
     * @return A memory range and a state. The memory range is [a.min,b.max] if range a is left of b and are adjacent
     *         and of the same type and null otherwise. The state is the specified one possibly updated during the
     *         association checks.
     */
    private static Pair<LLVMMemoryRange, LLVMAbstractState> merge(
        Pair<Boolean, LLVMAbstractState> compatible,
        LLVMMemoryRange a,
        LLVMMemoryRange b,
        Abortion aborter
    ) {
        if (compatible.x) {
            final Pair<Boolean, ? extends LLVMAbstractState> atLeft =
                LLVMMemoryRange.isAtLeftBorderOf(compatible.y, a, b, aborter);
            if (atLeft.x) {
                return
                    new Pair<LLVMMemoryRange, LLVMAbstractState>(
                        new LLVMMemoryRange(a.fromRef, b.toRef, a.getType(), a.getUnsigned()),
                        atLeft.y
                    );
            }
            return new Pair<LLVMMemoryRange, LLVMAbstractState>(null, atLeft.y);
        }
        return new Pair<LLVMMemoryRange, LLVMAbstractState>(null, compatible.y);
    }
    
    
    public Pair<Boolean, ? extends LLVMAbstractState> isContainedInAllocation(LLVMAbstractState state, LLVMAllocation alloction, Abortion aborter) {
    	final LLVMRelationFactory relationFactory = state.getRelationFactory();
    	final Pair<Boolean, ? extends LLVMAbstractState> lowerBoundResult =
                state.checkRelation(relationFactory.lessThanEquals(alloction.x, fromRef), aborter);
    	if(lowerBoundResult.x) {
    		state = lowerBoundResult.y;
    		LLVMTermFactory termFactory = state.getRelationFactory().getTermFactory();
    		final LLVMConstant offset = termFactory.constant(BigInteger.valueOf(IntegerUtils.bitsToBytes(type.size()) - 1));
    		final Pair<Boolean, ? extends LLVMAbstractState> upperBoundResult =
                    state.checkRelation(relationFactory.lessThanEquals(termFactory.add(toRef, offset), alloction.y), aborter);
    		
    		return upperBoundResult;
    	}
    	
    	return lowerBoundResult;
    }

    /**
     * references that represent the upper and lower bound of the range
     */
    private final LLVMSimpleTerm fromRef;

    private final LLVMSimpleTerm toRef;

    //The type that is stored, e.g. i32 if a value of type i32 is obtained when dereferencing fromRef, toRef, or the addresses in between
    private final LLVMType type;

    private final boolean unsigned;

    public LLVMMemoryRange(LLVMSimpleTerm from, LLVMSimpleTerm to, LLVMType ptr_type, boolean unsigned) {
        if (Globals.useAssertions) {
            assert (from != null) : "The lower bound must not be null!";
            assert (to != null) : "The upper bound must not be null!";
        }
        this.fromRef = from;
        this.toRef = to;
        this.type = ptr_type;
        this.unsigned = unsigned;
    }

    public boolean equalBounds(LLVMMemoryRange otherRange) {
        // FIXME This looks really dangerous... Are you sure that == is the right way to compare the bounds here?
        return this.fromRef == otherRange.getFromRef() && this.toRef == otherRange.getToRef();
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        LLVMMemoryRange other = (LLVMMemoryRange)obj;
        if (this.fromRef == null) {
            if (other.fromRef != null) {
                return false;
            }
        } else if (!this.fromRef.equals(other.fromRef)) {
            return false;
        }
        if (this.toRef == null) {
            if (other.toRef != null) {
                return false;
            }
        } else if (!this.toRef.equals(other.toRef)) {
            return false;
        }
        if (this.type == null) {
            if (other.type != null) {
                return false;
            }
        } else if (!this.type.equals(other.type)) {
            return false;
        }
        return true;
    }

    public LLVMSimpleTerm getFromRef() {
        return this.fromRef;
    }

    public LLVMSimpleTerm getToRef() {
        return this.toRef;
    }

    public LLVMType getType() {
        return this.type;
    }

    public boolean getUnsigned() {
        return this.unsigned;
    }
    
    

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.fromRef == null) ? 0 : this.fromRef.hashCode());
        result = prime * result + ((this.toRef == null) ? 0 : this.toRef.hashCode());
        result = prime * result + ((this.type == null) ? 0 : this.type.hashCode());
        return result;
    }

    public boolean isPointwise() {
        return this.fromRef.equals(this.toRef);
    }

    public LLVMMemoryRange replaceReference(LLVMSimpleTerm old, LLVMSimpleTerm replacement) {
        LLVMSimpleTerm new_lower = this.getFromRef();
        LLVMSimpleTerm new_upper = this.getFromRef();
        boolean replaced = false;
        if (new_lower == old) {
            new_lower = replacement;
            replaced = true;
        }
        if (new_upper == old) {
            new_upper = replacement;
            replaced = true;
        }
        if (!replaced) {
            return null;
        }
        return new LLVMMemoryRange(new_lower, new_upper, this.getType(), this.getUnsigned());
    }

    @Override
    public String toDOTString() {
        if (this.fromRef == this.toRef) {
            return "[" + this.fromRef.toDOTString() + "|" + this.type.toString() + "]";
        }
        return "[" + this.fromRef.toDOTString() + "," + this.toRef.toDOTString() + "|" + this.type.toString() + "]";
    }

    @Override
    public String toString() {
        if (this.fromRef == this.toRef) {
            return "[" + this.fromRef.toDOTString() + "]";
        }
        return "[" + this.fromRef.toDOTString() + "," + this.toRef.toDOTString() + "]";
    }

}
