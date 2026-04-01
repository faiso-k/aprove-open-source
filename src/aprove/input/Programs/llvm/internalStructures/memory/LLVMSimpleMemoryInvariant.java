package aprove.input.Programs.llvm.internalStructures.memory;

import java.math.BigInteger;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import aprove.Globals;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.states.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class LLVMSimpleMemoryInvariant implements LLVMMemoryInvariant {

    final private LLVMSimpleTerm pointedTo;

    public LLVMSimpleMemoryInvariant(LLVMSimpleTerm res) {
        this.pointedTo = res;
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
        LLVMSimpleMemoryInvariant other = (LLVMSimpleMemoryInvariant)obj;
        if (this.pointedTo == null) {
            if (other.pointedTo != null) {
                return false;
            }
        } else if (!this.pointedTo.equals(other.pointedTo)) {
            return false;
        }
        return true;
    }

    public LLVMSimpleTerm getPointedToValue() {
        assert (this.isSimple());
        return this.pointedTo;
    }

    @Override
    public Set<LLVMSymbolicVariable> getUsedReferences() {
        Set<LLVMSymbolicVariable> res = new LinkedHashSet<LLVMSymbolicVariable>();
        LLVMSimpleTerm value = this.getPointedToValue();
        if (value instanceof LLVMSymbolicVariable) {
            res.add((LLVMSymbolicVariable)value);
        }
        return res;
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.pointedTo == null) ? 0 : this.pointedTo.hashCode());
        return result;
    }
    
    public boolean isPositive(LLVMAbstractState state, Abortion aborter) {
        return state.checkIfPositive(this.pointedTo, aborter).x;
    }

    @Override
    public boolean isSimple() {
        // has to be changed as soon as we use more info than resTemplate
        return true;
    }

    @Override
    public Pair<LLVMMemoryInvariant, ? extends LLVMAbstractState> joinInvariant(
        LLVMAbstractState state,
        LLVMMemoryInvariant other,
        Abortion aborter
    ) {
        if (other instanceof LLVMSimpleMemoryInvariant) {
            LLVMSimpleMemoryInvariant simp = (LLVMSimpleMemoryInvariant)other;
            final Pair<Boolean, ? extends LLVMAbstractState> sameValue =
                state.checkRelation(this.pointedTo, IntegerRelationType.EQ, simp.getPointedToValue(), aborter);
            if (sameValue.x) {
                return new Pair<LLVMMemoryInvariant, LLVMAbstractState>(this, sameValue.y);
            }
            return this.generalizing_join(sameValue.y, simp, aborter);
        }
        if (other instanceof LLVMIntervalMemoryInvariant) {
            return other.joinInvariant(state, this, aborter);
        }
        if (other instanceof LLVMComplexMemoryInvariant) {
            LLVMComplexMemoryInvariant complex = (LLVMComplexMemoryInvariant) other;
            // if this = v49 and other = (v44..v;x), and there is a relation v49 = v44 - x,
            // then create (v49..v;x)
            LLVMSimpleTerm v49 = this.getPointedToValue();
            LLVMSimpleTerm v44 = ((LLVMComplexMemoryInvariant)other).getFirstValue();
            LLVMSimpleTerm x = null;
            LLVMTerm v44Minusx = null;
            LLVMRelation rel = null;
            if (complex.getChange().getLinearRate() != null) {
                x = state.getRelationFactory().getTermFactory().constant(complex.getChange().getLinearRate());
            }
            if (x != null) {
                v44Minusx = state.getRelationFactory().getTermFactory().sub(v44, x);
            }
            if (v44Minusx != null) {
                rel = state.getRelationFactory().createRelation(IntegerRelationType.EQ, v49, v44Minusx);
            }
            LLVMComplexMemoryInvariant newInv = null;
            if (rel != null && state.checkRelation(rel, aborter).x) {
                newInv = new LLVMComplexMemoryInvariant(v49, complex.getLastValue(), complex.getChange(), complex.getType());
            }
            if (newInv == null) {
                if (complex.getChange().getSortedType() != LLVMSortedType.UNSORTED) {
                    LLVMSortedType sortedType = LLVMSortedType.UNSORTED;
                    if (complex.getChange().getSortedType() == LLVMSortedType.ASCENDING) {
                        if (state.checkRelation(state.getRelationFactory().lessThan(v49, v44), aborter).x) {
                            sortedType = LLVMSortedType.ASCENDING;
                        } else if (state.checkRelation(state.getRelationFactory().lessThanEquals(v49, v44), aborter).x) {
                            sortedType = LLVMSortedType.NONDESCENDING;
                        }
                    } else if (complex.getChange().getSortedType() == LLVMSortedType.DESCENDING) {
                        if (state.checkRelation(state.getRelationFactory().lessThan(v44, v49), aborter).x) {
                            sortedType = LLVMSortedType.DESCENDING;
                        } else if (state.checkRelation(state.getRelationFactory().lessThanEquals(v44, v49), aborter).x) {
                            sortedType = LLVMSortedType.NONASCENDING;
                        }
                    } else if (complex.getChange().getSortedType() == LLVMSortedType.NONASCENDING) {
                        if (state.checkRelation(state.getRelationFactory().lessThanEquals(v44, v49), aborter).x) {
                            sortedType = LLVMSortedType.NONASCENDING;
                        }
                    } else if (complex.getChange().getSortedType() == LLVMSortedType.NONDESCENDING) {
                        if (state.checkRelation(state.getRelationFactory().lessThanEquals(v49, v44), aborter).x) {
                            sortedType = LLVMSortedType.NONDESCENDING;
                        }
                    }
                    newInv = complex.havoc(v49, complex.getLastValue(), sortedType);
                } else {
                    newInv = complex.havoc(v49, complex.getLastValue(), LLVMSortedType.UNSORTED);
                }
            }
            return new Pair<LLVMMemoryInvariant, LLVMAbstractState>(newInv, state);
        }
        return new Pair<LLVMMemoryInvariant, LLVMAbstractState>(null, state);
    }

    @Override
    public Pair<LLVMSimpleTerm, LLVMAbstractState> load(
        LLVMAbstractState state,
        LLVMSimpleTerm ptr,
        LLVMType targetType,
        boolean unsigned,
        Abortion aborter
    ) {
        return new Pair<LLVMSimpleTerm, LLVMAbstractState>(this.getPointedToValue(), state);
    }

    @Override
    public Pair<Boolean, ? extends LLVMAbstractState> mayShareWith(LLVMMemoryInvariant other, LLVMAbstractState state, Abortion aborter) {
        if (Globals.useAssertions) {
            assert (this.isSimple()) : "This invariant should be simple!";
        }
        if (other instanceof LLVMSimpleMemoryInvariant) {
            final Pair<Boolean, ? extends LLVMAbstractState> res =
                state.checkRelation(
                    this.pointedTo,
                    IntegerRelationType.NE,
                    ((LLVMSimpleMemoryInvariant)other).getPointedToValue(),
                    aborter
                );
            res.x = !res.x;
            return res;
        }
        if (other instanceof LLVMIntervalMemoryInvariant) {
            return other.mayShareWith(this, state, aborter);
        }
        return new Pair<Boolean, LLVMAbstractState>(true, state);
    }

    @Override
    public LLVMMemoryInvariant replaceReference(LLVMSimpleTerm old_ref, LLVMSimpleTerm new_ref) {
        if (this.pointedTo.equals(old_ref)) {
            if (new_ref instanceof LLVMSymbolicVariable) {
                return new LLVMSimpleMemoryInvariant(new_ref);
            }
            throw new IllegalArgumentException("Cannot replace template variable by a constant!");
        }
        return this;
    }

    @Override
    public LLVMMemoryInvariant replaceReferences(Map<? extends LLVMSimpleTerm, ? extends LLVMSimpleTerm> replacements) {
        if (replacements.containsKey(this.getPointedToValue())) {
            return this.replaceReference(this.getPointedToValue(), replacements.get(this.getPointedToValue()));
        }
        return this;
    }

    public LLVMIntervalMemoryInvariant to_interval_invariant(LLVMAbstractState state) {
        final LLVMTermFactory termFactory = state.getRelationFactory().getTermFactory();
        LLVMSimpleTerm ref = this.getPointedToValue();
        if (ref instanceof LLVMConstant) {
            return new LLVMIntervalMemoryInvariant((LLVMConstant)ref, (LLVMConstant)ref);
        }
        LLVMConstant otherLower = null;
        LLVMConstant otherUpper = null;
        for (LLVMRelation rel : state.getValueRelations((LLVMSymbolicVariable)ref)) {
            if (rel.isEquation()) {
                if (rel.getLhs().equals(ref)) {
                    otherLower = (LLVMConstant)rel.getRhs();
                } else {
                    otherLower = (LLVMConstant)rel.getLhs();
                }
                otherUpper = otherLower;
                break;
            }
            if (rel.isDirectedInequality()) {
                final LLVMConstant c;
                final boolean greater;
                if (rel.getLhs().equals(ref)) {
                    switch (rel.getRelationType()) {
                        case LE:
                            greater = false;
                            c = (LLVMConstant)rel.getRhs();
                            break;
                        case LT:
                            greater = false;
                            c =
                                termFactory.constant(
                                    ((LLVMConstant)rel.getRhs()).getIntegerValue().subtract(BigInteger.ONE)
                                );
                            break;
                        case GE:
                            greater = true;
                            c = (LLVMConstant)rel.getRhs();
                            break;
                        case GT:
                            greater = true;
                            c =
                                termFactory.constant(
                                    ((LLVMConstant)rel.getRhs()).getIntegerValue().add(BigInteger.ONE)
                                );
                            break;
                        default:
                            throw new IllegalStateException("Some found a new directed inequality!");
                    }
                } else {
                    switch (rel.getRelationType()) {
                        case LE:
                            greater = true;
                            c = (LLVMConstant)rel.getLhs();
                            break;
                        case LT:
                            greater = true;
                            c =
                                termFactory.constant(
                                    ((LLVMConstant)rel.getLhs()).getIntegerValue().add(BigInteger.ONE)
                                );
                            break;
                        case GE:
                            greater = false;
                            c = (LLVMConstant)rel.getLhs();
                            break;
                        case GT:
                            greater = false;
                            c =
                                termFactory.constant(
                                    ((LLVMConstant)rel.getLhs()).getIntegerValue().subtract(BigInteger.ONE)
                                );
                            break;
                        default:
                            throw new IllegalStateException("Some found a new directed inequality!");
                    }
                }
                if (greater) {
                    otherLower = IntegerUtils.max(otherLower, c, false);
                } else {
                    otherUpper = IntegerUtils.min(otherUpper, c, true);
                }
            } else {
                // we must have an undirected inequality
                final LLVMConstant c;
                if (rel.getLhs().equals(ref)) {
                    c = (LLVMConstant)rel.getRhs();
                } else {
                    c = (LLVMConstant)rel.getLhs();
                }
                if (c.equals(otherLower)) {
                    otherLower = termFactory.constant(c.getIntegerValue().add(BigInteger.ONE));
                }
                if (c.equals(otherUpper)) {
                    otherUpper = termFactory.constant(c.getIntegerValue().subtract(BigInteger.ONE));
                }
            }
        }
        if (
            otherLower != null
            && otherUpper != null
            && otherLower.getIntegerValue().compareTo(otherUpper.getIntegerValue()) > 0
        ) {
            throw new IllegalStateException("Inconsistent value information detected!");
        }
        return new LLVMIntervalMemoryInvariant(otherLower, otherUpper);
    }

    @Override
    public String toString() {
        return "Inv[" + this.pointedTo + "]";
    }

    @Override
    public boolean usesReference(LLVMSimpleTerm other) {
        return this.pointedTo.equals(other);
    }

    private Pair<LLVMMemoryInvariant, ? extends LLVMAbstractState> generalizing_join(
        LLVMAbstractState state,
        LLVMSimpleMemoryInvariant other,
        Abortion aborter
    ) {
        LLVMMemoryInvariant inv = this.to_interval_invariant(state);
        if (inv != null) {
            return inv.joinInvariant(state, other, aborter);
        }
        return new Pair<LLVMMemoryInvariant, LLVMAbstractState>(null, state);
    }

}
