package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.math.*;
import java.util.*;

import org.json.*;

import aprove.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.IntegerRelationType.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Calls.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import immutables.*;

/**
 * Information about the relation of to variables, e.g. a4 op a5, where op \in
 * {<. \le, >, \ge, =, \not= }
 * @author christian
 */
public class JBCIntegerRelation implements IntegerInformation, Immutable {

    /**
     * Abstract integer (that is, possibly a range of values) used on
     * the left side of this relation. Is null iff leftIntegerRef
     * is set.
     */
    private final LiteralInt leftInteger;

    /**
     * Reference to an abstract integer (that is, possibly a range of
     * values) used on the left side of this relation. Is null iff
     * leftInteger is set.
     */
    private final AbstractVariableReference leftIntegerRef;

    /**
     * Type of relation of these two integers.
     */
    private final IntegerRelationType relation;

    /**
     * Abstract integer (that is, possibly a range of values) used on
     * the right side of this relation. Is null iff rightIntegerRef
     * is set.
     */
    private final LiteralInt rightInteger;

    /**
     * Reference to an abstract integer (that is, possibly a range of
     * values) used on the right side of this relation. Is null iff
     * rightInteger is set.
     */
    private final AbstractVariableReference rightIntegerRef;

    /**
     * @param leftIntRef a reference to the {@link AbstractInt} used on
     *  the left side of this relation.
     * @param rel relation of these two {@link AbstractInt} objects.
     * @param rightIntRef a reference to the {@link AbstractInt} used
     *  on the right side of this relation.
     */
    public JBCIntegerRelation(
        final AbstractVariableReference leftIntRef,
        final IntegerRelationType rel,
        final AbstractVariableReference rightIntRef)
    {
        assert (leftIntRef != null && rightIntRef != null) : "Integer relation with lhs/rhs of NULL";
        assert leftIntRef.pointsToAnyIntegerType();
        assert rightIntRef.pointsToAnyIntegerType();
        this.leftIntegerRef = leftIntRef;
        this.leftInteger = null;
        this.rightIntegerRef = rightIntRef;
        this.rightInteger = null;
        this.relation = rel;
    }

    /**
     * @param leftIntRef a reference to the {@link AbstractInt} used on the left
     * side of this relation.
     * @param rel relation of these two {@link AbstractInt} objects.
     * @param rightInt BigInteger used on the right side of this relation.
     */
    public JBCIntegerRelation(
        final AbstractVariableReference leftIntRef,
        final IntegerRelationType rel,
        final BigInteger rightInt)
    {
        this(leftIntRef, rel, AbstractInt.create(rightInt));
    }

    /**
     * @param leftIntRef a reference to the {@link AbstractInt} used on
     *  the left side of this relation.
     * @param rel relation of these two {@link AbstractInt} objects.
     * @param rightInt (Java) integer used on the right side of
     *  this relation.
     */
    public JBCIntegerRelation(final AbstractVariableReference leftIntRef, final IntegerRelationType rel, final int rightInt)
    {
        this(leftIntRef, rel, AbstractInt.create(rightInt));
    }

    /**
     * @param leftIntRef a reference to the {@link AbstractInt} used on
     *  the left side of this relation.
     * @param rel relation of these two {@link AbstractInt} objects.
     * @param rightInt {@link AbstractInt} used on the right side of
     *  this relation.
     */
    public JBCIntegerRelation(
        final AbstractVariableReference leftIntRef,
        final IntegerRelationType rel,
        final LiteralInt rightInt)
    {
        assert leftIntRef.pointsToAnyIntegerType();
        this.leftIntegerRef = leftIntRef;
        this.leftInteger = null;
        this.rightIntegerRef = null;
        this.rightInteger = rightInt;
        this.relation = rel;
        assert (this.leftIntegerRef != null && this.rightInteger != null) : "Integer relation with lhs/rhs of NULL";
    }

    /**
     * @param leftInt {@link AbstractInt} used on the left side of
     *  this relation.
     * @param rel relation of these two {@link AbstractInt} objects.
     * @param rightIntRef a reference to the {@link AbstractInt} used on
     *  the right side of this relation.
     */
    public JBCIntegerRelation(
        final LiteralInt leftInt,
        final IntegerRelationType rel,
        final AbstractVariableReference rightIntRef)
    {
        this.leftIntegerRef = null;
        this.leftInteger = leftInt;
        this.rightIntegerRef = rightIntRef;
        this.rightInteger = null;
        this.relation = rel;
        assert (this.leftInteger != null && this.rightIntegerRef != null) : "Integer relation with lhs/rhs of NULL";
    }

    /**
     * @param leftInt {@link AbstractInt} used on the left side of
     *  this relation.
     * @param rel relation of these two {@link AbstractInt} objects.
     * @param rightInt {@link AbstractInt} used on the right side of
     *  this relation.
     */
    private JBCIntegerRelation(final LiteralInt leftInt, final IntegerRelationType rel, final LiteralInt rightInt) {
        this.leftIntegerRef = null;
        this.leftInteger = leftInt;
        this.rightIntegerRef = null;
        this.rightInteger = rightInt;
        this.relation = rel;
        assert (this.leftInteger != null && this.rightInteger != null) : "Integer relation with lhs/rhs of NULL";
    }

    /** {@inheritDoc} */
    @Override
    public boolean concernsInterestingRef(
        @SuppressWarnings("unchecked") final Set<AbstractVariableReference>... interestingRefs)
    {
        for (final Set<AbstractVariableReference> refSet : interestingRefs) {
            if (refSet == null || refSet.contains(this.leftIntegerRef) || refSet.contains(this.rightIntegerRef)) {
                return true;
            }
        }
        return false;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final JBCIntegerRelation other = (JBCIntegerRelation) obj;
        if (this.leftInteger == null) {
            if (other.leftInteger != null) {
                return false;
            }
        } else if (!this.leftInteger.equals(other.leftInteger)) {
            return false;
        }
        if (this.rightInteger == null) {
            if (other.rightInteger != null) {
                return false;
            }
        } else if (!this.rightInteger.equals(other.rightInteger)) {
            return false;
        }
        if (this.leftIntegerRef == null) {
            if (other.leftIntegerRef != null) {
                return false;
            }
        } else if (!this.leftIntegerRef.equals(other.leftIntegerRef)) {
            return false;
        }
        if (this.relation == null) {
            if (other.relation != null) {
                return false;
            }
        } else if (!this.relation.equals(other.relation)) {
            return false;
        }
        if (this.rightIntegerRef == null) {
            if (other.rightIntegerRef != null) {
                return false;
            }
        } else if (!this.rightIntegerRef.equals(other.rightIntegerRef)) {
            return false;
        }
        return true;
    }

    /**
     * Note: This may return null if the left side of the relation is stored
     * as reference to an {@link AbstractInt} (and not as the actual value).
     * Check with leftIntegerIsRef() if this is the case.
     * @return The {@link AbstractInt} used on the left side of this relation.
     */
    public AbstractInt getLeftInt() {
        if (Globals.useAssertions) {
            assert (this.leftIntegerIsNoRef());
        }
        return this.leftInteger;
    }

    /**
     * @return A reference to the integer used on the left side of this relation.
     */
    public AbstractVariableReference getLeftIntRef() {
        return this.leftIntegerRef;
    }

    /**
     * @return Type of relation of these two integers.
     */
    public IntegerRelationType getRelationType() {
        return this.relation;
    }

    /**
     * Note: This may return null if the right side of the relation is stored
     * as reference to an {@link AbstractInt} (and not as the actual value).
     * Check with rightIntegerIsRef() if this is the case.
     * @return The {@link AbstractInt} used on the right side of this relation.
     */
    public AbstractInt getRightInt() {
        if (Globals.useAssertions) {
            assert (this.rightIntegerIsNoRef());
        }
        return this.rightInteger;
    }

    /**
     * Note: This may return null if the right side of the relation is stored
     * as {@link AbstractInt} (and not as a state-dependent reference to one).
     * Check with rightIntegerIsRef() if this is the case.
     * @return A reference to the integer used on the right side of this relation.
     */
    public AbstractVariableReference getRightIntRef() {
        if (Globals.useAssertions) {
            assert (!this.rightIntegerIsNoRef());
        }
        return this.rightIntegerRef;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.leftInteger == null) ? 0 : this.leftInteger.hashCode());
        result = prime * result + ((this.rightInteger == null) ? 0 : this.rightInteger.hashCode());
        result = prime * result + ((this.leftIntegerRef == null) ? 0 : this.leftIntegerRef.hashCode());
        result = prime * result + ((this.relation == null) ? 0 : this.relation.hashCode());
        result = prime * result + ((this.rightIntegerRef == null) ? 0 : this.rightIntegerRef.hashCode());
        return result;
    }

    /**
     * @return true iff the left side of this relation is stored as an
     *  {@link AbstractInt}.
     */
    public boolean leftIntegerIsNoRef() {
        return this.leftInteger != null;
    }

    /**
     * @return a mirrored version of this relation (ie, if this is a < b,
     *  the returned relation is b > a).
     */
    public JBCIntegerRelation mirror() {
        if (this.leftIntegerIsNoRef()) {
            if (this.rightIntegerIsNoRef()) {
                return new JBCIntegerRelation(this.rightInteger, this.relation.mirror(), this.leftInteger);
            } else {
                return new JBCIntegerRelation(this.rightIntegerRef, this.relation.mirror(), this.leftInteger);
            }
        } else {
            if (this.rightIntegerIsNoRef()) {
                return new JBCIntegerRelation(this.rightInteger, this.relation.mirror(), this.leftIntegerRef);
            } else {
                return new JBCIntegerRelation(this.rightIntegerRef, this.relation.mirror(), this.leftIntegerRef);
            }
        }
    }

    /**
     * @return true iff the right side of this relation is stored as an
     *  {@link AbstractInt}.
     */
    public boolean rightIntegerIsNoRef() {
        return this.rightInteger != null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public SMTLIBTheoryAtom toSMTAtom(final String varPrefix) {
        final SMTLIBIntValue leftValue;
        if (this.leftInteger != null) {
            leftValue = this.leftInteger.toSMTIntValue();
        } else {
            leftValue = this.leftIntegerRef.toSMTIntValue(varPrefix);
        }
        final SMTLIBIntValue rightValue;
        if (this.rightInteger != null) {
            rightValue = this.rightInteger.toSMTIntValue();
        } else {
            rightValue = this.rightIntegerRef.toSMTIntValue(varPrefix);
        }

        return this.relation.toSMTAtom(leftValue, rightValue);
    }

    /**
     * @return String representation of this relation.
     */
    @Override
    public String toString() {
        final StringBuilder s = new StringBuilder();
        s.append(this.leftIntegerRef);
        s.append(this.relation.toString());
        if (this.rightIntegerIsNoRef()) {
            s.append(this.rightInteger);
        } else {
            s.append(this.rightIntegerRef);
        }
        return s.toString();
    }

    public JBCIntegerRelation toStrict() {
        switch (relation) {
            case EQ:
            case NE:
                return this;
            default:
                if (leftIntegerIsNoRef()) {
                    return new JBCIntegerRelation(leftInteger, relation.toStrict(), rightIntegerRef);
                } else if (rightIntegerIsNoRef()) {
                    return new JBCIntegerRelation(leftIntegerRef, relation.toStrict(), rightInteger);
                } else {
                    return new JBCIntegerRelation(leftIntegerRef, relation.toStrict(), rightIntegerRef);
                }
        }
    }

    public JBCIntegerRelation as(IntegerRelationType type) {
        if (leftIntegerIsNoRef()) {
            return new JBCIntegerRelation(leftInteger, type, rightIntegerRef);
        } else if (rightIntegerIsNoRef()) {
            return new JBCIntegerRelation(leftIntegerRef, type, rightInteger);
        } else {
            return new JBCIntegerRelation(leftIntegerRef, type, rightIntegerRef);
        }
    }

    public String toSExpString() {
        final StringBuilder s = new StringBuilder();
        s.append("(");
        s.append(this.relation.toString());
        if (this.leftInteger != null) {
            s.append(this.leftInteger.toSMTIntValue());
        } else {
            s.append(this.leftIntegerRef.toSMTIntValue(""));
        }
        s.append(" ");
        if (this.rightInteger != null) {
            s.append(this.rightInteger.toSMTIntValue());
        } else {
            s.append(this.rightIntegerRef.toSMTIntValue(""));
        }
        s.append(")");
        return s.toString();
    }

    public JBCIntegerRelation toNonStrict() {
        switch (relation) {
            case EQ:
            case NE:
                return this;
            default:
                if (leftIntegerIsNoRef()) {
                    return new JBCIntegerRelation(leftInteger, relation.toNonStrict(), rightIntegerRef);
                } else if (rightIntegerIsNoRef()) {
                    return new JBCIntegerRelation(leftIntegerRef, relation.toNonStrict(), rightInteger);
                } else {
                    return new JBCIntegerRelation(leftIntegerRef, relation.toNonStrict(), rightIntegerRef);
                }
        }
    }

    public boolean isStrict() {
        return relation.isStrict();
    }

    public JBCIntegerRelation invert() {
        if (this.leftIntegerIsNoRef()) {
            if (this.rightIntegerIsNoRef()) {
                return new JBCIntegerRelation(this.leftInteger, this.relation.invert(), this.rightInteger);
            } else {
                return new JBCIntegerRelation(this.leftInteger, this.relation.invert(), this.rightIntegerRef);
            }
        } else if (this.rightIntegerIsNoRef()) {
            return new JBCIntegerRelation(this.leftIntegerRef, this.relation.invert(), this.rightInteger);
        } else {
            return new JBCIntegerRelation(this.leftIntegerRef, this.relation.invert(), this.rightIntegerRef);
        }
    }

    @SuppressWarnings({ "rawtypes", "unchecked" })
    public SMTExpression<SBool> toSMTExp() {
        List<SMTExpression<SInt>> args = new LinkedList<>();
        if (leftIntegerIsNoRef()) {
            AbstractInt left = getLeftInt();
            if (left.isIntLiteral()) {
                args.add(new IntConstant(left.getLiteral()));
            } else {
                throw new RuntimeException("an integer relation should relate AVRs and/or constants");
            }
        } else {
            args.add(new NamedSymbol0<SInt>(SInt.representative, leftIntegerRef.toString()));
        }
        if (rightIntegerIsNoRef()) {
            AbstractInt right = getRightInt();
            if (right.isIntLiteral()) {
                args.add(new IntConstant(right.getLiteral()));
            } else {
                throw new RuntimeException("an integer relation should relate AVRs and/or constants");
            }
        } else {
            args.add(new NamedSymbol0<SInt>(SInt.representative, rightIntegerRef.toString()));
        }
        try {
            return new ChainableCall(relation.toChainableSymbol(), ImmutableCreator.create(args));
        } catch (NotChainableException e) {
            // its not chainable - try the inverse
        }
        try {
            return new Call1<SBool, SBool>(Symbol1.Not, new ChainableCall(relation.invert().toChainableSymbol(), ImmutableCreator.create(args)));
        } catch (NotChainableException e1) {
            assert false;
            return null;
        }
    }

    /** @return true iff the left side as well as the right side is not a constant */
    public boolean justVariables() {
        return (leftIntegerRef != null && !leftIntegerRef.pointsToConstant()) && (rightIntegerRef != null && !rightIntegerRef.pointsToConstant());
    }

    /** @return true iff the left side equals the right side */
    public boolean leftEqRight() {
        return (leftInteger != null && leftInteger.equals(rightInteger)) || (leftIntegerRef != null && leftIntegerRef.equals(rightIntegerRef));
    }

    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Information Type", "Integer Relation Established");
        res.put("Relation", this.toSExpString());
        return res;
    }
}
