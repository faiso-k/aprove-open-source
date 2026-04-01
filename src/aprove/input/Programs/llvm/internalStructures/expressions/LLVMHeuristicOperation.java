package aprove.input.Programs.llvm.internalStructures.expressions;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.AbstractBoundedInt.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Represents a binary operation like add, and, subtract, multiply, ...
 * @author Janine Repke, Marc Brockschmidt, cryingshadow
 */
public class LLVMHeuristicOperation extends LLVMOperation implements LLVMHeuristicTerm {

    /**
     * Creates an operation. Should not be used outside of factory methods (this is why it is package private).
     * @param op Type of the (binary) operation. May never be null.
     * @param l Left-hand side of this (binary) operation. May never be null.
     * @param r Right-hand side of this (binary) operation. May never be null.
     */
    LLVMHeuristicOperation(ArithmeticOperationType op, LLVMHeuristicTerm l, LLVMHeuristicTerm r) {
        super(op, l, r);
    }

    @Override
    public LLVMHeuristicOperation applySubstitution(Map<? extends Variable, ? extends Expression> sigma) {
        return this.applySubstitution(Substitution.toSubstitution(sigma));
    }

    @Override
    public LLVMHeuristicOperation applySubstitution(Substitution sigma) {
        return Substitution.applySubstitution(this, sigma);
    }

    @Override
    public Set<LLVMHeuristicTerm> computeAllSubExpressions() {
        Set<LLVMHeuristicTerm> res = new LinkedHashSet<LLVMHeuristicTerm>(this.getLhs().computeAllSubExpressions());
        res.addAll(this.getRhs().computeAllSubExpressions());
        res.add(this);
        return res;
    }

    @Override
    public BigInteger computeHighestAbsoluteFactor() {
        BigInteger res = BigInteger.ZERO;
        for (LLVMHeuristicTerm literal : this.getLiterals()) {
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linear = literal.toLinear();
            if (linear.x == null) {
                continue;
            }
            res = res.max(linear.z.abs());
        }
        return res;
    }

    @Override
    public boolean equals(Object o) {
        if (o instanceof LLVMHeuristicOperation) {
            LLVMHeuristicOperation other = (LLVMHeuristicOperation) o;
            if (this.getOperation() != other.getOperation()) {
                return false;
            }
            // note that both sides must be non-null
            return
                (this.getLhs().equals(other.getLhs()) && this.getRhs().equals(other.getRhs()))
                || (
                    this.getOperation().isCommutative()
                    && this.getLhs().equals(other.getRhs())
                    && this.getRhs().equals(other.getLhs())
                );
        } else {
            return false;
        }
    }

    @Override
    public AbstractBoundedInt evaluate(Map<LLVMHeuristicVariable, LLVMValue> valueMap, LLVMParameters params)
    throws OverflowException {
        AbstractBoundedInt left = this.getLhs().evaluate(valueMap, params);
        AbstractBoundedInt right = this.getRhs().evaluate(valueMap, params);
        final boolean useBoundedIntegers = params.useBoundedIntegers;
        final boolean handleOverflows = useBoundedIntegers;
        // integers in relations are always mathematical integers
        IntegerType intType = IntegerType.UNBOUND;
        if (left == null || right == null) {
            return null;
        } else {
            boolean sameRef = this.getLhs().equals(this.getRhs());
            switch (this.getOperation()) {
                case ADD:
                    return left.add(right, intType, handleOverflows).x;
                case MUL:
                    return left.mul(right, intType, handleOverflows).x;
                case AND:
                    return left.and(right, sameRef, intType, !useBoundedIntegers);
                case TIDIV:
                    Triple<? extends AbstractBoundedInt, Boolean, Boolean> divRes =
                    left.div(right, sameRef, intType, handleOverflows);
                    return divRes.y ? null : divRes.x;
                case EMOD:
                    Pair<? extends AbstractBoundedInt, Boolean> modRes =
                    left.mod(right, sameRef, intType, handleOverflows);
                    return modRes.y ? null : modRes.x;
                case NEG:
                    throw new IllegalStateException("Found unary operator in binary expression!");
                case OR:
                    return left.or(right, sameRef, intType, !useBoundedIntegers);
                case TMOD:
                    Pair<? extends AbstractBoundedInt, Boolean> remRes =
                        left.rem(right, sameRef, intType, handleOverflows);
                    return remRes.y ? null : remRes.x;
                case SHL:
                    return left.shl(right, intType, !useBoundedIntegers);
                case SHR:
                    return left.shr(right, intType, !useBoundedIntegers);
                case SUB:
                    return left.add(right.negate(intType), intType, handleOverflows).x;
                case UREM:
                    Pair<? extends AbstractBoundedInt, Boolean> uremRes =
                    left.urem(right, sameRef, intType, handleOverflows);
                    return uremRes.y ? null : uremRes.x;
                case USHR:
                    return left.ushr(right, intType, !useBoundedIntegers);
                case XOR:
                    return left.xor(right, sameRef, intType, !useBoundedIntegers);
                default:
                    // we are not able to evaluate this operation
                    return null;
            }
        }
    }

    @Override
    public LLVMHeuristicTerm getLhs() {
        return (LLVMHeuristicTerm)super.getLhs();
    }

    @Override
    public List<LLVMHeuristicTerm> getLiterals() {
        List<LLVMHeuristicTerm> res;
        switch (this.getOperation()) {
        case ADD:
            res = new ArrayList<LLVMHeuristicTerm>();
            res.addAll(this.getLhs().getLiterals());
            res.addAll(this.getRhs().getLiterals());
            return res;
        case SUB:
            res = new ArrayList<LLVMHeuristicTerm>();
            res.addAll(this.getLhs().getLiterals());
            for (LLVMHeuristicTerm literal : this.getRhs().getLiterals()) {
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linear = literal.toLinear();
                if (linear.x == null) {
                    res.add(new LLVMHeuristicConstRef(linear.y.negate()));
                } else {
                    if (Globals.useAssertions && LLVMDebuggingFlags.CHECK_INVARIANTS) {
                        assert (linear.y.compareTo(BigInteger.ZERO) == 0) : "This should be another literal!";
                    }
                    res.add(
                        new LLVMHeuristicOperation(
                            ArithmeticOperationType.MUL,
                            new LLVMHeuristicConstRef(linear.z.negate()),
                            linear.x
                        )
                    );
                }
            }
            return res;
        default:
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linear = this.toLinear();
            if (linear.x == null) {
                return Collections.<LLVMHeuristicTerm>singletonList(new LLVMHeuristicConstRef(linear.y));
            } else if (linear.y.compareTo(BigInteger.ZERO) == 0) {
                if (linear.z.compareTo(BigInteger.ONE) == 0) {
                    return Collections.<LLVMHeuristicTerm>singletonList(linear.x);
                } else {
                    return Collections.<LLVMHeuristicTerm>singletonList(
                        new LLVMHeuristicOperation(
                            ArithmeticOperationType.MUL,
                            new LLVMHeuristicConstRef(linear.z), linear.x)
                    );
                }
            } else if (linear.z.compareTo(BigInteger.ONE) == 0) {
                res = new ArrayList<LLVMHeuristicTerm>();
                res.add(new LLVMHeuristicConstRef(linear.y));
                res.add(linear.x);
                return res;
            } else {
                res = new ArrayList<LLVMHeuristicTerm>();
                res.add(new LLVMHeuristicConstRef(linear.y));
                res.add(
                    new LLVMHeuristicOperation(
                        ArithmeticOperationType.MUL,
                        new LLVMHeuristicConstRef(linear.z),
                        linear.x
                    )
                );
                return res;
            }
        }
    }

    @Override
    public int getNumberOfVarOccs() {
        return this.getLhs().getNumberOfVarOccs() + this.getRhs().getNumberOfVarOccs();
    }

    @Override
    public LLVMHeuristicTerm getRhs() {
        return (LLVMHeuristicTerm)super.getRhs();
    }

    @Override
    public Set<? extends LLVMHeuristicVariable> getVariables() {
        return this.getVariables(true);
    }

    @Override
    public Set<? extends LLVMHeuristicVariable> getVariables(boolean includeConstants) {
        Set<LLVMHeuristicVariable> res =
            new LinkedHashSet<LLVMHeuristicVariable>(this.getLhs().getVariables(includeConstants));
        res.addAll(this.getRhs().getVariables(includeConstants));
        return res;
    }

    @Override
    public boolean isLinear() {
        switch (this.getOperation()) {
            case ADD:
            case SUB:
                return
                    Collections.disjoint(this.getLhs().getVariables(false), this.getRhs().getVariables(false))
                    && this.getLhs().isLinear()
                    && this.getRhs().isLinear();
            case MUL:
                if (this.getLhs() instanceof LLVMHeuristicConstRef) {
                    return this.getRhs().isLinear();
                } else if (this.getRhs() instanceof LLVMHeuristicConstRef) {
                    return this.getLhs().isLinear();
                }
                //$FALL-THROUGH$
            case TIDIV:
                return this.getRhs() instanceof LLVMHeuristicConstRef && this.getLhs().isLinear();
            default:
                return false;
        }
    }

    /**
     * Checks if this is a modulo operation.
     * @return True iff the outer most operator is MOD.
     */
    public boolean isModuloOperation() {
        if (this.getOperation().equals(ArithmeticOperationType.EMOD)) {
            return true;
        }
        return false;
    }
    
    @Override
    public boolean isNegatedVariable() {
        switch (this.getOperation()) {
            case MUL:
                return
                    this.getLhs().equals(new LLVMHeuristicConstRef(BigInteger.ONE.negate()))
                    && this.getRhs() instanceof LLVMHeuristicVarRef;
            default:
                return false;
        }
    }

    @Override
    public boolean isNegative(ImmutableMap<LLVMHeuristicVariable, LLVMValue> values) {
        switch (this.getOperation()) {
            case ADD:
                return
                    (this.getLhs().isNegative(values) && this.getRhs().isNonPositive(values))
                    || (this.getLhs().isNonPositive(values) && this.getRhs().isNegative(values));
            case SUB:
                return
                    (this.getLhs().isNegative(values) && this.getRhs().isNonNegative(values))
                    || (this.getLhs().isNonPositive(values) && this.getRhs().isPositive(values));
            case MUL:
                return
                    (this.getLhs().isNegative(values) && this.getRhs().isPositive(values))
                    || (this.getLhs().isPositive(values) && this.getRhs().isNegative(values));
            default:
                return false;
        }
    }

    @Override
    public boolean isNonNegative(ImmutableMap<LLVMHeuristicVariable, LLVMValue> values) {
        switch (this.getOperation()) {
            case ADD:
            case MUL:
                return this.getLhs().isNonNegative(values) && this.getRhs().isNonNegative(values);
            case SUB:
                return this.getLhs().isNonNegative(values) && this.getRhs().isNonPositive(values);
            default:
                return false;
        }
    }

    @Override
    public boolean isNonPositive(ImmutableMap<LLVMHeuristicVariable, LLVMValue> values) {
        switch (this.getOperation()) {
            case ADD:
                return this.getLhs().isNonPositive(values) && this.getRhs().isNonPositive(values);
            case SUB:
                return this.getLhs().isNonPositive(values) && this.getRhs().isNonNegative(values);
            case MUL:
                return
                    (this.getLhs().isNonPositive(values) && this.getRhs().isNonNegative(values))
                    || (this.getLhs().isNonNegative(values) && this.getRhs().isNonPositive(values));
            default:
                return false;
        }
    }

    /**
     * @return A pair of a reference r and an offset o such that r + o is equivalent to this operation. Null if no such
     *         reference and offset can be inferred.
     */
    public Pair<LLVMHeuristicVariable, BigInteger> isOffByConstantPattern() {
        switch (this.getOperation()) {
            case ADD:
                if (this.getLhs() instanceof LLVMHeuristicConstRef) {
                    if (this.getRhs() instanceof LLVMHeuristicVarRef) {
                        return
                            new Pair<LLVMHeuristicVariable, BigInteger>(
                                (LLVMHeuristicVariable)this.getRhs(),
                                ((LLVMHeuristicConstRef)this.getLhs()).getIntegerValue()
                            );
                    }
                } else if (this.getRhs() instanceof LLVMHeuristicConstRef && this.getLhs() instanceof LLVMHeuristicVarRef) {
                    return
                        new Pair<LLVMHeuristicVariable, BigInteger>(
                            (LLVMHeuristicVariable)this.getLhs(),
                            ((LLVMHeuristicConstRef)this.getRhs()).getIntegerValue()
                        );
                }
                break;
            case SUB:
                if (this.getRhs() instanceof LLVMHeuristicConstRef && this.getLhs() instanceof LLVMHeuristicVarRef) {
                    return
                        new Pair<LLVMHeuristicVariable, BigInteger>(
                            (LLVMHeuristicVariable)this.getLhs(),
                            ((LLVMHeuristicConstRef)this.getRhs()).getIntegerValue().negate()
                        );
                }
                break;
            default:
                // we cannot infer anything
        }
        return null;
    }

    @Override
    public boolean isPositive(ImmutableMap<LLVMHeuristicVariable, LLVMValue> values) {
        switch (this.getOperation()) {
            case ADD:
                return
                    (this.getLhs().isPositive(values) && this.getRhs().isNonNegative(values))
                    || (this.getLhs().isNonNegative(values) && this.getRhs().isPositive(values));
            case SUB:
                return
                    (this.getLhs().isPositive(values) && this.getRhs().isNonPositive(values))
                    || (this.getLhs().isNonNegative(values) && this.getRhs().isNegative(values));
            case MUL:
                return this.getLhs().isPositive(values) && this.getRhs().isPositive(values);
            default:
                return false;
        }
    }

    /**
     * @return True iff both arguments are references. False otherwise.
     */
    public boolean isSimple() {
        return this.getLhs() instanceof LLVMHeuristicVariable && this.getRhs() instanceof LLVMHeuristicVariable;
    }

    @Override
    public boolean isSum() {
        switch (this.getOperation()) {
            case ADD:
                return true;
            default:
                return false;
        }
    }

    @Override
    public boolean isSumOfTwoDifferentVariables() {
        switch (this.getOperation()) {
            case ADD:
                return
                    this.getLhs() instanceof LLVMHeuristicVarRef
                    && this.getRhs() instanceof LLVMHeuristicVarRef
                    && !this.getLhs().equals(this.getRhs());
            default:
                return false;
        }
    }

    @Override
    public boolean isSumOfVariableAndConstant() {
        switch (this.getOperation()) {
            case ADD:
                return
                    (this.getLhs() instanceof LLVMHeuristicVarRef
                        && this.getRhs() instanceof LLVMHeuristicConstRef)
                    || (this.getRhs() instanceof LLVMHeuristicVarRef
                        && this.getLhs() instanceof LLVMHeuristicConstRef);
            default:
                return false;
        }
    }

    @Override
    public LLVMHeuristicTerm negate() {
        Iterator<LLVMHeuristicTerm> it = this.getLiterals().iterator();
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> cur = it.next().toLinear();
        LLVMHeuristicTerm res;
        if (cur.x == null) {
            res = new LLVMHeuristicConstRef(cur.y.negate());
        } else {
            if (Globals.useAssertions && LLVMDebuggingFlags.CHECK_INVARIANTS) {
                assert (cur.y.compareTo(BigInteger.ZERO) == 0) : "This should be another literal!";
            }
            if (cur.z.compareTo(IntegerUtils.NEGONE) == 0) {
                res = cur.x;
            } else {
                res = new LLVMHeuristicOperation(
                    ArithmeticOperationType.MUL,
                    new LLVMHeuristicConstRef(cur.z.negate()),
                    cur.x
                );
            }
        }
        while (it.hasNext()) {
            cur = it.next().toLinear();
            LLVMHeuristicTerm toAdd;
            if (cur.x == null) {
                toAdd = new LLVMHeuristicConstRef(cur.y.negate());
            } else {
                if (Globals.useAssertions && LLVMDebuggingFlags.CHECK_INVARIANTS) {
                    assert (cur.y.compareTo(BigInteger.ZERO) == 0) : "This should be another literal!";
                }
                if (cur.z.compareTo(IntegerUtils.NEGONE) == 0) {
                    toAdd = cur.x;
                } else {
                    toAdd =
                        new LLVMHeuristicOperation(
                            ArithmeticOperationType.MUL,
                            new LLVMHeuristicConstRef(cur.z.negate()),
                            cur.x
                        );
                }
            }
            res = new LLVMHeuristicOperation(ArithmeticOperationType.ADD, res, toAdd);
        }
        return res;
    }

    @Override
    public LLVMHeuristicOperation setArguments(ImmutableList<? extends Expression> args) {
        assert (args.size() == 2) : "A binary expression must have exactly two arguments!";
        return
            new LLVMHeuristicOperation(
                this.getOperation(),
                (LLVMHeuristicTerm)args.get(0),
                (LLVMHeuristicTerm)args.get(1)
            );
    }

    /**
     * Using this setter might violate the invariants on the structure of heuristic terms.
     */
    @Override
    public LLVMHeuristicOperation setLhs(LLVMTerm lhsParam) {
        return new LLVMHeuristicOperation(this.getOperation(), (LLVMHeuristicTerm)lhsParam, this.getRhs());
    }

    /**
     * Using this setter might violate the invariants on the structure of heuristic terms.
     */
    @Override
    public LLVMHeuristicOperation setRhs(LLVMTerm rhsParam) {
        return new LLVMHeuristicOperation(this.getOperation(), this.getLhs(), (LLVMHeuristicTerm)rhsParam);
    }

    @Override
    public LLVMHeuristicTerm substitute(Map<LLVMHeuristicVariable, ? extends LLVMHeuristicTerm> substitution) {
        return
            this.getTermFactory().create(
                this.getOperation(),
                this.getLhs().substitute(substitution),
                this.getRhs().substitute(substitution)
            );
    }

    @Override
    public Triple<LLVMHeuristicTerm, BigInteger, BigInteger> toLinear() {
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> left = this.getLhs().toLinear();
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> right = this.getRhs().toLinear();
        final LLVMHeuristicTerm resExpr;
        final BigInteger multiplier;
        switch (this.getOperation()) {
            case ADD:
                if (left.x == null) {
                    resExpr = right.x;
                    multiplier = right.z;
                } else if (right.x == null) {
                    resExpr = left.x;
                    multiplier = left.z;
                } else if (left.z.compareTo(BigInteger.ONE) == 0) {
                    if (right.z.compareTo(BigInteger.ONE) == 0) {
                        resExpr = new LLVMHeuristicOperation(ArithmeticOperationType.ADD, left.x, right.x);
                        multiplier = BigInteger.ONE;
                    } else {
                        // we have: x + c + a * y + d
                        // thus: (x + a * y) + (c + d)
                        resExpr =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.ADD,
                                left.x,
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    new LLVMHeuristicConstRef(right.z),
                                    right.x
                                )
                            );
                        multiplier = BigInteger.ONE;
                    }
                } else if (right.z.compareTo(BigInteger.ONE) == 0) {
                    // we have: a * x + c + y + d
                    // thus: (a * x + y) + (c + d)
                    resExpr =
                        new LLVMHeuristicOperation(
                            ArithmeticOperationType.ADD,
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(left.z),
                                left.x
                            ),
                            right.x
                        );
                    multiplier = BigInteger.ONE;
                } else if (left.z.compareTo(right.z) == 0) {
                    // we have: a * x + c + a * y + d
                    // thus: a * (x + y) + (c + d)
                    resExpr = new LLVMHeuristicOperation(ArithmeticOperationType.ADD, left.x, right.x);
                    multiplier = left.z;
                } else {
                    // we have: a * x + c + b * y + d
                    // thus: (a * x + b * y) + (c + d)
                    resExpr =
                        new LLVMHeuristicOperation(
                            ArithmeticOperationType.ADD,
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(left.z),
                                left.x
                            ),
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(right.z),
                                right.x
                            )
                        );
                    multiplier = BigInteger.ONE;
                }
                return new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(resExpr, left.y.add(right.y), multiplier);
            case SUB:
                if (left.x == null) {
                    resExpr = right.x;
                    multiplier = right.x == null ? null : right.z.negate();
                } else if (right.x == null) {
                    resExpr = left.x;
                    multiplier = left.z;
                } else if (left.z.compareTo(right.z.negate()) == 0) {
                    // we have: a * x + c - (-a) * y - d
                    // thus: a * (x + y) + (c - d)
                    resExpr = new LLVMHeuristicOperation(ArithmeticOperationType.ADD, left.x, right.x);
                    multiplier = left.z;
                } else if (right.z.compareTo(IntegerUtils.NEGONE) == 0) {
                    // we have: a * x + c + y - d
                    // thus: (a * x + y) + (c - d)
                    resExpr =
                        new LLVMHeuristicOperation(
                            ArithmeticOperationType.ADD,
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(left.z),
                                left.x
                            ),
                            right.x
                        );
                    multiplier = BigInteger.ONE;
                } else if (left.z.compareTo(BigInteger.ONE) == 0) {
                    // we have: x + c - a * y - d
                    // thus: (x + (-a) * y) + (c - d)
                    resExpr =
                        new LLVMHeuristicOperation(
                            ArithmeticOperationType.ADD,
                            left.x,
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(right.z.negate()),
                                right.x
                            )
                        );
                    multiplier = BigInteger.ONE;
                } else if (left.z.compareTo(IntegerUtils.NEGONE) == 0) {
                    // we have: -x + c - a * y - d
                    // thus: -(x + a * y) + (c - d)
                    resExpr =
                        new LLVMHeuristicOperation(
                            ArithmeticOperationType.ADD,
                            left.x,
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(right.z),
                                right.x
                            )
                        );
                    multiplier = IntegerUtils.NEGONE;
                } else {
                    // we have: a * x + c - b * y - d
                    // thus: (a * x + (-b) * y) + (c - d)
                    resExpr =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.ADD,
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    new LLVMHeuristicConstRef(left.z),
                                    left.x
                                ),
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    new LLVMHeuristicConstRef(right.z.negate()),
                                    right.x
                                )
                            );
                    multiplier = BigInteger.ONE;
                }
                return new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(
                    resExpr,
                    left.y.subtract(right.y),
                    multiplier
                );
            case MUL:
                if (left.x == null) {
                    if (right.x == null) {
                        return
                            new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(null, left.y.multiply(right.y), null);
                    } else if (left.y.compareTo(BigInteger.ZERO) == 0) {
                        return new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(null, BigInteger.ZERO, null);
                    } else if (left.y.compareTo(BigInteger.ONE) == 0) {
                        return right;
                    } else {
                        return new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(
                            right.x,
                            left.y.multiply(right.y),
                            left.y.multiply(right.z)
                        );
                    }
                } else if (right.x == null) {
                    if (right.y.compareTo(BigInteger.ZERO) == 0) {
                        return new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(null, BigInteger.ZERO, null);
                    } else if (right.y.compareTo(BigInteger.ONE) == 0) {
                        return left;
                    } else {
                        return new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(
                            left.x,
                            left.y.multiply(right.y),
                            left.z.multiply(right.y)
                        );
                    }
                } else if (left.y.compareTo(BigInteger.ZERO) == 0 && right.y.compareTo(BigInteger.ZERO) == 0) {
                    // a * x * b * y
                    return new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(
                        new LLVMHeuristicOperation(ArithmeticOperationType.MUL, left.x, right.x),
                        BigInteger.ZERO,
                        left.z.multiply(right.z)
                    );
                } else {
                    // (a * x + c) * (b * y + d)
                    // a * x * b * y + a * x * d + c * b * y + c * d
                    // probably too complicated for us
                    return new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(this, BigInteger.ZERO, BigInteger.ONE);
                }
            case TIDIV:
                if (right.x == null) {
                    if (Globals.useAssertions) {
                        // TODO better throw an ErrorStateException?
                        assert (right.y.compareTo(BigInteger.ZERO) != 0) : "Division by 0 detected!";
                    }
                    if (right.y.compareTo(BigInteger.ONE) == 0) {
                        return left;
                    } else if (
                        left.y.remainder(right.y).compareTo(BigInteger.ZERO) == 0
                        && (left.x == null || left.z.remainder(right.y).compareTo(BigInteger.ZERO) == 0)
                    ) {
                        return new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(
                            left.x,
                            left.y.divide(right.y),
                            left.x == null ? null : left.z.divide(right.y)
                        );
                    }
                }
                // probably too complicated for us - fall through
            default:
                return new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(this, BigInteger.ZERO, BigInteger.ONE);
        }
    }

//    @Override
//    public SMTLIBIntValue toSMTIntValue() {
//        List<SMTLIBIntValue> operands = new LinkedList<SMTLIBIntValue>();
//        operands.add(this.getLhs().toSMTIntValue());
//        operands.add(this.getRhs().toSMTIntValue());
//        switch (this.getOpType()) {
//        case ADD:
//            return SMTLIBIntPlus.create(operands);
//        case SUB:
//            return SMTLIBIntMinus.create(operands);
//        case MUL:
//            return SMTLIBIntMult.create(operands);
//        case DIV:
//            return SMTLIBIntDiv.create(operands);
//        default:
//            throw new UnsupportedOperationException("No viable cases left. Operation: " + this.getOpType());
//        }
//    }

}
