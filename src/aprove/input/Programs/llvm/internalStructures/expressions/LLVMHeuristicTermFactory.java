package aprove.input.Programs.llvm.internalStructures.expressions;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Utils.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Creates heuristic terms for LLVM.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMHeuristicTermFactory implements LLVMTermFactory {

    /**
     * The default heuristic factory.
     */
    public static final LLVMHeuristicTermFactory LLVM_HEURISTIC_TERM_FACTORY = new LLVMHeuristicTermFactory();

    /**
     * Constant reference representing the value -1.
     */
    private static final LLVMHeuristicConstRef NEGONE = new LLVMHeuristicConstRef(IntegerUtils.NEGONE);

    /**
     * Constant reference representing the value -2.
     */
    private static final LLVMHeuristicConstRef NEGTWO = new LLVMHeuristicConstRef(BigInteger.valueOf(-2));

    /**
     * Constant reference representing the value 1.
     */
    private static final LLVMHeuristicConstRef ONE = new LLVMHeuristicConstRef(BigInteger.ONE);

    /**
     * Constant reference representing the value 2.
     */
    private static final LLVMHeuristicConstRef TWO = new LLVMHeuristicConstRef(BigInteger.valueOf(2));

    /**
     * Constant reference representing the value 0.
     */
    private static final LLVMHeuristicConstRef ZERO = new LLVMHeuristicConstRef(BigInteger.ZERO);

    /**
     * @param constant A constant c.
     * @param linear A triple (x,y,z) representing the expression y + z * x where x is non-constant.
     * @return A normalized expression for c * (y + z * x).
     */
    private static LLVMHeuristicTerm multiplicationWithConstant(
        BigInteger constant,
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linear
    ) {
        if (constant.compareTo(BigInteger.ZERO) == 0) {
            return LLVMHeuristicTermFactory.ZERO;
        } else if (constant.compareTo(BigInteger.ONE) == 0) {
            if (linear.y.compareTo(BigInteger.ZERO) == 0) {
                if (linear.z.compareTo(BigInteger.ONE) == 0) {
                    return linear.x;
                } else {
                    return new LLVMHeuristicOperation(
                        ArithmeticOperationType.MUL,
                        new LLVMHeuristicConstRef(linear.z),
                        linear.x
                    );
                }
            } else if (linear.z.compareTo(BigInteger.ONE) == 0) {
                return new LLVMHeuristicOperation(
                    ArithmeticOperationType.ADD,
                    new LLVMHeuristicConstRef(linear.y),
                    linear.x
                );
            } else {
                // y + z * x
                return new LLVMHeuristicOperation(
                    ArithmeticOperationType.ADD,
                    new LLVMHeuristicConstRef(linear.y),
                    new LLVMHeuristicOperation(
                        ArithmeticOperationType.MUL,
                        new LLVMHeuristicConstRef(linear.z),
                        linear.x
                    )
                );
            }
        } else if (constant.compareTo(IntegerUtils.NEGONE) == 0) {
            if (linear.y.compareTo(BigInteger.ZERO) == 0) {
                if (linear.z.compareTo(IntegerUtils.NEGONE) == 0) {
                    return linear.x;
                } else {
                    return new LLVMHeuristicOperation(
                        ArithmeticOperationType.MUL,
                        new LLVMHeuristicConstRef(linear.z.negate()),
                        linear.x
                    );
                }
            } else if (linear.z.compareTo(IntegerUtils.NEGONE) == 0) {
                return new LLVMHeuristicOperation(
                    ArithmeticOperationType.ADD,
                    new LLVMHeuristicConstRef(linear.y.negate()),
                    linear.x
                );
            } else {
                // -y + (-z) * x
                return new LLVMHeuristicOperation(
                    ArithmeticOperationType.ADD,
                    new LLVMHeuristicConstRef(linear.y.negate()),
                    new LLVMHeuristicOperation(
                        ArithmeticOperationType.MUL,
                        new LLVMHeuristicConstRef(linear.z.negate()),
                        linear.x
                    )
                );
            }
        } else if (linear.y.compareTo(BigInteger.ZERO) == 0) {
            // c * z * x
            return new LLVMHeuristicOperation(
                ArithmeticOperationType.MUL,
                new LLVMHeuristicConstRef(constant.multiply(linear.z)),
                linear.x
            );
        } else {
            // c * (z * x + y)
            return new LLVMHeuristicOperation(
                ArithmeticOperationType.ADD,
                new LLVMHeuristicConstRef(constant.multiply(linear.y)),
                new LLVMHeuristicOperation(
                    ArithmeticOperationType.MUL,
                    new LLVMHeuristicConstRef(constant.multiply(linear.z)),
                    linear.x
                )
            );
        }
    }

    /**
     * @param constant A non-zero constant c.
     * @param expression A non-constant expression e.
     * @param linear A triple (x,y,z) representing the expression y + z * x where x is non-constant.
     * @return A normalized expression for c * e * (y + z * x).
     */
    private static LLVMHeuristicTerm multiplicationWithMultiplicativeTerm(
        BigInteger constant,
        LLVMHeuristicTerm expression,
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linear
    ) {
        if (linear.y.compareTo(BigInteger.ZERO) == 0) {
            // c * z * e * x
            BigInteger factor = constant.multiply(linear.z);
            if (factor.compareTo(BigInteger.ONE) == 0) {
                return new LLVMHeuristicOperation(ArithmeticOperationType.MUL, expression, linear.x);
            } else {
                return new LLVMHeuristicOperation(
                    ArithmeticOperationType.MUL,
                    new LLVMHeuristicConstRef(factor),
                    new LLVMHeuristicOperation(ArithmeticOperationType.MUL, expression, linear.x)
                );
            }
        } else {
            if (constant.compareTo(BigInteger.ONE) == 0) {
                if (linear.z.compareTo(BigInteger.ONE) == 0) {
                    // e * (y + x)
                    return new LLVMHeuristicOperation(
                        ArithmeticOperationType.MUL,
                        expression,
                        new LLVMHeuristicOperation(
                            ArithmeticOperationType.ADD,
                            new LLVMHeuristicConstRef(linear.y),
                            linear.x
                        )
                    );
                } else {
                    // e * (y + z * x)
                    return new LLVMHeuristicOperation(
                        ArithmeticOperationType.MUL,
                        expression,
                        new LLVMHeuristicOperation(
                            ArithmeticOperationType.ADD,
                            new LLVMHeuristicConstRef(linear.y),
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(linear.z),
                                linear.x
                            )
                        )
                    );
                }
            } else if (constant.compareTo(IntegerUtils.NEGONE) == 0) {
                if (linear.z.compareTo(IntegerUtils.NEGONE) == 0) {
                    // e * (-y + x)
                    return new LLVMHeuristicOperation(
                        ArithmeticOperationType.MUL,
                        expression,
                        new LLVMHeuristicOperation(
                            ArithmeticOperationType.ADD,
                            new LLVMHeuristicConstRef(linear.y.negate()),
                            linear.x
                        )
                    );
                } else {
                    // e * (-y + (-z) * x)
                    return new LLVMHeuristicOperation(
                        ArithmeticOperationType.MUL,
                        expression,
                        new LLVMHeuristicOperation(
                            ArithmeticOperationType.ADD,
                            new LLVMHeuristicConstRef(linear.y.negate()),
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(linear.z.negate()),
                                linear.x
                            )
                        )
                    );
                }
            } else {
                // e * (c * y + c * z * x)
                return new LLVMHeuristicOperation(
                    ArithmeticOperationType.MUL,
                    expression,
                    new LLVMHeuristicOperation(
                        ArithmeticOperationType.ADD,
                        new LLVMHeuristicConstRef(constant.multiply(linear.y)),
                        new LLVMHeuristicOperation(
                            ArithmeticOperationType.MUL,
                            new LLVMHeuristicConstRef(constant.multiply(linear.z)),
                            linear.x
                        )
                    )
                );
            }
        }
    }

    /**
     * No instantiation from outside.
     */
    private LLVMHeuristicTermFactory() {
        // do not instantiate me from outside
    }

    @Override
    public LLVMHeuristicTerm add(LLVMTerm lhs, LLVMTerm rhs) {
        return this.operation(ArithmeticOperationType.ADD, lhs, rhs);
    }

    @Override
    public LLVMHeuristicTerm and(LLVMTerm lhs, LLVMTerm rhs) {
        if (lhs.equals(this.zero()) || rhs.equals(this.zero())) {
            return this.zero();
        }
        return this.operation(ArithmeticOperationType.AND, lhs, rhs);
    }

    @Override
    public LLVMHeuristicConstRef constant(BigInteger value) {
        if (BigInteger.ZERO.compareTo(value) == 0) {
            return this.zero();
        }
        if (BigInteger.ONE.compareTo(value) == 0) {
            return this.one();
        }
        if (IntegerUtils.NEGONE.compareTo(value) == 0) {
            return this.negone();
        }
        if (IntegerUtils.TWO.compareTo(value) == 0) {
            return this.two();
        }
        if (IntegerUtils.NEGTWO.compareTo(value) == 0) {
            return this.negtwo();
        }
        return new LLVMHeuristicConstRef(value);
    }

    /**
     * Creates an expression. Operations are always normalized according to the toLinear() method such that constant
     * offsets are at the leftmost position only and subtractions occur only implicitly by multiplication with negative
     * numbers. Moreover, multiplicities of literals are joined.
     * @param op Type of the (binary) operation. May never be null.
     * @param l Left-hand side of this (binary) operation. May never be null.
     * @param r Right-hand side of this (binary) operation. May never be null.
     * @return The normalized operation.
     */
    public LLVMHeuristicTerm create(ArithmeticOperationType op, LLVMHeuristicTerm l, LLVMHeuristicTerm r) {
        List<LLVMHeuristicTerm> literals =
            this.joinMultiplicitiesOfLiterals(this.createNormalized(op, l, r).getLiterals());
        if (literals.isEmpty()) {
            return LLVMHeuristicTermFactory.ZERO;
        }
        Iterator<LLVMHeuristicTerm> it = literals.iterator();
        LLVMHeuristicTerm res = it.next();
        while (it.hasNext()) {
            res = new LLVMHeuristicOperation(ArithmeticOperationType.ADD, res, it.next());
        }
        return res;
    }

    @Override
    public LLVMHeuristicTerm create(FunctionalIntegerExpression exp) {
        if (exp instanceof LLVMHeuristicTerm) {
            return (LLVMHeuristicTerm)exp;
        }
        return (LLVMHeuristicTerm)LLVMTermFactory.create(exp, this);
    }

    /**
     * @param expr Some expression.
     * @param offset A constant offset.
     * @param factor A constant factor.
     * @return A normalized expression representing offset + factor * expr.
     */
    public LLVMHeuristicTerm create(LLVMHeuristicTerm expr, BigInteger offset, BigInteger factor) {
        return this.create(new Triple<LLVMHeuristicTerm, BigInteger, BigInteger>(expr, offset, factor));
    }

    /**
     * @param linear A triple (x,y,z) representing the term z * x + y.
     * @return A normalized expression for the specified term.
     */
    public LLVMHeuristicTerm create(Triple<? extends LLVMHeuristicTerm, BigInteger, BigInteger> linear) {
        if (linear.x == null) {
            return new LLVMHeuristicConstRef(linear.y);
        }
        if (linear.y.compareTo(BigInteger.ZERO) == 0) {
            if (linear.z.compareTo(BigInteger.ONE) == 0) {
                return linear.x;
            }
            return new LLVMHeuristicOperation(ArithmeticOperationType.MUL, new LLVMHeuristicConstRef(linear.z), linear.x);
        }
        if (linear.z.compareTo(BigInteger.ONE) == 0) {
            return new LLVMHeuristicOperation(ArithmeticOperationType.ADD, new LLVMHeuristicConstRef(linear.y), linear.x);
        }
        return new LLVMHeuristicOperation(
            ArithmeticOperationType.ADD,
            new LLVMHeuristicConstRef(linear.y),
            new LLVMHeuristicOperation(ArithmeticOperationType.MUL, new LLVMHeuristicConstRef(linear.z), linear.x)
        );
    }

    @Override
    public LLVMHeuristicVarRef freshVariable() {
        return new LLVMHeuristicVarRef(UIDGenerator.getValueUIDGenerator().next());
    }

    @Override
    public LLVMHeuristicVarRef freshVariable(String dName) {
        return new LLVMHeuristicVarRef(UIDGenerator.getValueUIDGenerator().next(), dName);
    }

    /**
     * @param literals The list of literals.
     * @return The specified literals with joined multiplicities.
     */
    public List<LLVMHeuristicTerm> joinMultiplicitiesOfLiterals(List<LLVMHeuristicTerm> literals) {
        // this method must stay in the LLVMOperation class as it is used to create operations
        Map<LLVMHeuristicTerm, BigInteger> multiplicity = new LinkedHashMap<LLVMHeuristicTerm, BigInteger>();
        BigInteger offset = BigInteger.ZERO;
        for (LLVMHeuristicTerm literal : literals) {
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linear = literal.toLinear();
            if (linear.x == null) {
                offset = offset.add(linear.y);
            } else {
                if (Globals.useAssertions && LLVMDebuggingFlags.CHECK_INVARIANTS) {
                    assert (linear.y.compareTo(BigInteger.ZERO) == 0) : "This should be another literal!";
                }
                if (multiplicity.containsKey(linear.x)) {
                    multiplicity.put(linear.x, multiplicity.get(linear.x).add(linear.z));
                } else {
                    multiplicity.put(linear.x, linear.z);
                }
            }
        }
        List<LLVMHeuristicTerm> res = new ArrayList<LLVMHeuristicTerm>();
        if (offset.compareTo(BigInteger.ZERO) != 0) {
            res.add(new LLVMHeuristicConstRef(offset));
        }
        for (Map.Entry<LLVMHeuristicTerm, BigInteger> entry : multiplicity.entrySet()) {
            BigInteger factor = entry.getValue();
            if (factor.compareTo(BigInteger.ZERO) == 0) {
                continue;
            }
            if (factor.compareTo(BigInteger.ONE) == 0) {
                res.add(entry.getKey());
            } else {
                res.add(new LLVMHeuristicOperation(ArithmeticOperationType.MUL, new LLVMHeuristicConstRef(factor), entry.getKey()));
            }
        }
        return res;
    }

    @Override
    public LLVMHeuristicConstRef negone() {
        return LLVMHeuristicTermFactory.NEGONE;
    }

    /**
     * @return The constant -2.
     */
    public LLVMHeuristicConstRef negtwo() {
        return LLVMHeuristicTermFactory.NEGTWO;
    }

    @Override
    public LLVMHeuristicConstRef one() {
        return LLVMHeuristicTermFactory.ONE;
    }

    @Override
    public LLVMHeuristicTerm operation(ArithmeticOperationType type, LLVMTerm lhs, LLVMTerm rhs) {
        return this.create(type, (LLVMHeuristicTerm)lhs, (LLVMHeuristicTerm)rhs);
    }

    /**
     * @return The constant 2.
     */
    public LLVMHeuristicConstRef two() {
        return LLVMHeuristicTermFactory.TWO;
    }

    /**
     * @param ref A pointer reference.
     * @param offset Maximal additional memory cells occupied by values referenced by <code>ref</code>.
     * @return An expression representing the biggest address occupied by a memory access specified by the given
     *         reference and offset.
     */
    public LLVMHeuristicTerm upperAddress(LLVMHeuristicVariable ref, BigInteger offset) {
        if (offset.compareTo(BigInteger.ZERO) == 0) {
            return ref;
        }
        if (Globals.useAssertions) {
            assert (offset.compareTo(BigInteger.ZERO) > 0) : "Found a memory access with negative offset!";
        }
        return this.add(ref, this.constant(offset));
    }

    @Override
    public LLVMHeuristicVarRef varRef(String name) {
        return new LLVMHeuristicVarRef(name);
    }

    @Override
    public LLVMHeuristicVarRef varRef(String name, String dName) {
        return new LLVMHeuristicVarRef(name, dName);
    }

    @Override
    public LLVMHeuristicConstRef zero() {
        return LLVMHeuristicTermFactory.ZERO;
    }

    /**
     * Creates an expression. Operations are always normalized according to the toLinear() method such that constant
     * offsets are at the leftmost position only and subtractions occur only implicitly by multiplication with negative
     * numbers.
     * @param op Type of the (binary) operation. May never be null.
     * @param l Left-hand side of this (binary) operation. May never be null.
     * @param r Right-hand side of this (binary) operation. May never be null.
     * @return The normalized operation.
     */
    private LLVMHeuristicTerm createNormalized(
        ArithmeticOperationType op,
        LLVMHeuristicTerm l,
        LLVMHeuristicTerm r
    ) {
        if (l == null) {
            if (r == null) {
                return null;
            }
            switch (op) {
                case ADD:
                    this.create(r.toLinear());
                case SUB:
                    Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linear = r.toLinear();
                    if (linear.x == null) {
                        return new LLVMHeuristicConstRef(linear.y.negate());
                    }
                    linear.z = linear.z.negate();
                    linear.y = linear.y.negate();
                    return this.create(linear);
                default:
                    return null;
            }
        }
        if (r == null) {
            switch (op) {
                case ADD:
                case SUB:
                    return this.create(l.toLinear());
                default:
                    return null;
            }
        }
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> leftLinear = l.toLinear();
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rightLinear = r.toLinear();
        if (leftLinear.x == null && rightLinear.x == null) {
            switch (op) {
                case ADD:
                    return new LLVMHeuristicConstRef(leftLinear.y.add(rightLinear.y));
                case SUB:
                    return new LLVMHeuristicConstRef(leftLinear.y.subtract(rightLinear.y));
                case MUL:
                    return new LLVMHeuristicConstRef(leftLinear.y.multiply(rightLinear.y));
                case TIDIV:
                    return new LLVMHeuristicConstRef(leftLinear.y.divide(rightLinear.y));
                case AND:
                    return new LLVMHeuristicConstRef(leftLinear.y.and(rightLinear.y));
                case OR:
                    return new LLVMHeuristicConstRef(leftLinear.y.or(rightLinear.y));
                case POW:
                    return new LLVMHeuristicConstRef(leftLinear.y.pow(rightLinear.y.intValue()));
                case TMOD:
                    return new LLVMHeuristicConstRef(leftLinear.y.remainder(rightLinear.y));
                    //                case UREM:
                    //                    BigInteger res;
                    //                    if (leftLinear.y.compareTo(BigInteger.ZERO) >= 0) {
                    //                        res = leftLinear.y.remainder(rightLinear.y);
                    //                    } else {
                    //                        int size = l.getReferenceType().size();
                    //                        res = leftLinear.y.add(BigInteger.valueOf(2).pow(size)).remainder(rightLinear.y);
                    //                    }
                    //                    return new LLVMConstRef(res);
                case EMOD:
                    return new LLVMHeuristicConstRef(leftLinear.y.mod(rightLinear.y));
                case SHL:
                    return new LLVMHeuristicConstRef(leftLinear.y.shiftLeft(rightLinear.y.intValue()));
                case SHR:
                    return new LLVMHeuristicConstRef(leftLinear.y.shiftRight(rightLinear.y.intValue()));
                case USHR:
                    throw new UnsupportedOperationException("This makes no sense with BigInteger! We need size info!");
                case XOR:
                    return new LLVMHeuristicConstRef(leftLinear.y.xor(rightLinear.y));
                default:
                    throw new IllegalStateException("Unknown or non-binary operator type!");
            }
        }
        final ArithmeticOperationType resOpType;
        final LLVMHeuristicTerm resLhs;
        final LLVMHeuristicTerm resRhs;
        switch (op) {
            case ADD:
            case SUB:
                final int IS_SUB = 1;
                final int LX_NULL = 2;
                final int RX_NULL = 4;
                final int LZ_ONE = 8;
                final int RZ_ONE = 16;
                final int LZ_NEGONE = 32;
                final int RZ_NEGONE = 64;
                final int OFF_ZERO = 128;
                final int LXRX_EQUAL = 256;
                int status = 0;
                // determine constant offset
                final BigInteger offset;
                if (op == ArithmeticOperationType.SUB) {
                    status |= IS_SUB;
                    offset = leftLinear.y.subtract(rightLinear.y);
                } else {
                    offset = leftLinear.y.add(rightLinear.y);
                }
                if (offset.compareTo(BigInteger.ZERO) == 0) {
                    status |= OFF_ZERO;
                }
                resLhs = new LLVMHeuristicConstRef(offset);
                if (leftLinear.x == null) {
                    status |= LX_NULL;
                } else {
                    if (leftLinear.x.equals(rightLinear.x)) {
                        status |= LXRX_EQUAL;
                    }
                    if (leftLinear.z.compareTo(BigInteger.ONE) == 0) {
                        status |= LZ_ONE;
                    } else if (leftLinear.z.compareTo(IntegerUtils.NEGONE) == 0) {
                        status |= LZ_NEGONE;
                    }
                }
                if (rightLinear.x == null) {
                    status |= RX_NULL;
                } else if (rightLinear.z.compareTo(BigInteger.ONE) == 0) {
                    status |= RZ_ONE;
                } else if (rightLinear.z.compareTo(IntegerUtils.NEGONE) == 0) {
                    status |= RZ_NEGONE;
                }
                switch (status) {
                    case 0:
                    case LZ_NEGONE:
                    case RZ_NEGONE:
                    case LZ_NEGONE | RZ_NEGONE:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.ADD,
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    new LLVMHeuristicConstRef(leftLinear.z),
                                    leftLinear.x
                                ),
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    new LLVMHeuristicConstRef(rightLinear.z),
                                    rightLinear.x
                                )
                            );
                        break;
                    case IS_SUB:
                    case LZ_NEGONE | IS_SUB:
                    case RZ_ONE | LZ_NEGONE | IS_SUB:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.ADD,
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    new LLVMHeuristicConstRef(leftLinear.z),
                                    leftLinear.x
                                ),
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    new LLVMHeuristicConstRef(rightLinear.z.negate()),
                                    rightLinear.x
                                )
                            );
                        break;
                    case RX_NULL | LZ_ONE | OFF_ZERO:
                    case RX_NULL | LZ_ONE | OFF_ZERO | IS_SUB:
                        return leftLinear.x;
                    case RX_NULL | LZ_ONE:
                    case RX_NULL | LZ_ONE | IS_SUB:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs = leftLinear.x;
                        break;
                    case RX_NULL:
                    case RX_NULL | IS_SUB:
                    case RX_NULL | LZ_NEGONE:
                    case RX_NULL | LZ_NEGONE | IS_SUB:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(leftLinear.z),
                                leftLinear.x
                            );
                        break;
                    case RX_NULL | OFF_ZERO:
                    case RX_NULL | OFF_ZERO | IS_SUB:
                    case RX_NULL | LZ_NEGONE | OFF_ZERO:
                    case RX_NULL | LZ_NEGONE | IS_SUB | OFF_ZERO:
                        return
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(leftLinear.z),
                                leftLinear.x
                            );
                    case LX_NULL | RZ_ONE | OFF_ZERO:
                    case LX_NULL | RZ_NEGONE | OFF_ZERO | IS_SUB:
                        return rightLinear.x;
                    case LX_NULL | RZ_ONE:
                    case LX_NULL | RZ_NEGONE | IS_SUB:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs = rightLinear.x;
                        break;
                    case LX_NULL | OFF_ZERO:
                    case LX_NULL | RZ_NEGONE | OFF_ZERO:
                        return
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(rightLinear.z),
                                rightLinear.x
                            );
                    case LX_NULL | OFF_ZERO | IS_SUB:
                    case LX_NULL | RZ_ONE | OFF_ZERO | IS_SUB:
                        return
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(rightLinear.z.negate()),
                                rightLinear.x
                            );
                    case LX_NULL:
                    case LX_NULL | RZ_NEGONE:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(rightLinear.z),
                                rightLinear.x
                            );
                        break;
                    case LX_NULL | IS_SUB:
                    case LX_NULL | RZ_ONE | IS_SUB:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(rightLinear.z.negate()),
                                rightLinear.x
                            );
                        break;
                    case LZ_ONE | RZ_ONE | LXRX_EQUAL | IS_SUB:
                    case LZ_ONE | RZ_ONE | LXRX_EQUAL | IS_SUB | OFF_ZERO:
                    case LZ_ONE | RZ_NEGONE | LXRX_EQUAL:
                    case LZ_ONE | RZ_NEGONE | LXRX_EQUAL | OFF_ZERO:
                    case RZ_ONE | LZ_NEGONE | LXRX_EQUAL:
                    case RZ_ONE | LZ_NEGONE | LXRX_EQUAL | OFF_ZERO:
                    case LZ_NEGONE | RZ_NEGONE | IS_SUB | LXRX_EQUAL:
                    case LZ_NEGONE | RZ_NEGONE | IS_SUB | LXRX_EQUAL | OFF_ZERO:
                        return new LLVMHeuristicConstRef(offset);
                    case LZ_ONE | RZ_ONE | LXRX_EQUAL:
                    case LZ_ONE | RZ_NEGONE | LXRX_EQUAL | IS_SUB:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                LLVMHeuristicTermFactory.TWO,
                                leftLinear.x
                            );
                        break;
                    case LZ_ONE | RZ_ONE | IS_SUB:
                    case LZ_ONE | RZ_NEGONE:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.ADD,
                                leftLinear.x,
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    LLVMHeuristicTermFactory.NEGONE,
                                    rightLinear.x
                                )
                            );
                        break;
                    case LZ_ONE | RZ_ONE:
                    case LZ_ONE | RZ_NEGONE | IS_SUB:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs = new LLVMHeuristicOperation(ArithmeticOperationType.ADD, leftLinear.x, rightLinear.x);
                        break;
                    case LZ_ONE | RZ_NEGONE | OFF_ZERO:
                    case LZ_ONE | RZ_ONE | OFF_ZERO | IS_SUB:
                        return
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.ADD,
                                leftLinear.x,
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    LLVMHeuristicTermFactory.NEGONE,
                                    rightLinear.x
                                )
                            );
                    case LZ_ONE | RZ_ONE | OFF_ZERO:
                    case LZ_ONE | RZ_NEGONE | OFF_ZERO | IS_SUB:
                        return new LLVMHeuristicOperation(ArithmeticOperationType.ADD, leftLinear.x, rightLinear.x);
                    case LZ_ONE | RZ_NEGONE | LXRX_EQUAL | OFF_ZERO | IS_SUB:
                    case LZ_ONE | RZ_ONE | LXRX_EQUAL | OFF_ZERO:
                        return
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                LLVMHeuristicTermFactory.TWO,
                                leftLinear.x
                            );
                    case LZ_ONE | LXRX_EQUAL | IS_SUB:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                LLVMHeuristicTermFactory.NEGTWO,
                                leftLinear.x
                            );
                        break;
                    case LZ_ONE | LXRX_EQUAL:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(rightLinear.z.add(BigInteger.ONE)),
                                leftLinear.x
                            );
                        break;
                    case LZ_ONE:
                    case LZ_ONE | IS_SUB:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                op,
                                leftLinear.x,
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    new LLVMHeuristicConstRef(rightLinear.z),
                                    rightLinear.x
                                )
                            );
                        break;
                    case LZ_ONE | OFF_ZERO:
                    case LZ_ONE | OFF_ZERO | IS_SUB:
                        return
                            new LLVMHeuristicOperation(
                                op,
                                leftLinear.x,
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    new LLVMHeuristicConstRef(rightLinear.z),
                                    rightLinear.x
                                )
                            );
                    case LZ_ONE | LXRX_EQUAL | OFF_ZERO:
                        return
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(rightLinear.z.add(BigInteger.ONE)),
                                leftLinear.x
                            );
                    case LZ_ONE | LXRX_EQUAL | OFF_ZERO | IS_SUB:
                        return
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(rightLinear.z.negate().add(BigInteger.ONE)),
                                leftLinear.x
                            );
                    case RZ_ONE | LZ_NEGONE | IS_SUB | LXRX_EQUAL:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                LLVMHeuristicTermFactory.NEGTWO,
                                leftLinear.x
                            );
                        break;
                    case RZ_ONE | LZ_NEGONE | IS_SUB | LXRX_EQUAL | OFF_ZERO:
                    case LZ_NEGONE | RZ_NEGONE | LXRX_EQUAL | OFF_ZERO:
                        return
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                LLVMHeuristicTermFactory.NEGTWO,
                                leftLinear.x
                            );
                    case LZ_NEGONE | RZ_NEGONE | IS_SUB:
                    case RZ_ONE | LZ_NEGONE:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.ADD,
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    LLVMHeuristicTermFactory.NEGONE,
                                    leftLinear.x
                                ),
                                rightLinear.x
                            );
                        break;
                    case LZ_NEGONE | RZ_NEGONE | IS_SUB | OFF_ZERO:
                    case RZ_ONE | LZ_NEGONE | OFF_ZERO:
                        return
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.ADD,
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    LLVMHeuristicTermFactory.NEGONE,
                                    leftLinear.x
                                ),
                                rightLinear.x
                            );
                    case RZ_ONE | LXRX_EQUAL | IS_SUB:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(leftLinear.z.subtract(BigInteger.ONE)),
                                leftLinear.x
                            );
                        break;
                    case RZ_ONE | LXRX_EQUAL | IS_SUB | OFF_ZERO:
                        return
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(leftLinear.z.subtract(BigInteger.ONE)),
                                leftLinear.x
                            );
                    case RZ_ONE | LXRX_EQUAL:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(leftLinear.z.add(BigInteger.ONE)),
                                leftLinear.x
                            );
                        break;
                    case RZ_ONE | LXRX_EQUAL | OFF_ZERO:
                        return
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(leftLinear.z.add(BigInteger.ONE)),
                                leftLinear.x
                            );
                    case RZ_ONE:
                    case RZ_ONE | IS_SUB:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                op,
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    new LLVMHeuristicConstRef(leftLinear.z),
                                    leftLinear.x
                                ),
                                rightLinear.x
                            );
                        break;
                    case LZ_NEGONE | IS_SUB | OFF_ZERO | LXRX_EQUAL:
                        return
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(rightLinear.z.negate().subtract(BigInteger.ONE)),
                                leftLinear.x
                            );
                    case LZ_NEGONE | IS_SUB | LXRX_EQUAL:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(rightLinear.z.negate().subtract(BigInteger.ONE)),
                                leftLinear.x
                            );
                        break;
                    case LZ_NEGONE | LXRX_EQUAL:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(rightLinear.z.subtract(BigInteger.ONE)),
                                leftLinear.x
                            );
                        break;
                    case LZ_NEGONE | LXRX_EQUAL | OFF_ZERO:
                        return
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(rightLinear.z.subtract(BigInteger.ONE)),
                                leftLinear.x
                            );
                    case RZ_NEGONE | LXRX_EQUAL | IS_SUB:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(leftLinear.z.add(BigInteger.ONE)),
                                leftLinear.x
                            );
                        break;
                    case RZ_NEGONE | LXRX_EQUAL | IS_SUB | OFF_ZERO:
                        return
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(leftLinear.z.add(BigInteger.ONE)),
                                leftLinear.x
                            );
                    case RZ_NEGONE | IS_SUB:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.ADD,
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    new LLVMHeuristicConstRef(leftLinear.z),
                                    leftLinear.x
                                ),
                                rightLinear.x
                            );
                        break;
                    case RZ_ONE | OFF_ZERO:
                    case RZ_NEGONE | IS_SUB | OFF_ZERO:
                        return
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.ADD,
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    new LLVMHeuristicConstRef(leftLinear.z),
                                    leftLinear.x
                                ),
                                rightLinear.x
                            );
                    case LXRX_EQUAL | IS_SUB:
                        if (leftLinear.z.compareTo(rightLinear.z) == 0) {
                            return resLhs;
                        }
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(leftLinear.z.subtract(rightLinear.z)),
                                leftLinear.x
                            );
                        break;
                    case LXRX_EQUAL | IS_SUB | OFF_ZERO:
                        if (leftLinear.z.compareTo(rightLinear.z) == 0) {
                            return LLVMHeuristicTermFactory.ZERO;
                        }
                        return
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(leftLinear.z.subtract(rightLinear.z)),
                                leftLinear.x
                            );
                    case LXRX_EQUAL:
                        if (leftLinear.z.negate().compareTo(rightLinear.z) == 0) {
                            return resLhs;
                        }
                    case RZ_NEGONE | LXRX_EQUAL:
                    case LZ_NEGONE | RZ_NEGONE | LXRX_EQUAL:
                        resOpType = ArithmeticOperationType.ADD;
                        resRhs =
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(leftLinear.z.add(rightLinear.z)),
                                leftLinear.x
                            );
                        break;
                    case LXRX_EQUAL | OFF_ZERO:
                    case RZ_NEGONE | LXRX_EQUAL | OFF_ZERO:
                        if (leftLinear.z.negate().compareTo(rightLinear.z) == 0) {
                            return LLVMHeuristicTermFactory.ZERO;
                        }
                        return
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(leftLinear.z.add(rightLinear.z)),
                                leftLinear.x
                            );
                    case OFF_ZERO:
                    case LZ_NEGONE | OFF_ZERO:
                    case RZ_NEGONE | OFF_ZERO:
                    case LZ_NEGONE | RZ_NEGONE | OFF_ZERO:
                        return
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.ADD,
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    new LLVMHeuristicConstRef(leftLinear.z),
                                    leftLinear.x
                                ),
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    new LLVMHeuristicConstRef(rightLinear.z),
                                    rightLinear.x
                                )
                            );
                    case OFF_ZERO | IS_SUB:
                    case LZ_NEGONE | OFF_ZERO | IS_SUB:
                    case RZ_ONE | OFF_ZERO | IS_SUB:
                    case LZ_NEGONE | RZ_ONE | OFF_ZERO | IS_SUB:
                        return
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.ADD,
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    new LLVMHeuristicConstRef(leftLinear.z),
                                    leftLinear.x
                                ),
                                new LLVMHeuristicOperation(
                                    ArithmeticOperationType.MUL,
                                    new LLVMHeuristicConstRef(rightLinear.z.negate()),
                                    rightLinear.x
                                )
                            );
                    default:
                        throw new IllegalStateException("This input combination should not be possible!");
                }
                break;
            case MUL:
                if (leftLinear.x == null) {
                    return LLVMHeuristicTermFactory.multiplicationWithConstant(leftLinear.y, rightLinear);
                } else if (rightLinear.x == null) {
                    return LLVMHeuristicTermFactory.multiplicationWithConstant(rightLinear.y, leftLinear);
                } else if (leftLinear.y.compareTo(BigInteger.ZERO) == 0) {
                    return
                        LLVMHeuristicTermFactory.multiplicationWithMultiplicativeTerm(
                            leftLinear.z,
                            leftLinear.x,
                            rightLinear
                        );
                } else if (rightLinear.y.compareTo(BigInteger.ZERO) == 0) {
                    return
                        LLVMHeuristicTermFactory.multiplicationWithMultiplicativeTerm(
                            rightLinear.z,
                            rightLinear.x,
                            leftLinear
                        );
                } else {
                    // (l.y + l.z * l.x) * (r.y + r.z * r.x)
                    // probably too complicated for us
                    resOpType = ArithmeticOperationType.MUL;
                    resLhs =
                        new LLVMHeuristicOperation(
                            ArithmeticOperationType.ADD,
                            new LLVMHeuristicConstRef(leftLinear.y),
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(leftLinear.z),
                                leftLinear.x
                            )
                        );
                    resRhs =
                        new LLVMHeuristicOperation(
                            ArithmeticOperationType.ADD,
                            new LLVMHeuristicConstRef(rightLinear.y),
                            new LLVMHeuristicOperation(
                                ArithmeticOperationType.MUL,
                                new LLVMHeuristicConstRef(rightLinear.z),
                                rightLinear.x
                            )
                        );
                }
                break;
            default:
                resOpType = op;
                resLhs = l;
                resRhs = r;
        }
        return new LLVMHeuristicOperation(resOpType, resLhs, resRhs);
    }

}
