package aprove.verification.oldframework.BasicStructures.Arithmetic;

import java.math.BigInteger;
import java.util.Collections;
import java.util.Set;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntegerReasoning.*;

/**
 * Possible arithmetic operators.
 * @author Marc Brockschmidt, cryingshadow
 */
public enum ArithmeticOperationType implements HasName, HasArity, HasFunctionSymbols, HasRootSymbol {

    /**
     * Addition.
     */
    ADD("+", true, 2) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) {
            return args[0].add(args[1]);
        }

    },

    /**
     * Logical and.
     */
    AND("&", true, 2) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) {
            return args[0].and(args[1]);
        }

    },

    /**
     * Euclidean integer division (remainder is always non-negative).
     */
    EIDIV("//e", false, 2) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) throws DivisionByZeroException {
            if (args[1].compareTo(BigInteger.ZERO) == 0) {
                throw new DivisionByZeroException();
            }
            return
                args[0].subtract(
                    args[0].compareTo(BigInteger.ZERO) < 0 ? args[1].subtract(BigInteger.ONE) : BigInteger.ZERO
                ).divide(args[1]);
        }

    },

    /**
     * Euclidean remainder of division. The result is always non-negative.
     */
    EMOD("mod", false, 2) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) throws DivisionByZeroException {
            if (args[1].compareTo(BigInteger.ZERO) == 0) {
                throw new DivisionByZeroException();
            }
            return args[0].mod(args[1]);
        }

    },

    /**
     * Floating-point division. TODO check what variants exist
     */
    FDIV("/f", false, 2) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) {
            throw new UnsupportedOperationException("No integer operation!");
        }

    },

    /**
     * Flooring integer division (rounding towards -infinity).
     */
    FIDIV("//f", false, 2) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) {
            return
                args[0].add(
                    (args[0].compareTo(BigInteger.ZERO) < 0) != (args[1].compareTo(BigInteger.ZERO) < 0) ?
                        args[1].subtract(BigInteger.ONE) :
                            BigInteger.ZERO
                ).divide(args[1]);
        }

    },

    /**
     * Flooring remainder of division. The sign of the result is that of the divisor.
     */
    FMOD("floormod", false, 2) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) throws DivisionByZeroException {
            if (args[1].compareTo(BigInteger.ZERO) == 0) {
                throw new DivisionByZeroException();
            }
            return
                args[0].mod(
                    args[1]
                ).subtract(
                    args[1].compareTo(BigInteger.ZERO) < 0 ? BigInteger.ONE : BigInteger.ZERO
                );
        }

    },

    /**
     * Mathematically precise division.
     */
    MDIV("/m", false, 2) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) throws DivisionByZeroException {
            if (args[1].compareTo(BigInteger.ZERO) == 0) {
                throw new DivisionByZeroException();
            }
            if (args[0].abs().mod(args[1].abs()).compareTo(BigInteger.ZERO) == 0) {
                return args[0].divide(args[1]);
            }
            throw new UnsupportedOperationException("No integer operation!");
        }

    },

    /**
     * Multiplication.
     */
    MUL("*", true, 2) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) {
            return args[0].multiply(args[1]);
        }

    },

    /**
     * Negate.
     */
    NEG("-", true, 1) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) {
            return args[0].negate();
        }

    },

    /**
     * Logical or.
     */
    OR("|", true, 2) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) {
            return args[0].or(args[1]);
        }

    },

    /**
     * Power.
     */
    POW("pow", false, 2) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) {
            if (args[1].compareTo(BigInteger.ZERO) < 0) {
                throw new UnsupportedOperationException("No integer operation!");
            }
            BigInteger counter = BigInteger.ZERO;
            BigInteger res = BigInteger.ONE;
            while (counter.compareTo(args[1]) < 0) {
                res = res.multiply(args[0]);
                counter = counter.add(BigInteger.ONE);
            }
            return res;
        }

    },

    /**
     * Shift left.
     */
    SHL("<<", false, 2) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) {
            // TODO what shall we implement here?
            throw new UnsupportedOperationException("Not yet implemented!");
        }

    },

    /**
     * Shift right.
     */
    SHR(">>", false, 2) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) {
            // TODO what shall we implement here?
            throw new UnsupportedOperationException("Not yet implemented!");
        }

    },

    /**
     * Subtraction.
     */
    SUB("-", false, 2) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) {
            return args[0].subtract(args[1]);
        }

    },

    /**
     * Truncating integer division (rounding towards zero).
     */
    TIDIV("//t", false, 2) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) throws DivisionByZeroException {
            if (args[1].compareTo(BigInteger.ZERO) == 0) {
                throw new DivisionByZeroException();
            }
            return args[0].divide(args[1]);
        }

    },

    /**
     * Truncating remainder of division. The sign of the result is that of the dividend.
     */
    TMOD("%", false, 2) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) throws DivisionByZeroException {
            if (args[1].compareTo(BigInteger.ZERO) == 0) {
                throw new DivisionByZeroException();
            }
            return args[0].remainder(args[1]);
        }

    },

    /**
     * Remainder of unsigned division.
     */
    UREM("urem", false, 2) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) {
            // TODO what shall we implement here?
            throw new UnsupportedOperationException("Not yet implemented!");
        }

    },

    /**
     * Shift right (unsigned).
     */
    USHR(">>>", false, 2) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) {
            // TODO what shall we implement here?
            throw new UnsupportedOperationException("Not yet implemented!");
        }

    },

    /**
     * Logical xor.
     */
    XOR("xor", true, 2) {

        @Override
        protected BigInteger evaluateOnIntegersResult(BigInteger... args) {
            return args[0].xor(args[1]);
        }

    };

    /**
     * @param sym Some function symbol.
     * @return The arithmetic operation type corresponding to the specified function symbol. Null if no such type
     *         exists.
     */
    public static ArithmeticOperationType forFunctionSymbol(FunctionSymbol sym) {
        for (ArithmeticOperationType type : ArithmeticOperationType.values()) {
            if (type.getRootSymbol().equals(sym)) {
                return type;
            }
        }
        return null;
    }

    /**
     * The arity.
     */
    private final int arity;

    /**
     * Flag indicating whether this operator is commutative.
     */
    private final boolean isCommutative;

    /**
     * A short string representation.
     */
    private final String name;

    /**
     * @param nameParam A short string representation.
     * @param commutative Flag indicating whether this operator is commutative.
     * @param arityParam The arity.
     */
    ArithmeticOperationType(String nameParam, boolean commutative, int arityParam) {
        this.name = nameParam;
        this.isCommutative = commutative;
        this.arity = arityParam;
    }

    /**
     * @param args The arguments.
     * @return The result of applying this operation to the specified integer arguments.
     * @throws DivisionByZeroException If the operation involves a division by zero.
     * @throws UnsupportedOperationException If the operation is no integer operation.
     */
    public BigInteger evaluateOnIntegers(BigInteger... args)
    throws DivisionByZeroException, UnsupportedOperationException {
        if (this.getArity() != args.length) {
            throw new IllegalArgumentException("The number of arguments does not match the arity of this operation!");
        }
        return this.evaluateOnIntegersResult(args);
    }

    @Override
    public int getArity() {
        return this.arity;
    }

    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        return Collections.singleton(this.getRootSymbol());
    }

    @Override
    public String getName() {
        return this.name;
    }

    @Override
    public FunctionSymbol getRootSymbol() {
        return FunctionSymbol.create(this.getName(), this.getArity());
    }

    /**
     * @return True if this operator is commutative. False otherwise.
     */
    public boolean isCommutative() {
        return this.isCommutative;
    }

    /**
     * @return A long string representation.
     */
    public String toLongString() {
        return super.toString();
    }

    @Override
    public String toString() {
        return this.getName();
    }

    /**
     * @param args The arguments.
     * @return The result of applying this operation to the specified integer arguments.
     *         Null otherwise.
     * @throws DivisionByZeroException If the operation involves a division by zero.
     * @throws UnsupportedOperationException If the operation is no integer operation.
     */
    protected abstract BigInteger evaluateOnIntegersResult(BigInteger... args)
    throws DivisionByZeroException, UnsupportedOperationException;

}
