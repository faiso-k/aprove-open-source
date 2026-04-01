package aprove.verification.oldframework.IntegerReasoning.llvm;

/**
 * Functionality for processing LLVM expressions.
 * @author cryingshadow
 * @version $Id$
 */
abstract class LLVMExpressionUtils {

//    /**
//     * TODO: This is just a pattern matching heuristic. Would real inference be better (precision vs. runtime)?
//     * @param values The value function.
//     * @param rels The known relations.
//     * @param expr An expression.
//     * @return A reference equating the specified expression in the relations of this set. Null if no such reference
//     *         can be found.
//     */
//    public static LLVMReference findReferenceForExpression(
//        final ImmutableMap<LLVMReference, LLVMValue> values,
//        final RelationSet rels,
//        final LLVMExpression expr)
//    {
//        if (expr instanceof LLVMReference) {
//            return (LLVMReference) expr;
//        } else if (expr == null) {
//            return null;
//        }
//        final int limit = rels.computeMaximalNumberOfVariableOccurrences();
//        final BigInteger factorLimit = rels.computeHighestAbsoluteFactor();
//        // set of equal expressions to the original one
//        final Set<Triple<LLVMExpression, BigInteger, BigInteger>> equal =
//            new LinkedHashSet<Triple<LLVMExpression, BigInteger, BigInteger>>();
//        final Set<Triple<LLVMExpression, BigInteger, BigInteger>> newEqual =
//            new LinkedHashSet<Triple<LLVMExpression, BigInteger, BigInteger>>();
//        newEqual.add(expr.toLinear());
//        while (!newEqual.isEmpty()) {
//            equal.addAll(newEqual);
//            final Set<Triple<LLVMExpression, BigInteger, BigInteger>> oldEqual =
//                new LinkedHashSet<Triple<LLVMExpression, BigInteger, BigInteger>>(newEqual);
//            newEqual.clear();
//            for (final Relation rel : rels.getEquations()) {
//                final Triple<LLVMExpression, BigInteger, BigInteger> lhsLinear = rel.getLHS().toLinear();
//                final Triple<LLVMExpression, BigInteger, BigInteger> rhsLinear = rel.getRHS().toLinear();
//                for (final Triple<LLVMExpression, BigInteger, BigInteger> linear : oldEqual) {
//                    if (linear.x.equals(lhsLinear.x) && linear.z.compareTo(lhsLinear.z) == 0) {
//                        // lhsLinear.y + linear.z * linear.x = rhsLinear.y + rhsLinear.z * rhsLinear.x
//                        // linear.y + linear.z * linear.x = (linear.y - lhsLinear.y) + lhsLinear.y + linear.z * linear.x
//                        // = (linear.y - lhsLinear.y) + rhsLinear.y + rhsLinear.z * rhsLinear.x
//                        final BigInteger offset = rhsLinear.y.add(linear.y).subtract(lhsLinear.y);
//                        if (rhsLinear.x instanceof LLVMReference
//                            && offset.compareTo(BigInteger.ZERO) == 0
//                            && rhsLinear.z.compareTo(BigInteger.ONE) == 0)
//                        {
//                            return (LLVMReference) rhsLinear.x;
//                        } else if (rhsLinear.x == null) {
//                            return new LLVMConstRef(rhsLinear.y);
//                        }
//                        newEqual.add(new Triple<LLVMExpression, BigInteger, BigInteger>(
//                            rhsLinear.x,
//                            offset,
//                            rhsLinear.z));
//                    } else if (linear.x.equals(rhsLinear.x) && linear.z.compareTo(rhsLinear.z) == 0) {
//                        // lhsLinear.y + lhsLinear.z * lhsLinear.x = rhsLinear.y + linear.z * linear.x
//                        // linear.y + linear.z * linear.x = (linear.y - rhsLinear.y) + rhsLinear.y + linear.z * linear.x
//                        // = (linear.y - rhsLinear.y) + lhsLinear.y + lhsLinear.z * lhsLinear.x
//                        final BigInteger offset = lhsLinear.y.add(linear.y).subtract(rhsLinear.y);
//                        if (lhsLinear.x instanceof LLVMReference
//                            && offset.compareTo(BigInteger.ZERO) == 0
//                            && lhsLinear.z.compareTo(BigInteger.ONE) == 0)
//                        {
//                            return (LLVMReference) lhsLinear.x;
//                        } else if (lhsLinear.x == null) {
//                            return new LLVMConstRef(lhsLinear.y);
//                        }
//                        newEqual.add(new Triple<LLVMExpression, BigInteger, BigInteger>(
//                            lhsLinear.x,
//                            offset,
//                            lhsLinear.z));
//                    } else {
//                        if (lhsLinear.x instanceof LLVMReference
//                            && (rhsLinear.x == null || rhsLinear.z.remainder(lhsLinear.z).compareTo(BigInteger.ZERO) == 0))
//                        {
//                            final BigInteger offset = rhsLinear.y.subtract(lhsLinear.y);
//                            if (offset.remainder(lhsLinear.z).compareTo(BigInteger.ZERO) == 0) {
//                                final LLVMExpression newExpr =
//                                    linear.x.substitute(Collections.<LLVMReference, LLVMExpression>singletonMap(
//                                        (LLVMReference) lhsLinear.x,
//                                        LLVMOperation.create(
//                                            rhsLinear.x,
//                                            offset.divide(lhsLinear.z),
//                                            rhsLinear.x == null ? null : rhsLinear.z.divide(lhsLinear.z))));
//                                if (
//                                    newExpr.getNumberOfVarOccs() < limit
//                                    && factorLimit.compareTo(newExpr.computeHighestAbsoluteFactor()) >= 0
//                                ) {
//                                    final Triple<LLVMExpression, BigInteger, BigInteger> newLinear = newExpr.toLinear();
//                                    if (newLinear.x != null) {
//                                        newEqual.add(new Triple<LLVMExpression, BigInteger, BigInteger>(
//                                            newLinear.x,
//                                            newLinear.y.multiply(linear.z).add(linear.y),
//                                            newLinear.z.multiply(linear.z)));
//                                    }
//                                }
//                            }
//                        }
//                        if (rhsLinear.x instanceof LLVMReference
//                            && (lhsLinear.x == null || lhsLinear.z.remainder(rhsLinear.z).compareTo(BigInteger.ZERO) == 0))
//                        {
//                            final BigInteger offset = lhsLinear.y.subtract(rhsLinear.y);
//                            if (offset.remainder(rhsLinear.z).compareTo(BigInteger.ZERO) == 0) {
//                                final LLVMExpression newExpr =
//                                    linear.x.substitute(Collections.<LLVMReference, LLVMExpression>singletonMap(
//                                        (LLVMReference) rhsLinear.x,
//                                        LLVMOperation.create(
//                                            lhsLinear.x,
//                                            offset.divide(rhsLinear.z),
//                                            lhsLinear.x == null ? null : lhsLinear.z.divide(rhsLinear.z))));
//                                if (
//                                    newExpr.getNumberOfVarOccs() < limit
//                                    && factorLimit.compareTo(newExpr.computeHighestAbsoluteFactor()) >= 0
//                                ) {
//                                    final Triple<LLVMExpression, BigInteger, BigInteger> newLinear = newExpr.toLinear();
//                                    if (newLinear.x != null) {
//                                        newEqual.add(new Triple<LLVMExpression, BigInteger, BigInteger>(
//                                            newLinear.x,
//                                            newLinear.y.multiply(linear.z).add(linear.y),
//                                            newLinear.z.multiply(linear.z)));
//                                    }
//                                }
//                            }
//                        }
//                    }
//                }
//            }
//            newEqual.removeAll(equal);
//        }
//        // we did not find an equal reference yet - check remainder case
//        for (final Triple<LLVMExpression, BigInteger, BigInteger> linear : equal) {
//            if (!(linear.x instanceof LLVMOperation)
//                || linear.z.compareTo(BigInteger.ONE) != 0
//                || linear.y.compareTo(BigInteger.ZERO) != 0)
//            {
//                continue;
//            }
//            final LLVMOperation op = (LLVMOperation) linear.x;
//            final Triple<LLVMExpression, BigInteger, BigInteger> opLhsLinear = op.getLhs().toLinear();
//            final LLVMExpression opRhs = op.getRhs();
//            if (op.getOpType() != IntArithType.REM
//                || !(opRhs instanceof LLVMConstRef && opLhsLinear.x instanceof LLVMReference))
//            {
//                continue;
//            }
//            final AbstractInt value =
//                LLVMAbstractState.getValue((LLVMReference) opLhsLinear.x, values).getThisAsAbstractInt();
//            if (opLhsLinear.z.compareTo(BigInteger.ONE) < 0 || !value.isNonNegative()) {
//                continue;
//            }
//            // we have an expression of the form (opLhsLinear.y + opLhsLinear.z * opLhsLinear.x) % opRhs
//            for (final Relation rel : rels.getEquations()) {
//                if (rel.getNumberOfVarOccs() != 1) {
//                    continue;
//                }
//                final LLVMExpression lhs = rel.getLHS();
//                final LLVMExpression rhs = rel.getRHS();
//                if (lhs instanceof LLVMOperation) {
//                    if (!(rhs instanceof LLVMConstRef)) {
//                        continue;
//                    }
//                    final LLVMOperation relOp = (LLVMOperation) lhs;
//                    final Triple<LLVMExpression, BigInteger, BigInteger> relOpLhsLinear = relOp.getLhs().toLinear();
//                    final LLVMExpression relOpRhs = relOp.getRhs();
//                    BigInteger offset = opLhsLinear.y.subtract(relOpLhsLinear.y);
//                    if (!(relOp.getOpType() == IntArithType.REM
//                        && opRhs.equals(relOpRhs)
//                        && opLhsLinear.x.equals(relOpLhsLinear.x) && opLhsLinear.z.compareTo(relOpLhsLinear.z) == 0))
//                    {
//                        continue;
//                    }
//                    final BigInteger c = ((LLVMConstRef) opRhs).getValue();
//                    if (offset.compareTo(BigInteger.ZERO) < 0) {
//                        if (value.getLower().compareTo(offset.abs()) < 0) {
//                            continue;
//                        }
//                        while (offset.compareTo(BigInteger.ZERO) < 0) {
//                            offset = offset.add(c);
//                        }
//                    }
//                    // we have a relation of the form (relOpLhsLinear.y + opLhsLinear.z * opLhsLinear.x) % opRhs = rhs
//                    // - this implies (opLhsLinear.y + opLhsLinear.z * opLhsLinear.x) % opRhs =
//                    // (((opLhsLinear.y - relOpLhsLinear.y) % opRhs) + rhs) % opRhs
//                    return new LLVMConstRef(offset.remainder(c).add(((LLVMConstRef) rhs).getValue()).remainder(c));
//                } else if (rhs instanceof LLVMOperation) {
//                    if (!(lhs instanceof LLVMConstRef)) {
//                        continue;
//                    }
//                    final LLVMOperation relOp = (LLVMOperation) rhs;
//                    final Triple<LLVMExpression, BigInteger, BigInteger> relOpLhsLinear = relOp.getLhs().toLinear();
//                    final LLVMExpression relOpRhs = relOp.getRhs();
//                    BigInteger offset = opLhsLinear.y.subtract(relOpLhsLinear.y);
//                    if (!(relOp.getOpType() == IntArithType.REM
//                        && opRhs.equals(relOpRhs)
//                        && opLhsLinear.x.equals(relOpLhsLinear.x) && opLhsLinear.z.compareTo(relOpLhsLinear.z) == 0))
//                    {
//                        continue;
//                    }
//                    final BigInteger c = ((LLVMConstRef) opRhs).getValue();
//                    if (offset.compareTo(BigInteger.ZERO) < 0) {
//                        if (value.getLower().compareTo(offset.abs()) < 0) {
//                            continue;
//                        }
//                        while (offset.compareTo(BigInteger.ZERO) < 0) {
//                            offset = offset.add(c);
//                        }
//                    }
//                    // we have a relation of the form lhs = (relOpLhsLinear.y + opLhsLinear.z * opLhsLinear.x) % opRhs
//                    // - this implies (opLhsLinear.y + opLhsLinear.z * opLhsLinear.x) % opRhs =
//                    // (((opLhsLinear.y - relOpLhsLinear.y) % opRhs) + lhs) % opRhs
//                    return new LLVMConstRef(offset.remainder(c).add(((LLVMConstRef) lhs).getValue()).remainder(c));
//                }
//            }
//        }
//        return null;
//    }
//
//    /**
//     * @param expr The expression.
//     * @param values Value function.
//     * @param strict Strict or weak relation?
//     * @param greater Greater or less than?
//     * @return The set of expressions emerging from the specified one by replacing some refs by extreme constants such
//     *         that the specified expression is known to be in the desired relation to the resulting expressions by the
//     *         specified value function.
//     */
//    public static Set<LLVMExpression> inRelationByReplacingRefsByConstants(
//        final LLVMExpression expr,
//        final ImmutableMap<LLVMReference, LLVMValue> values,
//        final boolean strict,
//        final boolean greater)
//    {
//        if (expr instanceof LLVMConstRef) {
//            return Collections.emptySet();
//        } else if (expr instanceof LLVMVarRef) {
//            if (!values.containsKey(expr)) {
//                return Collections.emptySet();
//            }
//            // TODO the following statement will lead to a cast exception as soon as we have other value types than
//            // integers
//            final AbstractInt val = LLVMAbstractState.getValue((LLVMReference) expr, values).getThisAsAbstractInt();
//            if (greater) {
//                // the variable is greater than its lowest value - 1
//                final IntervalBound smallest = val.getLower();
//                if (!smallest.isFinite()) {
//                    return Collections.emptySet();
//                }
//                BigInteger res = smallest.getConstant();
//                if (strict) {
//                    res = res.subtract(BigInteger.ONE);
//                }
//                return Collections.<LLVMExpression>singleton(new LLVMConstRef(res));
//            } else {
//                // the variable is less than its biggest value + 1
//                final IntervalBound biggest = val.getUpper();
//                if (!biggest.isFinite()) {
//                    return Collections.emptySet();
//                }
//                BigInteger res = biggest.getConstant();
//                if (strict) {
//                    res = res.add(BigInteger.ONE);
//                }
//                return Collections.<LLVMExpression>singleton(new LLVMConstRef(res));
//            }
//        }
//        // here, we know that expr is an operation
//        final LLVMOperation op = (LLVMOperation) expr;
//        final IntArithType opType = op.getOpType();
//        final LLVMExpression lhs = op.getLhs();
//        final LLVMExpression rhs = op.getRhs();
//        final Set<LLVMExpression> res = new LinkedHashSet<LLVMExpression>();
//        switch (opType) {
//        case ADD:
//            LLVMExpressionUtils.addReplacedAdditiveCombinations(
//                op,
//                res,
//                LLVMExpressionUtils.inRelationByReplacingRefsByConstants(lhs, values, false, greater),
//                LLVMExpressionUtils.inRelationByReplacingRefsByConstants(rhs, values, false, greater),
//                strict,
//                greater);
//            return res;
//        case SUB:
//            LLVMExpressionUtils.addReplacedAdditiveCombinations(
//                op,
//                res,
//                LLVMExpressionUtils.inRelationByReplacingRefsByConstants(lhs, values, false, greater),
//                LLVMExpressionUtils.inRelationByReplacingRefsByConstants(rhs, values, false, !greater),
//                strict,
//                greater);
//            return res;
//        case MUL:
//            final Triple<LLVMExpression, BigInteger, BigInteger> origLeftLinear = lhs.toLinear();
//            if (origLeftLinear.x == null) {
//                if (origLeftLinear.y.compareTo(BigInteger.ZERO) > 0) {
//                    for (final LLVMExpression rightExpr : LLVMExpressionUtils.inRelationByReplacingRefsByConstants(
//                        rhs,
//                        values,
//                        false,
//                        greater))
//                    {
//                        final Triple<LLVMExpression, BigInteger, BigInteger> repRightLinear = rightExpr.toLinear();
//                        if (repRightLinear.x == null) {
//                            // this yields a constant
//                            BigInteger offset = repRightLinear.y.multiply(origLeftLinear.y);
//                            if (strict) {
//                                if (greater) {
//                                    offset = offset.subtract(BigInteger.ONE);
//                                } else {
//                                    offset = offset.add(BigInteger.ONE);
//                                }
//                            }
//                            res.add(new LLVMConstRef(offset));
//                        } else {
//                            BigInteger offset = repRightLinear.y.multiply(origLeftLinear.y);
//                            if (strict) {
//                                if (greater) {
//                                    offset = offset.subtract(BigInteger.ONE);
//                                } else {
//                                    offset = offset.add(BigInteger.ONE);
//                                }
//                            }
//                            res.add(LLVMOperation.create(
//                                IntArithType.ADD,
//                                new LLVMConstRef(offset),
//                                LLVMOperation.create(
//                                    IntArithType.MUL,
//                                    new LLVMConstRef(origLeftLinear.y.multiply(repRightLinear.z)),
//                                    repRightLinear.x)));
//                        }
//                    }
//                } else if (origLeftLinear.y.compareTo(BigInteger.ZERO) < 0) {
//                    for (final LLVMExpression rightExpr : LLVMExpressionUtils.inRelationByReplacingRefsByConstants(
//                        rhs,
//                        values,
//                        false,
//                        !greater))
//                    {
//                        final Triple<LLVMExpression, BigInteger, BigInteger> repRightLinear = rightExpr.toLinear();
//                        if (repRightLinear.x == null) {
//                            // this yields a constant
//                            BigInteger offset = repRightLinear.y.multiply(origLeftLinear.y);
//                            if (strict) {
//                                if (greater) {
//                                    offset = offset.subtract(BigInteger.ONE);
//                                } else {
//                                    offset = offset.add(BigInteger.ONE);
//                                }
//                            }
//                            res.add(new LLVMConstRef(offset));
//                        } else {
//                            BigInteger offset = repRightLinear.y.multiply(origLeftLinear.y);
//                            if (strict) {
//                                if (greater) {
//                                    offset = offset.subtract(BigInteger.ONE);
//                                } else {
//                                    offset = offset.add(BigInteger.ONE);
//                                }
//                            }
//                            res.add(LLVMOperation.create(
//                                IntArithType.ADD,
//                                new LLVMConstRef(offset),
//                                LLVMOperation.create(
//                                    IntArithType.MUL,
//                                    new LLVMConstRef(origLeftLinear.y.multiply(repRightLinear.z)),
//                                    repRightLinear.x)));
//                        }
//                    }
//                } else {
//                    return Collections.emptySet();
//                }
//            } else if (lhs.isPositive(values)) {
//                for (final LLVMExpression rightExpr : LLVMExpressionUtils.inRelationByReplacingRefsByConstants(
//                    rhs,
//                    values,
//                    false,
//                    greater))
//                {
//                    LLVMExpression toAdd = LLVMOperation.create(opType, lhs, rightExpr);
//                    if (strict) {
//                        toAdd =
//                            LLVMOperation.create(
//                                IntArithType.ADD,
//                                greater ? LLVMConstRef.NEGONE : LLVMConstRef.ONE,
//                                toAdd);
//                    }
//                    res.add(toAdd);
//                }
//            } else if (lhs.isNegative(values)) {
//                for (final LLVMExpression rightExpr : LLVMExpressionUtils.inRelationByReplacingRefsByConstants(
//                    rhs,
//                    values,
//                    false,
//                    !greater))
//                {
//                    LLVMExpression toAdd = LLVMOperation.create(opType, lhs, rightExpr);
//                    if (strict) {
//                        toAdd =
//                            LLVMOperation.create(
//                                IntArithType.ADD,
//                                greater ? LLVMConstRef.NEGONE : LLVMConstRef.ONE,
//                                toAdd);
//                    }
//                    res.add(toAdd);
//                }
//            } else if (!strict && lhs.isNonNegative(values)) {
//                for (final LLVMExpression rightExpr : LLVMExpressionUtils.inRelationByReplacingRefsByConstants(
//                    rhs,
//                    values,
//                    false,
//                    greater))
//                {
//                    res.add(LLVMOperation.create(opType, lhs, rightExpr));
//                }
//            } else if (!strict && lhs.isNonPositive(values)) {
//                for (final LLVMExpression rightExpr : LLVMExpressionUtils.inRelationByReplacingRefsByConstants(
//                    rhs,
//                    values,
//                    false,
//                    !greater))
//                {
//                    res.add(LLVMOperation.create(opType, lhs, rightExpr));
//                }
//            }
//            final Triple<LLVMExpression, BigInteger, BigInteger> origRightLinear = rhs.toLinear();
//            if (origRightLinear.x == null) {
//                if (origRightLinear.y.compareTo(BigInteger.ZERO) > 0) {
//                    for (final LLVMExpression leftExpr : LLVMExpressionUtils.inRelationByReplacingRefsByConstants(
//                        lhs,
//                        values,
//                        false,
//                        greater))
//                    {
//                        final Triple<LLVMExpression, BigInteger, BigInteger> repLeftLinear = leftExpr.toLinear();
//                        if (repLeftLinear.x == null) {
//                            // this yields a constant
//                            BigInteger offset = repLeftLinear.y.multiply(origRightLinear.y);
//                            if (strict) {
//                                if (greater) {
//                                    offset = offset.subtract(BigInteger.ONE);
//                                } else {
//                                    offset = offset.add(BigInteger.ONE);
//                                }
//                            }
//                            res.add(new LLVMConstRef(offset));
//                        } else {
//                            BigInteger offset = repLeftLinear.y.multiply(origRightLinear.y);
//                            if (strict) {
//                                if (greater) {
//                                    offset = offset.subtract(BigInteger.ONE);
//                                } else {
//                                    offset = offset.add(BigInteger.ONE);
//                                }
//                            }
//                            res.add(LLVMOperation.create(
//                                IntArithType.ADD,
//                                new LLVMConstRef(offset),
//                                LLVMOperation.create(
//                                    IntArithType.MUL,
//                                    new LLVMConstRef(origRightLinear.y.multiply(repLeftLinear.z)),
//                                    repLeftLinear.x)));
//                        }
//                    }
//                } else if (origRightLinear.y.compareTo(BigInteger.ZERO) < 0) {
//                    for (final LLVMExpression leftExpr : LLVMExpressionUtils.inRelationByReplacingRefsByConstants(
//                        lhs,
//                        values,
//                        false,
//                        !greater))
//                    {
//                        final Triple<LLVMExpression, BigInteger, BigInteger> repLeftLinear = leftExpr.toLinear();
//                        if (repLeftLinear.x == null) {
//                            // this yields a constant
//                            BigInteger offset = repLeftLinear.y.multiply(origRightLinear.y);
//                            if (strict) {
//                                if (greater) {
//                                    offset = offset.subtract(BigInteger.ONE);
//                                } else {
//                                    offset = offset.add(BigInteger.ONE);
//                                }
//                            }
//                            res.add(new LLVMConstRef(offset));
//                        } else {
//                            BigInteger offset = repLeftLinear.y.multiply(origRightLinear.y);
//                            if (strict) {
//                                if (greater) {
//                                    offset = offset.subtract(BigInteger.ONE);
//                                } else {
//                                    offset = offset.add(BigInteger.ONE);
//                                }
//                            }
//                            res.add(LLVMOperation.create(
//                                IntArithType.ADD,
//                                new LLVMConstRef(offset),
//                                LLVMOperation.create(
//                                    IntArithType.MUL,
//                                    new LLVMConstRef(origRightLinear.y.multiply(repLeftLinear.z)),
//                                    repLeftLinear.x)));
//                        }
//                    }
//                } else {
//                    return Collections.emptySet();
//                }
//            } else if (rhs.isPositive(values)) {
//                for (final LLVMExpression leftExpr : LLVMExpressionUtils.inRelationByReplacingRefsByConstants(
//                    lhs,
//                    values,
//                    false,
//                    greater))
//                {
//                    LLVMExpression toAdd = LLVMOperation.create(opType, leftExpr, rhs);
//                    if (strict) {
//                        toAdd =
//                            LLVMOperation.create(
//                                IntArithType.ADD,
//                                greater ? LLVMConstRef.NEGONE : LLVMConstRef.ONE,
//                                toAdd);
//                    }
//                    res.add(toAdd);
//                }
//            } else if (rhs.isNegative(values)) {
//                for (final LLVMExpression leftExpr : LLVMExpressionUtils.inRelationByReplacingRefsByConstants(
//                    lhs,
//                    values,
//                    false,
//                    !greater))
//                {
//                    LLVMExpression toAdd = LLVMOperation.create(opType, leftExpr, rhs);
//                    if (strict) {
//                        toAdd =
//                            LLVMOperation.create(
//                                IntArithType.ADD,
//                                greater ? LLVMConstRef.NEGONE : LLVMConstRef.ONE,
//                                toAdd);
//                    }
//                    res.add(toAdd);
//                }
//            } else if (!strict && rhs.isNonNegative(values)) {
//                for (final LLVMExpression leftExpr : LLVMExpressionUtils.inRelationByReplacingRefsByConstants(
//                    lhs,
//                    values,
//                    false,
//                    greater))
//                {
//                    res.add(LLVMOperation.create(opType, leftExpr, rhs));
//                }
//            } else if (!strict && rhs.isNonPositive(values)) {
//                for (final LLVMExpression leftExpr : LLVMExpressionUtils.inRelationByReplacingRefsByConstants(
//                    lhs,
//                    values,
//                    false,
//                    !greater))
//                {
//                    res.add(LLVMOperation.create(opType, leftExpr, rhs));
//                }
//            }
//            return res;
//        case DIV:
//            // TODO
//            return Collections.emptySet();
//        case REM:
//            if (rhs instanceof LLVMConstRef) {
//                if (greater) {
//                    if (lhs.isNonNegative(values)) {
//                        return Collections.<LLVMExpression>singleton(new LLVMConstRef(strict
//                            ? LLVMIntegerUtils.NEGONE
//                                : BigInteger.ZERO));
//                    } else {
//                        return Collections.<LLVMExpression>singleton(new LLVMConstRef(((LLVMConstRef) rhs)
//                            .getValue()
//                            .abs()
//                            .negate()
//                            .add(strict ? BigInteger.ZERO : BigInteger.ONE)));
//                    }
//                } else {
//                    if (lhs.isNonPositive(values)) {
//                        return Collections.<LLVMExpression>singleton(new LLVMConstRef(strict
//                            ? BigInteger.ONE
//                                : BigInteger.ZERO));
//                    } else {
//                        return Collections.<LLVMExpression>singleton(new LLVMConstRef(((LLVMConstRef) rhs)
//                            .getValue()
//                            .abs()
//                            .subtract(strict ? BigInteger.ZERO : BigInteger.ONE)));
//                    }
//                }
//            }
//            return Collections.emptySet();
//        default:
//            return Collections.emptySet();
//        }
//    }
//
//    /**
//     * Adds all combinations of replaced expressions for the left- and right-hand side of an additive expression to the
//     * specified res set.
//     * @param op The additive expression.
//     * @param res The set to add the replaced expressions to.
//     * @param left The expressions to replace the left-hand side with.
//     * @param right The expressions to replace the right-hand side with.
//     * @param strict Strict relation?
//     * @param greater Greater relation?
//     */
//    private static void addReplacedAdditiveCombinations(
//        final LLVMOperation op,
//        final Set<LLVMExpression> res,
//        final Set<LLVMExpression> left,
//        final Set<LLVMExpression> right,
//        final boolean strict,
//        final boolean greater)
//    {
//        final IntArithType opType = op.getOpType();
//        if (Globals.useAssertions) {
//            assert (opType == IntArithType.ADD || opType == IntArithType.SUB) : "This method should only be called on additive expressions!";
//        }
//        final LLVMExpression lhs = op.getLhs();
//        final LLVMExpression rhs = op.getRhs();
//        final Triple<LLVMExpression, BigInteger, BigInteger> origLeftLinear = lhs.toLinear();
//        final Triple<LLVMExpression, BigInteger, BigInteger> origRightLinear = rhs.toLinear();
//        for (final LLVMExpression leftExpr : left) {
//            final Triple<LLVMExpression, BigInteger, BigInteger> repLeftLinear = leftExpr.toLinear();
//            if (repLeftLinear.x == null && origRightLinear.x == null) {
//                // this yields a constant
//                BigInteger constant;
//                switch (opType) {
//                case ADD:
//                    constant = repLeftLinear.y.add(origRightLinear.y);
//                    break;
//                case SUB:
//                    constant = repLeftLinear.y.subtract(origRightLinear.y);
//                    break;
//                default:
//                    throw new IllegalStateException("This method should only be called on additive expressions!");
//                }
//                if (strict) {
//                    if (greater) {
//                        constant = constant.subtract(BigInteger.ONE);
//                    } else {
//                        constant = constant.add(BigInteger.ONE);
//                    }
//                }
//                res.add(new LLVMConstRef(constant));
//            } else {
//                LLVMExpression toAdd = LLVMOperation.create(opType, leftExpr, rhs);
//                if (strict) {
//                    toAdd =
//                        LLVMOperation.create(IntArithType.ADD, greater ? LLVMConstRef.NEGONE : LLVMConstRef.ONE, toAdd);
//                }
//                res.add(toAdd);
//            }
//            for (final LLVMExpression rightExpr : right) {
//                final Triple<LLVMExpression, BigInteger, BigInteger> repRightLinear = rightExpr.toLinear();
//                if (repLeftLinear.x == null && repRightLinear.x == null) {
//                    // this yields a constant
//                    BigInteger constant;
//                    switch (opType) {
//                    case ADD:
//                        constant = repLeftLinear.y.add(repRightLinear.y);
//                        break;
//                    case SUB:
//                        constant = repLeftLinear.y.subtract(repRightLinear.y);
//                        break;
//                    default:
//                        throw new IllegalStateException("This method should only be called on additive expressions!");
//                    }
//                    if (strict) {
//                        if (greater) {
//                            constant = constant.subtract(BigInteger.ONE);
//                        } else {
//                            constant = constant.add(BigInteger.ONE);
//                        }
//                    }
//                    res.add(new LLVMConstRef(constant));
//                } else {
//                    LLVMExpression toAdd = LLVMOperation.create(opType, leftExpr, rightExpr);
//                    if (strict) {
//                        toAdd =
//                            LLVMOperation.create(
//                                IntArithType.ADD,
//                                greater ? LLVMConstRef.NEGONE : LLVMConstRef.ONE,
//                                toAdd);
//                    }
//                    res.add(toAdd);
//                }
//            }
//        }
//        for (final LLVMExpression rightExpr : right) {
//            final Triple<LLVMExpression, BigInteger, BigInteger> repRightLinear = rightExpr.toLinear();
//            if (origLeftLinear.x == null && repRightLinear.x == null) {
//                // this yields a constant
//                BigInteger constant;
//                switch (opType) {
//                case ADD:
//                    constant = origLeftLinear.y.add(repRightLinear.y);
//                    break;
//                case SUB:
//                    constant = origLeftLinear.y.subtract(repRightLinear.y);
//                    break;
//                default:
//                    throw new IllegalStateException("This method should only be called on additive expressions!");
//                }
//                if (strict) {
//                    if (greater) {
//                        constant = constant.subtract(BigInteger.ONE);
//                    } else {
//                        constant = constant.add(BigInteger.ONE);
//                    }
//                }
//                res.add(new LLVMConstRef(constant));
//            } else {
//                LLVMExpression toAdd = LLVMOperation.create(opType, lhs, rightExpr);
//                if (strict) {
//                    toAdd =
//                        LLVMOperation.create(IntArithType.ADD, greater ? LLVMConstRef.NEGONE : LLVMConstRef.ONE, toAdd);
//                }
//                res.add(toAdd);
//            }
//        }
//    }
//
//    /**
//     * Hides default constructor.
//     */
//    private LLVMExpressionUtils() {
//        throw new UnsupportedOperationException("Do not instantiate me!");
//    }

}
