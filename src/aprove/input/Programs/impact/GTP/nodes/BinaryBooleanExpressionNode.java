package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;

@SuppressWarnings("javadoc")
public class BinaryBooleanExpressionNode extends BooleanExpressionNode {

    private final NumericExpressionNode expressionA;
    private final NumericExpressionNode expressionB;
    private final Type type;

    public BinaryBooleanExpressionNode(
        final String text,
        final int line,
        final int position,
        final NumericExpressionNode expA,
        final NumericExpressionNode expB,
        final Type t)
    {
        super(text, line, position);
        this.expressionA = expA;
        this.expressionB = expB;
        this.type = t;
    }


    @Override
    public String toString() {
        return this.expressionA.toString() + " " + this.type.getSymbol() + " " + this.expressionB.toString();
    }

    public enum Type {
        EQUAL("=="), GREATER(">"), GREATER_EQ(">=");

        private String symbol;

        private Type(final String s) {
            this.symbol = s;
        }

        public String getSymbol() {
            return this.symbol;
        }
    }

    public NumericExpressionNode getLeftExpression() {
        return this.expressionA;
    }

    public NumericExpressionNode getRightExpression() {
        return this.expressionB;
    }

    public Type getType() {
        return this.type;
    }

    //    public static PolyDisjunction createDisjunction(
    //        SimplePolynomial numenator,
    //        final SimplePolynomial denumenator,
    //        final Type t)
    //    {
    //        if (numenator == null) {
    //            return PolyDisjunction.TRUE;
    //        }
    //
    //        if (denumenator.isConstant()) {
    //            if (denumenator.getNumericalAddend().compareTo(BigInteger.ZERO) < 0) {
    //                numenator = numenator.times(SimplePolynomial.MINUS_ONE);
    //            }
    //
    //            if (numenator.isConstant()) {
    //                final int cmp = numenator.getNumericalAddend().compareTo(BigInteger.ZERO);
    //
    //                switch (t) {
    //                case EQUAL:
    //                    return PolyDisjunction.create(cmp == 0);
    //                case GREATER:
    //                    return PolyDisjunction.create(cmp > 0);
    //                case GREATER_EQ:
    //                    return PolyDisjunction.create(cmp >= 0);
    //                default:
    //                    //return null;
    //                }
    //            }
    //
    //            PolyConstraintsSystem conSys = PolyConstraintsSystem.TRUE;
    //
    //            switch (t) {
    //            case EQUAL:
    //                conSys = conSys.addConstraint(new SimplePolyConstraint(numenator, ConstraintType.EQ));
    //                break;
    //            case GREATER:
    //                conSys = conSys.addConstraint(new SimplePolyConstraint(numenator, ConstraintType.GT));
    //                break;
    //            case GREATER_EQ:
    //                conSys = conSys.addConstraint(new SimplePolyConstraint(numenator, ConstraintType.GE));
    //                break;
    //            default:
    //                //return null;
    //            }
    //
    //
    //            return PolyDisjunction.create(conSys);
    //
    //        } else {
    //            final PolyConstraintsSystem denumenatorPositive =
    //                PolyConstraintsSystem.create(new SimplePolyConstraint(denumenator, ConstraintType.GT));
    //
    //            final HashSet<SimplePolynomial> denNegProduct = new HashSet<>();
    //            denNegProduct.add(denumenator);
    //            denNegProduct.add(SimplePolynomial.MINUS_ONE);
    //
    //            final PolyConstraintsSystem denumenatorNegative =
    //                PolyConstraintsSystem.create(new SimplePolyConstraint(
    //                    SimplePolynomial.times(denNegProduct),
    //                    ConstraintType.GT));
    //
    //            final PolyDisjunction denumenatorNonzero =
    //                PolyDisjunction.create(denumenatorPositive, denumenatorNegative);
    //            //denumenatorNonzero = denumenatorNonzero.addSystem(denumenatorPositive);
    //            //denumenatorNonzero = denumenatorNonzero.addSystem(denumenatorNegative);
    //
    //
    //            final PolyConstraintsSystem numenatorZero =
    //                PolyConstraintsSystem.create(new SimplePolyConstraint(numenator, ConstraintType.EQ));
    //
    //            final PolyConstraintsSystem numenatorPositive =
    //                PolyConstraintsSystem.create(new SimplePolyConstraint(numenator, ConstraintType.GT));
    //
    //            final HashSet<SimplePolynomial> numNegProduct = new HashSet<>();
    //            numNegProduct.add(numenator);
    //            numNegProduct.add(SimplePolynomial.MINUS_ONE);
    //
    //            final PolyConstraintsSystem numenatorNegative =
    //                PolyConstraintsSystem.create(new SimplePolyConstraint(
    //                    SimplePolynomial.times(numNegProduct),
    //                    ConstraintType.GT));
    //
    //            final PolyConstraintsSystem numenatorNonnegative =
    //                PolyConstraintsSystem.create(new SimplePolyConstraint(numenator, ConstraintType.GE));
    //            final PolyConstraintsSystem numenatorNonpositive =
    //                PolyConstraintsSystem.create(new SimplePolyConstraint(
    //                    SimplePolynomial.times(numNegProduct),
    //                    ConstraintType.GE));
    //
    //            switch (t) {
    //            case EQUAL:
    //                return denumenatorNonzero.mergeSystem(numenatorZero);
    //
    //                // return Formula.and(numenatorZero, denumenatorNonzero);
    //            case GREATER:
    //                final PolyDisjunction resultG = PolyDisjunction.create(denumenatorNegative, denumenatorPositive);
    //
    //                // resultG.add((PolyConstraintsSystem) numenatorPositive.merge(denumenatorNegative));
    //                // resultG.add((PolyConstraintsSystem) numenatorNegative.merge(denumenatorPositive));
    //
    //                return resultG;
    //
    //                /*  return Formula.or(
    //                      Formula.and(numenatorPositive, denumenatorNegative),
    //                      Formula.and(numenatorNegative, denumenatorPositive)); */
    //            case GREATER_EQ:
    //                final PolyDisjunction resultE = PolyDisjunction.create(denumenatorNegative, denumenatorPositive);
    //
    //                return resultE;
    //
    //                /* return Formula.or(
    //                     Formula.and(numenatorNonnegative, denumenatorNegative),
    //                     Formula.and(numenatorNonpositive, denumenatorPositive)); */
    //            default:
    //                return null;
    //            }
    //        }
    //    }



    @Override
    public BooleanExpressionNode negate() {
        switch (this.type) {
        case EQUAL:
            return new ComplexBooleanExpressionNode(
                null,
                0,
                0,
                new BinaryBooleanExpressionNode(
                    null,
                    0,
                    0,
                    this.expressionB,
                    this.expressionA,
                    Type.GREATER), new BinaryBooleanExpressionNode(
                        null,
                        0,
                        0,
                        this.expressionA,
                        this.expressionB,
                        Type.GREATER),
                        ComplexBooleanExpressionNode.Type.OR);
        case GREATER:
            return new BinaryBooleanExpressionNode(null, 0, 0, this.expressionB, this.expressionA, Type.GREATER_EQ);
        case GREATER_EQ:
            return new BinaryBooleanExpressionNode(null, 0, 0, this.expressionB, this.expressionA, Type.GREATER);
        default:
            return null;
        }
    }

    @Override
    public HashSet<String> getVariableNames() {
        final HashSet<String> result = (HashSet<String>) this.expressionA.getVariableNames().clone();
        result.addAll(this.expressionB.getVariableNames());
        return result;
    }

    @Override
    public
    boolean isFalse() {
        if (this.expressionA instanceof ConstantNumericExpressionNode
            && this.expressionB instanceof ConstantNumericExpressionNode)
        {
            final long valueA = ((ConstantNumericExpressionNode) this.expressionA).getValue();
            final long valueB = ((ConstantNumericExpressionNode) this.expressionB).getValue();

            switch (this.type) {
            case EQUAL:
                return valueA != valueB;
            case GREATER:
                return valueA <= valueB;
            case GREATER_EQ:
                return valueA < valueB;
            default:
                return false;
            }

        }

        return false;
    }

    @Override
    public boolean isTrue() {
        if (this.expressionA instanceof ConstantNumericExpressionNode
            && this.expressionB instanceof ConstantNumericExpressionNode)
        {
            final long valueA = ((ConstantNumericExpressionNode) this.expressionA).getValue();
            final long valueB = ((ConstantNumericExpressionNode) this.expressionB).getValue();

            switch (this.type) {
            case EQUAL:
                return valueA == valueB;
            case GREATER:
                return valueA > valueB;
            case GREATER_EQ:
                return valueA >= valueB;
            default:
                return false;
            }

        }

        return false;
    }

    //    @Override
    //    public PolyDisjunction toDisjunction() {
    //
    //        final NumericExpressionNode combinedExp =
    //            new BinrayNumericExpressionNode(
    //                "",
    //                0,
    //                0,
    //                this.expressionA,
    //                this.expressionB,
    //                BinrayNumericExpressionNode.Type.SUB);
    //
    //        return createDisjunction(combinedExp.getPolyFraction().getNumenator(), combinedExp
    //            .getPolyFraction()
    //            .getDenumenator(), this.type);
    //
    //        //            switch (this.type) {
    //        //            case EQUAL:
    //        //                return new SimpleFracConstraint(combinedExp, ConstraintType.EQ).toConstraintsSystem();
    //        //            case GREATER:
    //        //                return valueA > valueB;
    //        //            case GREATER_EQ:
    //        //                return valueA >= valueB;
    //        //            default:
    //        //                return false;
    //        //            }
    //        //
    //        //            final SimplePolynomial numenator = combinedExp.getPolyFraction().getNumenator();
    //        //            final SimplePolynomial denumenator = combinedExp.getPolyFraction().getDenumenator();
    //        //
    //        //            return BinaryBooleanExpressionNode.createDisjunction(numenator, denumenator, this.type);
    //    }


    //    @Override
    //    public boolean isNonDet() {
    //        return this.expressionA.isNonDet() || this.expressionB.isNonDet();
    //    }


    @Override
    public HashSet<VariableNode> getNonDetVariables() {
        final HashSet<VariableNode> variables = this.expressionA.getNonDetVariables();
        variables.addAll(this.expressionB.getNonDetVariables());
        return variables;
    }

    @Override
    public TRSTerm toTerm() {
        switch (this.type) {
        case EQUAL:
            return ToolBox.buildEq(this.expressionA.toTerm(), this.expressionB.toTerm());
        case GREATER:
            return ToolBox.buildGt(this.expressionA.toTerm(), this.expressionB.toTerm());
        case GREATER_EQ:
            return ToolBox.buildGe(this.expressionA.toTerm(), this.expressionB.toTerm());
        default:
            throw new RuntimeException();
        }
    }
}
