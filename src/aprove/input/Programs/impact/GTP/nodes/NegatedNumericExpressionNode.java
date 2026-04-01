package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;


public class NegatedNumericExpressionNode extends NumericExpressionNode {
    NumericExpressionNode exp;

    public NegatedNumericExpressionNode(
        final String text,
        final int line,
        final int position,
        final NumericExpressionNode exp)
    {
        super(text, line, position);
        this.exp = exp;
    }

    @Override
    public HashSet<String> getVariablesId() {
        return this.exp.getVariablesId();
    }

    //    @Override
    //    public SimplePolynomial getNumeratorPolynomial() {
    //        return this.exp.getNumeratorPolynomial().negate();
    //    }
    //
    //    @Override
    //    public SimplePolynomial getDenumeratorPolynomial() {
    //        return this.exp.getDenumeratorPolynomial();
    //    }

    //    @Override
    //    public boolean isNonDet() {
    //        return this.exp.isNonDet();
    //    }

    @Override
    public String toString() {
        final boolean simple = this.exp instanceof SimpleNumericExpressionNode;

        return NegatedNumericExpressionNode.MINUS + (simple ? "" : "(") + this.exp.toString() + (simple ? "" : ")");
    }

    @Override
    public HashSet<String> getVariableNames() {
        return this.exp.getVariableNames();
    }

    private static String MINUS = "-";

    @Override
    public HashSet<VariableNode> getNonDetVariables() {
        return this.exp.getNonDetVariables();
    }

    //    @Override
    //    public SimplePolyFraction getPolyFraction() {
    //        return this.exp.getPolyFraction().negate();
    //    }

    @Override
    public TRSTerm toTerm() {
        return ToolBox.buildMinus(this.exp.toTerm());
    }

}
