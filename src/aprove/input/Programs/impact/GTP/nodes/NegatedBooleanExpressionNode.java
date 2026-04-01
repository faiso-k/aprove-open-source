package aprove.input.Programs.impact.GTP.nodes;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;



@SuppressWarnings("javadoc")
public class NegatedBooleanExpressionNode extends BooleanExpressionNode {

    private final BooleanExpressionNode expression;

    public NegatedBooleanExpressionNode(
        final String text,
        final int line,
        final int position,
        final BooleanExpressionNode exp)
    {
        super(text, line, position);
        this.expression = exp;
    }

    @Override
    public String toString() {
        if (this.expression instanceof ConstantBooleanExpressionNode) {
            return this.expression.negate().toString();
        }
        return "!(" + this.expression.toString() + ")";
    }



    @Override
    public BooleanExpressionNode negate() {
        return this.expression;
    }

    /*
    @Override
    public HashSet<String> getVariablesId() {
        return this.expression.getVariablesId();
    }*/

    @Override
    public HashSet<String> getVariableNames() {
        return this.expression.getVariableNames();
    }

    @Override
    public boolean isFalse() {
        return this.expression.isTrue();
    }

    @Override
    public boolean isTrue() {
        return this.expression.isFalse();
    }

    //    @Override
    //    public PolyDisjunction toDisjunction() {
    //        final Abortion aborter = AbortionFactory.create();
    //        final DisjunctionSolver solver = DisjunctionSolver.create(ConstraintsSystemSolver.create(aborter), aborter);
    //        return solver.negate(this.expression.toDisjunction());
    //    }
    //
    //    @Override
    //    public boolean isNonDet() {
    //        return this.expression.isNonDet();
    //    }

    @Override
    public HashSet<VariableNode> getNonDetVariables() {
        return this.expression.getNonDetVariables();
    }

    @Override
    public TRSTerm toTerm() {
        return ToolBox.buildNot(this.expression.toTerm());
    }
}
