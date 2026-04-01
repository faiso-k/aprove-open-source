package aprove.verification.oldframework.BasicStructures;

import java.util.*;

import org.json.*;

import aprove.verification.oldframework.Utility.JSON.*;
import immutables.*;

/**
 * A binary expression has exactly two arguments.
 * @author cryingshadow
 * @version $Id$
 */
public interface BinaryExpression extends CompoundExpression {

    /**
     * @param exp Some non-null binary expression.
     * @return The arguments of the specified binary expression as immutable list.
     */
    public static ImmutableList<? extends Expression> getArguments(BinaryExpression exp) {
        List<Expression> res = new ArrayList<Expression>();
        res.add(exp.getLhs());
        res.add(exp.getRhs());
        return ImmutableCreator.create(res);
    }

    @Override
    default ImmutableList<? extends Expression> getArguments() {
        return BinaryExpression.getArguments(this);
    }

    @Override
    default int getArity() {
        return 2;
    }

    /**
     * @return The left-hand side.
     */
    Expression getLhs();

    /**
     * @return The right-hand side.
     */
    Expression getRhs();

    @Override
    default BinaryExpression setArguments(ImmutableList<? extends Expression> args) {
        assert (args.size() == 2) : "A binary expression must have exactly two arguments!";
        return this.setLhs(args.get(0)).setRhs(args.get(1));
    }

    /**
     * @param lhs The new left-hand side.
     * @return A binary expression with the specified left-hand side and the current right-hand side.
     */
    BinaryExpression setLhs(Expression lhs);

    /**
     * @param rhs The new right-hand side.
     * @return A binary expression with the current left-hand side and the specified right-hand side.
     */
    BinaryExpression setRhs(Expression rhs);

    @Override
    default Object toJSON() {
        JSONObject res = new JSONObject();
        res.put("type", this.getClass().getSimpleName());
        res.put("operation", this.getName());
        res.put("lhs", JSONExportUtil.toJSON(this.getLhs()));
        res.put("rhs", JSONExportUtil.toJSON(this.getRhs()));
        return res;
    }

    @Override
    default String toPrettyString() {
        StringBuilder res = new StringBuilder();
        res.append("(");
        res.append(this.getLhs().toPrettyString());
        res.append(" ");
        res.append(this.getName());
        res.append(" ");
        res.append(this.getRhs().toPrettyString());
        res.append(")");
        return res.toString();
    }

}
