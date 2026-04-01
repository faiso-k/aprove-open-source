package aprove.verification.oldframework.BasicStructures;

import java.util.*;

import immutables.*;

/**
 * A compound expression has at least one sub-expression/argument/parameter.
 * @author cryingshadow
 * @version $Id$
 */
public interface CompoundExpression extends Expression, HasArity {

    /**
     * @param exp Some compound expression.
     * @return The set of all variables occurring in the specified expression.
     */
    public static Set<? extends Variable> getVariables(CompoundExpression exp) {
        Set<Variable> res = new LinkedHashSet<Variable>();
        for (Expression arg : exp.getArguments()) {
            res.addAll(arg.getVariables());
        }
        return res;
    }

    @Override
    default Expression accept(Visitor<Expression, Expression> v) {
        List<Expression> args = new ArrayList<Expression>();
        for (Expression t : this.getArguments()) {
            args.add(t.accept(v));
        }
        return v.visit(this.setArguments(ImmutableCreator.create(args)));
    }

    @Override
    default CompoundExpression applySubstitution(Map<? extends Variable, ? extends Expression> sigma) {
        return this.applySubstitution(Substitution.toSubstitution(sigma));
    }

    @Override
    default CompoundExpression applySubstitution(Substitution sigma) {
        return Substitution.applySubstitution(this, sigma);
    }

    /**
     * @return The non-empty list of arguments of this compound expression.
     */
    ImmutableList<? extends Expression> getArguments();

    @Override
    default Set<? extends Variable> getVariables() {
        return CompoundExpression.getVariables(this);
    }

    /**
     * @param args The new arguments.
     * @return A FunctionApplication with the same FunctionSymbol as the one of this FunctionApplication and with the
     *         specified arguments.
     */
    CompoundExpression setArguments(ImmutableList<? extends Expression> args);

    @Override
    default String toPrettyString() {
        StringBuilder res = new StringBuilder();
        res.append(this.getName());
        ImmutableList<? extends Expression> args = this.getArguments();
        if (!args.isEmpty()) {
            res.append("(");
            Iterator<? extends Expression> it = args.iterator();
            res.append(it.next().toPrettyString());
            while (it.hasNext()) {
                res.append(", ");
                res.append(it.next().toPrettyString());
            }
            res.append(")");
        }
        return res.toString();
    }

    @Override
    default String toSExpressionString() {
        StringBuilder res = new StringBuilder();
        res.append("( ");
        res.append(this.getName());
        for (Expression arg : this.getArguments()) {
            res.append(" ");
            res.append(arg.toSExpressionString());
        }
        res.append(" )");
        return res.toString();
    }

}
