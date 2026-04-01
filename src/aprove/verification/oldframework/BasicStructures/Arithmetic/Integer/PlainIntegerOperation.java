package aprove.verification.oldframework.BasicStructures.Arithmetic.Integer;

import java.util.*;

import org.json.*;

import aprove.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.Utility.JSON.*;
import immutables.*;

/**
 * Plain integer operation.
 * @author cryingshadow
 * @version $Id$
 */
public class PlainIntegerOperation implements CompoundFunctionalIntegerExpression {

    /**
     * The arguments. Its size must match the arity of the operation.
     */
    private final ImmutableList<FunctionalIntegerExpression> arguments;

    /**
     * The operation.
     */
    private final ArithmeticOperationType operation;

    /**
     * @param opType The operation.
     * @param args The arguments.
     */
    public PlainIntegerOperation(ArithmeticOperationType opType, FunctionalIntegerExpression... args) {
        if (Globals.useAssertions) {
            assert (args.length == opType.getArity()) : "Arguments' size must match operation arity!";
        }
        this.operation = opType;
        this.arguments = ImmutableCreator.create(Arrays.asList(args));
    }

    /**
     * @param opType The operation.
     * @param args The arguments.
     */
    public PlainIntegerOperation(ArithmeticOperationType opType, List<FunctionalIntegerExpression> args) {
        if (Globals.useAssertions) {
            assert (args.size() == opType.getArity()) : "Arguments' size must match operation arity!";
        }
        this.operation = opType;
        this.arguments = ImmutableCreator.create(args);
    }

    @Override
    public PlainIntegerOperation applySubstitution(Substitution sigma) {
        List<FunctionalIntegerExpression> args = new ArrayList<FunctionalIntegerExpression>();
        for (FunctionalIntegerExpression arg : this.getArguments()) {
            args.add((FunctionalIntegerExpression)arg.applySubstitution(sigma));
        }
        return new PlainIntegerOperation(this.getOperation(), args);
    }

    @Override
    public boolean equals(Object o) {
        if (o == null) {
            return false;
        }
        if (this == o) {
            return true;
        }
        if (!this.getClass().equals(o.getClass())) {
            return false;
        }
        PlainIntegerOperation other = (PlainIntegerOperation)o;
        return this.getOperation().equals(other.getOperation()) && this.getArguments().equals(other.getArguments());
    }

    @Override
    public ImmutableList<? extends FunctionalIntegerExpression> getArguments() {
        return this.arguments;
    }

    @Override
    public ArithmeticOperationType getOperation() {
        return this.operation;
    }

    @Override
    public int hashCode() {
        return this.getClass().hashCode() + this.getOperation().hashCode() + this.getArguments().hashCode();
    }

    @Override
    public FunctionalIntegerExpression negate() {
        if (this.getOperation() == ArithmeticOperationType.NEG) {
            return this.getArguments().get(0);
        } else {
            return new PlainIntegerOperation(ArithmeticOperationType.NEG, this);
        }
    }

    @Override
    @SuppressWarnings("unchecked")
    public PlainIntegerOperation setArguments(ImmutableList<? extends Expression> args) {
        return new PlainIntegerOperation(this.getOperation(), (ImmutableList<FunctionalIntegerExpression>)args);
    }

    @Override
    public Object toJSON() {
        JSONObject res = new JSONObject();
        res.put("type", this.getClass().getSimpleName());
        res.put("operation", JSONExportUtil.toJSON(this.getOperation()));
        res.put("arguments", JSONExportUtil.toJSON(this.getArguments()));
        return res;
    }

    @Override
    public SMTExpression<SInt> toSMTExp() {
        final ImmutableList<? extends FunctionalIntegerExpression> args = this.getArguments();
        switch (this.getOperation()) {
            case ADD:
                return Ints.add(args.get(0).toSMTExp(), args.get(1).toSMTExp());
            case SUB:
                return Ints.subtract(args.get(0).toSMTExp(), args.get(1).toSMTExp());
            case MUL:
                return Ints.times(args.get(0).toSMTExp(), args.get(1).toSMTExp());
            case EIDIV:
                return Ints.div(args.get(0).toSMTExp(), args.get(1).toSMTExp());
            case EMOD:
                return Ints.mod(args.get(0).toSMTExp(), args.get(1).toSMTExp());
            case NEG:
                return Ints.negate(args.get(0).toSMTExp());
            default:
                throw new UnsupportedOperationException("No viable cases left. Operation: " + this.getOperation());
        }
    }

    @Override
    public String toString() {
        return this.toPrettyString();
    }

}
