package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.*;

import org.json.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
/**
 * @author ffrohn
 *
 * class representing the edge-labels that mark integer-overflows
 */
public class OverflowInformation implements IntegerInformation {

    /**
     * The arguments of the operation that caused the overflow.
     * Usually, args[0] points to the value that was affected by the overflow.
     */
    private final AbstractVariableReference[] args;

    /**
     * Optional description, might be usefull for debugging.
     */
    private final String description;

    /**
     * Type of the operation that caused the overflow. Set to {@code null} if a cast caused the overflow.
     */
    private final ArithmeticOperationType op;

    /**
     * type of the variable affected by the overflow ({@link Long} or {@link Integer})
     */
    private final IntegerType type;

    /**
     * @param opArg {@link OverflowInformation#op}
     * @param typeArg {@link OverflowInformation#type}
     * @param argsArg {@link OverflowInformation#args}
     */
    public OverflowInformation(
        final ArithmeticOperationType opArg,
        final IntegerType typeArg,
        final AbstractVariableReference... argsArg)
    {
        this(opArg, typeArg, null, argsArg);
    }

    /**
     * @param opArg {@link OverflowInformation#op}
     * @param typeArg {@link OverflowInformation#type}
     * @param argsArg {@link OverflowInformation#args}
     * @param descriptionArg {@link OverflowInformation#description}
     */
    public OverflowInformation(
        final ArithmeticOperationType opArg,
        final IntegerType typeArg,
        final String descriptionArg,
        final AbstractVariableReference... argsArg)
    {
        this.op = opArg;
        this.type = typeArg;
        this.args = argsArg;
        this.description = descriptionArg;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean concernsInterestingRef(final Set<AbstractVariableReference>... interestingRefs) {
        for (final Set<AbstractVariableReference> refs : interestingRefs) {
            if (refs == null) {
                continue;
            }
            for (final AbstractVariableReference arg : this.args) {
                if (refs.contains(arg)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public SMTLIBTheoryAtom toSMTAtom(final String varPrefix) {
        // This method is only used during non-termination analysis. Since overflows and non-termination analysis
        // should not be used together by now, we should never get here.
        assert false;
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        final StringBuilder res = new StringBuilder();
        res.append("OF:");
        if (this.args.length > 0) {
            res.append(this.args[0]);
        }
        if (this.args.length > 1) {
            res.append("=");
            if (this.op == null) {
                res.append("cast");
            } else {
                res.append(this.op.toString());
                res.append('(');
            }
            for (int i = 1; i < this.args.length; i++) {
                res.append(this.args[i]);
                if (i < this.args.length - 1) {
                    res.append(",");
                }
            }
            res.append("),");
            res.append(this.type);
        }
        if (this.description != null) {
            res.append(",");
            res.append(this.description);
        }
        return res.toString();
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        throw new UnsupportedOperationException("JSON export not yet implemented.");
    }
}
