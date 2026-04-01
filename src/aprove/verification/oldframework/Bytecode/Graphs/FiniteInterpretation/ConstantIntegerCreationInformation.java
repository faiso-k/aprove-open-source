package aprove.verification.oldframework.Bytecode.Graphs.FiniteInterpretation;

import java.util.*;

import org.json.*;

import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool.*;

public class ConstantIntegerCreationInformation implements IntegerInformation {
    private final AbstractVariableReference var;
    private final LiteralInt value;

    public ConstantIntegerCreationInformation(
            final AbstractVariableReference ref, final LiteralInt value) {
        this.value = value;
        this.var = ref;
    }

    public AbstractVariableReference getVar() {
        return this.var;
    }

    public LiteralInt getValue() {
        return this.value;
    }

    /**
     * @return a readable string representation
     */
    @Override
    public String toString() {
        // This is boring as hell.
        return "";
        /*
        final StringBuilder sb = new StringBuilder("push: ");
        if (this.var != null) {
            sb.append(this.var.toString());
        }
        sb.append(" with value ");
        if (this.value != null) {
            sb.append(this.value.toString());
        }
        return sb.toString();
        */
    }

    @Override
    public SMTLIBTheoryAtom toSMTAtom(final String varPrefix) {
        return SMTLIBBoolTrue.create();
    }

    /** {@inheritDoc} */
    @Override
    public boolean concernsInterestingRef(final Set<AbstractVariableReference>... interestingRefs) {
        for (final Set<AbstractVariableReference> refSet : interestingRefs) {
            if (refSet == null || refSet.contains(this.var)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public JSONObject toJSON() throws JSONException {
        final JSONObject res = new JSONObject();
        res.put("Information Type", "Int Constant");
        res.put("Int ref", this.getVar().toString());
        res.put("Int value", this.getValue().toString());
        return res;
    }
}
