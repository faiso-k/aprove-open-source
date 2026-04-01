package aprove.input.Programs.pushdownSMT;

import java.util.*;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public final class PushdownCallInformation implements Immutable {
    /** Caller procedure name. */
    private final String callerName;

    /** Caller procedure name. */
    private final String calleeName;

    /** The variables of the caller. */
    private final ImmutableList<NamedSymbol0<?>> callerVariables;

    /** The variables of the callee. */
    private final ImmutableList<NamedSymbol0<?>> calleeVariables;

    /** The actual transitions, as (srcLoc, relation, dstLoc) triples. */
    private final ImmutableCollection<Triple<String, SMTExpression<SBool>, String>> calls;

    public PushdownCallInformation(
            String caller,
            String callee,
            List<NamedSymbol0<?>> callerV,
            List<NamedSymbol0<?>> calleeV,
            Collection<Triple<String, SMTExpression<SBool>, String>> cs) {
        this.callerName = caller;
        this.calleeName = callee;
        this.callerVariables = ImmutableCreator.create(callerV);
        this.calleeVariables = ImmutableCreator.create(calleeV);
        this.calls = ImmutableCreator.create(cs);
    }

    @Override
    public String toString() {
        final StringBuilder res = new StringBuilder();
        this.toSMTOutput(res);
        return (res.toString());
    }

    public void toSMTOutput(StringBuilder s) {
        s.append("(define-fun ").append(this.callerName).append("_call_").append(this.calleeName).append(" (\n")
         .append("                 (pc Loc) ");
        PushdownProcedureInformation.varListToString(s, this.calleeVariables);
        s.append("\n                 (pc1 Loc) ");
        PushdownProcedureInformation.varListToString(s, this.callerVariables);
        s.append("\n             ) Bool\n")
         .append("  (or\n");
        for (Triple<String, SMTExpression<SBool>, String> t : this.calls) {
            s.append("    ");
            PushdownProcedureInformation.trans2ToString(s, t);
            s.append("\n");
        }
        s.append("  )\n)\n");
    }
}
