package aprove.input.Programs.pushdownSMT;

import java.util.*;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public final class PushdownReturnInformation implements Immutable {
    /** Caller procedure name. */
    private final String callerName;

    /** Caller procedure name. */
    private final String calleeName;

    /** The pre-variables of the caller (i.e., at the call site). */
    private final ImmutableList<NamedSymbol0<?>> callerPreVariables;

    /** The post-variables of the caller (i.e., after the call was executed). */
    private final ImmutableList<NamedSymbol0<?>> callerPostVariables;

    /** The variables of the callee when exiting the called procedure. */
    private final ImmutableList<NamedSymbol0<?>> calleeExitVariables;

    /** The actual returns, as (exitLoc, callLoc, rel, returnLoc) triples. */
    private final ImmutableCollection<Quadruple<String, String, SMTExpression<SBool>, String>> returns;

    public PushdownReturnInformation(
            String caller,
            String callee,
            List<NamedSymbol0<?>> calleeExitV,
            List<NamedSymbol0<?>> callerPreV,
            List<NamedSymbol0<?>> callerPostV,
            Collection<Quadruple<String, String, SMTExpression<SBool>, String>> cs) {
        this.callerName = caller;
        this.calleeName = callee;
        this.calleeExitVariables = ImmutableCreator.create(calleeExitV);
        this.callerPreVariables = ImmutableCreator.create(callerPreV);
        this.callerPostVariables = ImmutableCreator.create(callerPostV);
        this.returns = ImmutableCreator.create(cs);
    }

    @Override
    public String toString() {
        final StringBuilder res = new StringBuilder();
        this.toSMTOutput(res);
        return (res.toString());
    }

    static void trans3ToString(StringBuilder s, Quadruple<String, String, SMTExpression<SBool>, String> trans) {
        s.append("(cfg_trans3 pc ")
         .append(trans.x)
         .append(" pc1 ")
         .append(trans.y)
         .append(" pc2 ")
         .append(trans.w)
         .append(" ")
         .append(trans.z.toString())
         .append(")\n");
    }

    public void toSMTOutput(StringBuilder s) {
        s.append("(define-fun ").append(this.callerName).append("_return_").append(this.calleeName).append(" (\n")
         .append(  "                 (pc Loc) ");
        PushdownProcedureInformation.varListToString(s, this.calleeExitVariables);
        s.append("\n                 (pc1 Loc) ");
        PushdownProcedureInformation.varListToString(s, this.callerPreVariables);
        s.append("\n                 (pc2 Loc) ");
        PushdownProcedureInformation.varListToString(s, this.callerPostVariables);
        s.append("\n             ) Bool\n")
         .append("  (or\n");
        for (Quadruple<String, String, SMTExpression<SBool>, String> t : this.returns) {
            s.append("    ");
            PushdownReturnInformation.trans3ToString(s, t);
            s.append("\n");
        }
        s.append("  )\n)\n");
    }
}
