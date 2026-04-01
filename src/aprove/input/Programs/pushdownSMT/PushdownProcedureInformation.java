package aprove.input.Programs.pushdownSMT;

import java.util.*;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public final class PushdownProcedureInformation implements Immutable {
    /** Procedure name. */
    private final String name;

    /** The pre-variables. */
    private final ImmutableList<NamedSymbol0<?>> preVariables;

    /** The post-variables. */
    private final ImmutableList<NamedSymbol0<?>> postVariables;

    /** The actual transitions, as (srcLoc, relation, dstLoc) triples. */
    private final ImmutableCollection<Triple<String, SMTExpression<SBool>, String>> transitions;

    public PushdownProcedureInformation(
            String n,
            List<NamedSymbol0<?>> preV,
            List<NamedSymbol0<?>> postV,
            Collection<Triple<String, SMTExpression<SBool>, String>> trans) {
        this.name = n;
        this.preVariables = ImmutableCreator.create(preV);
        this.postVariables = ImmutableCreator.create(postV);
        this.transitions = ImmutableCreator.create(trans);
    }

    /** @return the set of locations appearing in transition in this procedure. */
    public Set<String> getUsedLocations() {
        Set<String> res = new LinkedHashSet<>();
        for (Triple<String, SMTExpression<SBool>, String> t : this.transitions) {
            res.add(t.x);
            res.add(t.z);
        }
        return res;
    }

    @Override
    public String toString() {
        final StringBuilder res = new StringBuilder();
        this.toSMTOutput(res);
        return (res.toString());
    }

    static void varListToString(StringBuilder s, List<NamedSymbol0<?>> vars) {
        boolean isFirst = true;
        for (NamedSymbol0<?> sym : vars) {
            if (isFirst) {
                isFirst = false;
            } else {
                s.append(" ");
            }
            s.append("(")
             .append(sym.getName())
             .append(" ")
             .append(sym.getReturnSort().toString())
              .append(")");
        }
    }

    static void trans2ToString(StringBuilder s, Triple<String, SMTExpression<SBool>, String> trans) {
        s.append("(cfg_trans2 pc ")
         .append(trans.x)
         .append(" pc1 ")
         .append(trans.z)
         .append(" ")
         .append(trans.y.toString())
         .append(")");
    }

    public void toSMTOutput(StringBuilder s) {
        s.append("(define-fun next_").append(this.name).append(" (\n")
         .append("                 (pc Loc) ");
        PushdownProcedureInformation.varListToString(s, this.preVariables);
        s.append("\n                 (pc1 Loc) ");
        PushdownProcedureInformation.varListToString(s, this.postVariables);
        s.append("\n             ) Bool\n")
         .append("  (or\n");
        for (Triple<String, SMTExpression<SBool>, String> t : this.transitions) {
            s.append("    ");
            PushdownProcedureInformation.trans2ToString(s, t);
            s.append("\n");
        }
        s.append("  )\n)\n");
    }
}
