package aprove.input.Programs.pushdownSMT;

import java.util.*;

import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.Symbols.*;
import immutables.*;

public final class PushdownInitInformation implements Immutable {
    /** Initial procedure name. */
    private final String name;

    /** Initial location. */
    private final String location;

    /** Its variables. */
    private final ImmutableList<NamedSymbol0<?>> variables;

    /** The constraint on the initial states. */
    private final SMTExpression<SBool> initConstr;

    public PushdownInitInformation(
            String n,
            String l,
            List<NamedSymbol0<?>> vars,
            SMTExpression<SBool> constr) {
        this.name = n;
        this.location = l;
        this.variables = ImmutableCreator.create(vars);
        this.initConstr = constr;
    }

    @Override
    public String toString() {
        final StringBuilder res = new StringBuilder();
        this.toSMTOutput(res);
        return (res.toString());
    }

    public void toSMTOutput(StringBuilder s) {
        s.append("(define-fun init_").append(this.name).append(" (")
         .append(" (pc Loc) ");
        PushdownProcedureInformation.varListToString(s, this.variables);
        s.append(" ) Bool\n")
         .append("  (cfg_init pc ")
         .append(this.location)
         .append(" ")
         .append(this.initConstr.toString())
         .append("))\n\n");
    }
}
