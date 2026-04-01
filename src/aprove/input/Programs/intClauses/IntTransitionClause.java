package aprove.input.Programs.intClauses;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.IntegerConstraintCleaner.*;
import aprove.verification.oldframework.Utility.*;


public class IntTransitionClause implements Exportable {
    /** Start location of the transition. */
    private final Integer sourceLoc;
    /** Start location of the transition. */
    private final Integer targetLoc;
    /** Condition of the transition. */
    private final TRSTerm condition;

    /**
     * @param source Start location of the transition
     * @param cond Condition of the transition
     * @param target Target location of the transition
     */
    public IntTransitionClause(final Integer source, final TRSTerm cond, final Integer target) {
        this.sourceLoc = source;
        this.condition = cond;
        this.targetLoc = target;
    }

    /** @return Start location of the transition. */
    public Integer getSourceLoc() {
        return this.sourceLoc;
    }

    /** @return Start location of the transition. */
    public Integer getTargetLoc() {
        return this.targetLoc;
    }

    /** @return Condition of the transition. */
    public TRSTerm getCondition() {
        return this.condition;
    }

    /** @return String representation of this transition. */
    public String toConstraint() {
        return this.export(new PLAIN_Util());
    }

    /** @return String representation of this transition. */
    @Override
    public String export(final Export_Util o) {
        final StringBuilder sb = new StringBuilder();
        this.export(o, sb);
        return sb.toString();
    }

    /** Writes String representation of this transition into <code>sb</code>. */
    public void export(final Export_Util o, final StringBuilder sb) {
        sb.append(String.format("PC=%d, PCP=%d, ",
                                this.sourceLoc,
                                this.targetLoc));

        final List<IntegerConstraintRelation> conds = IntegerConstraintCleaner.takeApart(this.condition,
                                                                        new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS));
        boolean isFirst = true;
        for (final IntegerConstraintRelation r : conds) {
            if (isFirst) {
                isFirst = false;
                r.toClauseString(sb);
            } else {
                sb.append(", ");
                r.toClauseString(sb);
            }
        }
    }
}
