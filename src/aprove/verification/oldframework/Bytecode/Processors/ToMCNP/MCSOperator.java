package aprove.verification.oldframework.Bytecode.Processors.ToMCNP;

import aprove.verification.dpframework.MCSProblem.*;

/**
 *
 * @author Matthias Hoelzel
 *
 */
public enum MCSOperator {
    /**
     * GE: "Greater or equals"
     * LE: "Lower or equals"
     * G : "Greater"
     * L : "Lower"
     * EQ: "Equals"
     */
    MCS_GE, MCS_G, MCS_EQ, MCS_L, MCS_LE;

    @Override
    public String toString() {
        switch (this) {
        case MCS_GE:
            return ">=";
        case MCS_G:
            return ">";
        case MCS_EQ:
            return "=";
        case MCS_L:
            return "<";
        case MCS_LE:
            return "<=";
        default:
            return "??";
        }
    }

    /**
     * Returns this as a MCRelation.
     * @return MCRelation
     */
    public MCRelation toMCRelation() {
        switch (this) {
        case MCS_GE:
            return MCRelation.GE;
        case MCS_G:
            return MCRelation.GT;
        case MCS_LE:
            return MCRelation.LE;
        case MCS_L:
            return MCRelation.LT;
        case MCS_EQ:
            return MCRelation.EQ;
        default:
            return null;
        }
    }
}
