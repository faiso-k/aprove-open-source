package aprove.verification.oldframework.Logic;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.complexity.TruthValue.*;


/**
 * Implications can be either SOUND, COMPLETE, EQUIVALENT
 * or ANTIVALENT.
 * @author nowonder, rabe
 * @version $Id$
 */

public enum YNMImplication implements Implication {
    SOUND {
        @Override
        public TruthValue propagate(TruthValue val) {
            if (val == YNM.YES) {
                return YNM.YES;
            }
            return YNM.MAYBE;
        }
        @Override
        public String toRepresentation() {
            return "<=";
        }
        @Override
        public String export(Export_Util o) {
            return o.implication();
        }
    },
    COMPLETE {
        @Override
        public TruthValue propagate(TruthValue val) {
            if (val == YNM.NO) {
                return YNM.NO;
            }
            return YNM.MAYBE;
        }
        @Override
        public String toRepresentation() {
            return "=>";
        }
        @Override
        public String export(Export_Util o) {
            return o.complete();
        }
    },
    EQUIVALENT {
        @Override
        public TruthValue propagate(TruthValue val) {
            if (!Globals.DEBUG_NONE && val instanceof ComplexityYNM) {
                StringBuilder sb = new StringBuilder();
                sb.append("warning: using YNMImplication.EQUIVALENT for complexity values");
                sb.append(System.lineSeparator());
                sb.append("This is a bad idea, since there are processors which are used for termination and complexity analysis.");
                sb.append(System.lineSeparator());
                sb.append("However, equivalence for termination and equivalence for complexity are orthogonal in general.");
                sb.append(System.lineSeparator());
                sb.append("Moreover, AProVE nowadays also supports concrete (as opposed to asymptotic) bounds.");
                sb.append(System.lineSeparator());
                sb.append("However, equivalence for asymptotic complexity does not imply equivalence for concrete complexity.");
                sb.append(System.lineSeparator());
                sb.append("Hence, please use the appropriate implications to clearly indicate whether a processor is equivalent for termination, (concrete) complexity, or both.");
                System.err.println(sb);
            }
            return val;
        }
        @Override
        public String toRepresentation() {
            return "<=>";
        }
        @Override
        public String export(Export_Util o) {
            return o.equivalent();
        }
    },
    ANTIVALENT {
        @Override
        public TruthValue propagate(TruthValue val) {
            return val.not();
        }
        @Override
        public String toRepresentation() {
            return "<=/=>";
        }
        @Override
        public String export(Export_Util o) {
            // TODO wasn't shown before, show now?
            return "";
        }
    };

    public abstract String toRepresentation();
}
