package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * UnifyFailRule.<br><br>
 *
 * Created: May 4, 2010<br>
 * Last modified: May 4, 2010
 *
 * @author cryingshadow
 * @version $Id$
 */
public class UnifyFailRule extends AbstractInferenceRule {

    /**
     * The terms causing the failure.
     */
    private final Pair<PrologTerm, PrologTerm> clash;

    /**
     * Standard constructor.
     * @param c The terms causing the failure.
     */
    public UnifyFailRule(final Pair<PrologTerm, PrologTerm> c) {
        this.clash = c;
    }

    @Override
    public String prettyToString() {
        StringBuilder res = new StringBuilder();
        res.append("UNIFY-FAIL\\n");
        if (this.clash == null) {
            res.append("because of non-unification");
        } else {
            res.append("with clash: (");
            res.append(this.clash.x.prettyToString());
            res.append(", ");
            res.append(this.clash.y.prettyToString());
            res.append(")");
        }
        return res.toString();
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.UNIFY_FAIL;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        return "    node[auto]\n      {\\textsc{UnifyFail}}\n";
    }

    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        res.append("UNIFY-FAIL\n");
        if (this.clash == null) {
            res.append("because of non-unification");
        } else {
            res.append("with clash: (");
            res.append(this.clash.x.toString());
            res.append(", ");
            res.append(this.clash.y.toString());
            res.append(")");
        }
        return res.toString();
    }

}
