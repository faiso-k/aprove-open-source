package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * BacktrackStep.<br><br>
 *
 * Created: Sep 3, 2008<br>
 * Last modified: Sep 3, 2008
 *
 * @author cryingshadow
 * @version $Id$
 */
public class BacktrackRule extends AbstractInferenceRule {

    /**
     * The terms causing the failure.
     */
    private final Pair<PrologTerm, PrologTerm> clash;

    /**
     * The applied clause.
     */
    private final PrologClause clause;

    /**
     * Standard constructor.
     * @param clau The applied clause.
     * @param clas The terms causing the failure.
     */
    public BacktrackRule(final PrologClause clau, final Pair<PrologTerm, PrologTerm> clas) {
        if (clau == null) {
            throw new NullPointerException("Clause must not be null!");
        }
        this.clause = clau;
        this.clash = clas;
    }

    @Override
    public String prettyToString() {
        return "BACKTRACK"
            + "\\n"
            + "for clause: "
            + this.clause.prettyToString()
            + (this.clash == null ? "because of non-unification" : "\\n"
                + "with clash: ("
                + this.clash.x.prettyToString()
                + ", "
                + this.clash.y.prettyToString()
                + ")");
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.BACKTRACK;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        return "    node[auto]\n      {\\textsc{Backtrack}}\n";
    }

    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        res.append("BACKTRACK\nfor clause: ");
        res.append(this.clause.toString());
        if (this.clash == null) {
            res.append("because of non-unification");
        } else {
            res.append("\nwith clash: (");
            res.append(this.clash.x.toString());
            res.append(", ");
            res.append(this.clash.y.toString());
            res.append(")");
        }
        return res.toString();
    }

}
