package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;

/**
 * InstanceStep.<br><br>
 *
 * Created: Dec 1, 2006<br>
 * Last modified: Dec 1, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
public class InstanceRule extends AbstractInferenceRule {

    /**
     * The matcher.
     */
    private PrologSubstitution matcher;

    /**
     * Standard constructor.
     * @param mu The matcher.
     */
    public InstanceRule(final PrologSubstitution mu) {
        if (mu == null) {
            this.matcher = new PrologSubstitution();
        } else {
            this.matcher = mu;
        }
    }

    /**
     * @return The matcher.
     */
    public PrologSubstitution getMatcher() {
        return this.matcher;
    }

    @Override
    public String prettyToString() {
        String res = "INSTANCE";
        if (!this.matcher.isEmpty()) {
            res += " with matching:";
            for (final Map.Entry<PrologVariable, PrologTerm> entry : this.matcher.entrySet()) {
                res += "\\n" + entry.getKey().prettyToString() + " -> " + entry.getValue().prettyToString();
            }
        }
        return res;
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.INSTANCE;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        final StringBuilder res = new StringBuilder();
        res.append("    node[auto]\n");
        res.append("      {\\textsc{Inst}}\n");
        res.append("    node[auto,swap]\n");
        res.append("      {$");
        res.append(this.getMatcher().restrict(vars).toLaTeX(kb));
        res.append("$}\n");
        return res.toString();
    }

    @Override
    public String toString() {
        String res = "INSTANCE";
        if (!this.matcher.isEmpty()) {
            res += " with matching:";
            for (final Map.Entry<PrologVariable, PrologTerm> entry : this.matcher.entrySet()) {
                res += "\n" + entry.getKey().toString() + " -> " + entry.getValue().toString();
            }
        }
        return res;
    }

}
