package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;

/**
 * SplitStep.<br><br>
 *
 * Created: Dec 1, 2006<br>
 * Last modified: Dec 1, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
public class SplitRule extends AbstractInferenceRule {

    /**
     * The information for the right split child. Null indicates that this is the left branch.
     */
    private final SplitCase splitCase;

    /**
     * Standard constructor for left split.
     */
    public SplitRule() {
        this(null);
    }

    /**
     * Standard constructor for right split.
     * @param sCase The information for the right split.
     */
    public SplitRule(final SplitCase sCase) {
        this.splitCase = sCase;
    }

    /**
     * @return The information for the right split.
     */
    public SplitCase getSplitCase() {
        return this.splitCase;
    }

    /**
     * @return True if this rule belongs to the left split.
     */
    public boolean isFirstSplit() {
        return this.splitCase == null;
    }

    @Override
    public String prettyToString() {
        return "SPLIT "
            + ((this.splitCase == null) ? "1" : "2"
                + (this.splitCase.isEmpty() ? "" : "\\n" + this.splitCase.prettyToString()));
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.SPLIT;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        final StringBuilder res = new StringBuilder();
        res.append("    node[auto]\n");
        res.append("      {\\textsc{Split}}\n");
        if (!this.isFirstSplit()) {
            res.append("    node[auto,swap]\n");
            res.append("      {$");
            res.append(this.getSplitCase().getReplacements().restrict(vars).toLaTeX(kb));
            res.append("$}\n");
        }
        return res.toString();
    }

    @Override
    public String toString() {
        return "SPLIT "
            + ((this.splitCase == null) ? "1" : "2"
                + (this.splitCase.isEmpty() ? "" : "\n" + this.splitCase.toString()));
    }

}
