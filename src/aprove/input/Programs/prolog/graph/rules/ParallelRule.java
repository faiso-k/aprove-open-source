package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;

/**
 * ParallelRule.<br><br>
 *
 * Created: Sep 3, 2008<br>
 * Last modified: Sep 3, 2008
 *
 * @author cryingshadow
 * @version $Id$
 */
public class ParallelRule extends AbstractInferenceRule {

    /**
     * Flag indicating whether this rule belongs to the left parallel child.
     */
    private final boolean firstChild;

    /**
     * Standard constructor.
     * @param first Is it the left child?
     */
    public ParallelRule(final boolean first) {
        this.firstChild = first;
    }

    /**
     * @return True if this rule belongs to the left parallel child.
     */
    public boolean isFirstChild() {
        return this.firstChild;
    }

    @Override
    public String prettyToString() {
        return "PARALLEL";
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.PARALLEL;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        return "    node[auto]\n      {\\textsc{Parallel}}\n";
    }

    @Override
    public String toString() {
        return "PARALLEL";
    }

}
