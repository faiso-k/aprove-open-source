package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;

/**
 * NotRule.<br><br>
 *
 * Created: May 4, 2010<br>
 * Last modified: May 4, 2010
 *
 * @author cryingshadow
 * @version $Id$
 */
public class NotRule extends AbstractInferenceRule {

    @Override
    public String prettyToString() {
        return "NOT";
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.NOT;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        return "    node[auto]\n      {\\textsc{Not}}\n";
    }

    @Override
    public String toString() {
        return "NOT";
    }

}
