package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;

/**
 * CallRule.<br><br>
 *
 * Created: May 4, 2010<br>
 * Last modified: May 4, 2010
 *
 * @author cryingshadow
 * @version $Id$
 */
public class CallRule extends AbstractInferenceRule {

    @Override
    public String prettyToString() {
        return "CALL";
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.CALL;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        return "    node[auto]\n      {\\textsc{Call}}\n";
    }

    @Override
    public String toString() {
        return "CALL";
    }

}
