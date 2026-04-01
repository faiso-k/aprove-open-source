package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;

/**
 * UndefinedErrorRule.<br><br>
 *
 * Created: May 4, 2010<br>
 * Last modified: May 4, 2010
 *
 * @author cryingshadow
 * @version $Id$
 */
public class UndefinedErrorRule extends AbstractInferenceRule {

    @Override
    public String prettyToString() {
        return "UNDEFINED ERROR";
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.UNDEFINED_ERROR;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        return "    node[auto]\n      {\\textsc{UndefinedError}}\n";
    }

    @Override
    public String toString() {
        return "UNDEFINED ERROR";
    }

}
