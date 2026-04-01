package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;

/**
 * VariableErrorRule.<br><br>
 *
 * Created: May 4, 2010<br>
 * Last modified: May 4, 2010
 *
 * @author cryingshadow
 * @version $Id$
 */
public class VariableErrorRule extends AbstractInferenceRule {

    @Override
    public String prettyToString() {
        return "VARIABLE ERROR";
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.VARIABLE_ERROR;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        return "    node[auto]\n      {\\textsc{UnifySuc}}\n";
    }

    @Override
    public String toString() {
        return "VARIABLE ERROR";
    }

}
