package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;

/**
 * FailureStep.<br><br>
 *
 * Created: Sep 3, 2008<br>
 * Last modified: May 4, 2010
 *
 * @author cryingshadow
 * @version $Id$
 */
public class FailureRule extends AbstractInferenceRule {

    @Override
    public String prettyToString() {
        return "FAILURE";
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.FAILURE;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        return "    node[auto]\n      {\\textsc{Fail}}\n";
    }

    @Override
    public String toString() {
        return "FAILURE";
    }

}
