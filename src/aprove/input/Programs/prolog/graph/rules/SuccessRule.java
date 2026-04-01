package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;

/**
 * SuccessStep.<br><br>
 *
 * Created: Sep 3, 2008<br>
 * Last modified: Sep 3, 2008
 *
 * @author cryingshadow
 * @version $Id$
 */
public class SuccessRule extends AbstractInferenceRule {

    @Override
    public String prettyToString() {
        return "SUCCESS";
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.SUCCESS;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        return "    node[auto]\n      {\\textsc{Suc}}\n";
    }

    @Override
    public String toString() {
        return "SUCCESS";
    }

}
