package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;

/**
 * CutStep.<br><br>
 *
 * Created: Sep 3, 2008<br>
 * Last modified: Sep 3, 2008
 *
 * @author cryingshadow
 * @version $Id$
 */
public class CutRule extends AbstractInferenceRule {

    @Override
    public String prettyToString() {
        return "CUT";
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.CUT;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        return "    node[auto]\n      {\\textsc{Cut}}\n";
    }

    @Override
    public String toString() {
        return "CUT";
    }

}
