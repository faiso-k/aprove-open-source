package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;

/**
 * A CaseStep contains the information gained by performing a CASE
 * step in the PartEvalTree evaluation for use in fixpoint
 * algorithms.<br><br>
 *
 * Created: Dec 1, 2006<br>
 * Last modified: Dec 1, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
public class CaseRule extends AbstractInferenceRule {

    @Override
    public String prettyToString() {
        return "CASE";
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.CASE;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        return "    node[auto]\n      {\\textsc{Case}}\n";
    }

    @Override
    public String toString() {
        return "CASE";
    }

}
