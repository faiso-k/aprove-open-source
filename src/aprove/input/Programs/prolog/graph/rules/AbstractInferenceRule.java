package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * Step.<br><br>
 *
 * Created: Dec 1, 2006<br>
 * Last modified: Dec 1, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
public abstract class AbstractInferenceRule implements PrettyStringable {

    /**
     * @return The rule type.
     */
    public abstract AbstractInferenceRules rule();

    /**
     * @param vars The variables to which substitutions should be restricted.
     * @param kb The knowledge base indicating which variables are ground (and, thus, overlined in the output).
     * @return A representation suitable for LaTeX documents.
     */
    public abstract String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb);

}
