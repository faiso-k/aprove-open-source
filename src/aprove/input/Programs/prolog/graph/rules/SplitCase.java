package aprove.input.Programs.prolog.graph.rules;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.verification.oldframework.Utility.Graph.*;

/**
 * SplitCase.<br><br>
 *
 * Created: May 16, 2007<br>
 * Last modified: May 16, 2007
 *
 * @author cryingshadow
 * @version $Id$
 */
public class SplitCase implements PrettyStringable {

    /**
     * The new knowledge.
     */
    private final KnowledgeBase knowledgeBase;

    /**
     * The replacements.
     */
    private final PrologSubstitution replacements;

    /**
     * Standard constructor.
     * @param base The new knowledge.
     * @param replace The replacements.
     */
    public SplitCase(final KnowledgeBase base, final PrologSubstitution replace) {
        this.knowledgeBase = base;
        this.replacements = replace;
    }

    /**
     * @return The replacements.
     */
    public PrologSubstitution getReplacements() {
        return this.replacements;
    }

    /**
     * @return True if there is neither new knowledge nor replacements.
     */
    public boolean isEmpty() {
        return this.knowledgeBase.isEmpty() && this.replacements.isEmpty();
    }

    /* (non-Javadoc)
     * @see aprove.verification.oldframework.Utility.Graph.PrettyStringable#prettyToString()
     */
    @Override
    public String prettyToString() {
        return (this.knowledgeBase.isEmpty() ? (this.replacements.isEmpty() ? "" : "replacements:"
            + this.replacements.prettyToString()) : "new knowledge:"
            + "\\n"
            + this.knowledgeBase.prettyToString()
            + (this.replacements.isEmpty() ? "" : "\\nreplacements:" + this.replacements.prettyToString()));
    }

    /* (non-Javadoc)
     * @see java.lang.Object#toString()
     */
    @Override
    public String toString() {
        return (this.knowledgeBase.isEmpty() ? (this.replacements.isEmpty() ? "" : "replacements:"
            + this.replacements.toString()) : "new knowledge:"
            + "\n"
            + this.knowledgeBase.toString()
            + (this.replacements.isEmpty() ? "" : "\nreplacements:" + this.replacements.toString()));
    }

}
