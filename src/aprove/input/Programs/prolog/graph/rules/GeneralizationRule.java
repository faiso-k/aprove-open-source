package aprove.input.Programs.prolog.graph.rules;

import java.util.*;

import aprove.input.Programs.prolog.graph.*;
import aprove.input.Programs.prolog.structure.*;

/**
 * GeneralizationStep.<br><br>
 *
 * Created: Oct 24, 2007<br>
 * Last modified: Oct 24, 2007
 *
 * @author cryingshadow
 * @version $Id$
 */
public class GeneralizationRule extends AbstractInferenceRule {

    /**
     * The performed generalizations.
     */
    private final PrologSubstitution generalizations;

    /**
     * The inferred knowledge about the replaced variables.
     */
    private final KnowledgeBase newKnowledge;

    /**
     * Standard constructor.
     * @param g The generalizations.
     * @param newKB The new knowledge.
     */
    public GeneralizationRule(final PrologSubstitution g, final KnowledgeBase newKB) {
        if (g == null) {
            throw new NullPointerException("Generalization map may not be null!");
        }
        this.generalizations = g;
        this.newKnowledge = newKB;
    }

    /**
     * @return The generalizations as new substitution.
     */
    public PrologSubstitution getGeneralizationAsSubstitution() {
        final PrologSubstitution res = new PrologSubstitution();
        for (final Map.Entry<PrologVariable, PrologTerm> entry : this.generalizations.entrySet()) {
            res.put(entry.getKey(), entry.getValue());
        }
        return res;
    }

    @Override
    public String prettyToString() {
        String res = "GENERALIZATION";
        for (final Map.Entry<PrologVariable, PrologTerm> entry : this.generalizations.entrySet()) {
            res += "\\n" + entry.getKey().prettyToString() + " <-- " + entry.getValue().prettyToString();
        }
        if (this.newKnowledge != null && !this.newKnowledge.isEmpty()) {
            res += "\\n\\n" + "New Knowledge:" + "\\n" + this.newKnowledge.prettyToString();
        }
        return res;
    }

    @Override
    public AbstractInferenceRules rule() {
        return AbstractInferenceRules.GENERALIZATION;
    }

    @Override
    public String toLaTeX(final Set<PrologVariable> vars, final KnowledgeBase kb) {
        final StringBuilder res = new StringBuilder();
        res.append("    node[auto]\n");
        res.append("      {\\textsc{Inst}}\n");
        res.append("    node[auto,swap]\n");
        res.append("      {$");
        res.append(this.getGeneralizationAsSubstitution().restrict(vars).toLaTeX(kb));
        res.append("$}\n");
        return res.toString();
    }

    @Override
    public String toString() {
        String res = "GENERALIZATION";
        for (final Map.Entry<PrologVariable, PrologTerm> entry : this.generalizations.entrySet()) {
            res += "\n" + entry.getKey().toString() + " <-- " + entry.getValue().toString();
        }
        if (this.newKnowledge != null && !this.newKnowledge.isEmpty()) {
            res += "\n\n" + "New Knowledge:" + "\n" + this.newKnowledge.toString();
        }
        return res;
    }

}
