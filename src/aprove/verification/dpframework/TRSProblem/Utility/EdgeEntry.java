package aprove.verification.dpframework.TRSProblem.Utility;

import aprove.verification.dpframework.BasicStructures.*;

/**
 * this class represents the information labelled to an Edge of the "OutermostTerminationGraph"
 *
 * @author Sebastian Weise
 */

public class EdgeEntry {

    private final TRSSubstitution subst;

    // additional information dependent on the Type of the Start-Node
    // Narrow-/ParSplit-Node
    private Position position;
    // Narrow-Node
    private Rule rule;
    // Ins-Node
    private boolean isInsEdge;
    // Linearize-Node
    private boolean isLinearizeEdge;

    public EdgeEntry() {
        this.subst = TRSSubstitution.create();
    }

    public EdgeEntry(final TRSSubstitution subst) {
        this.subst = subst;
    }

    public TRSSubstitution getSubstitution() {
        return this.subst;
    }

    /**************************************************************************/

    public void setPosition(final Position position) {
        this.position = position;
    }

    public void setRule(final Rule rule) {
        this.rule = rule;
    }

    public boolean getIsInsEdge() {
        return this.isInsEdge;
    }

    public void setIsInsEdge(final boolean isInsEdge) {
        this.isInsEdge = isInsEdge;
    }

    public boolean getIsLinearizeEdge() {
        return this.isLinearizeEdge;
    }

    public void setIsLinearizeEdge(final boolean isLinearizeEdge) {
        this.isLinearizeEdge = isLinearizeEdge;
    }

    /**************************************************************************/

    @Override
    public String toString() {
        final StringBuilder result =
            new StringBuilder("subst: " + this.subst.toString());
        if (this.position != null) {
            result.append("\\npos: " + this.position);
        }
        if (this.rule != null) {
            result.append("\\nrule: " + this.rule.getLeft() + " -&gt; "
                + this.rule.getRight());
        }
        return result.toString();
    }
}