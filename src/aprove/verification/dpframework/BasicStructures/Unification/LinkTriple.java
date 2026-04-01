package aprove.verification.dpframework.BasicStructures.Unification;

import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Class which represents a link in the dag. It's a triple with the following items:
 * x: weight on this side of the link (own weight)
 * y: weight on the other side of the link (target weight)
 * z: representative of the whole equivalence class (representative)
 *
 * @author Matthias Sondermann
 */
public class LinkTriple extends Triple<Integer, Integer, SemiUnificationNode> {

    /**
     * The caller has to ensure that the three arguments are not null!
     * @param x own weight
     * @param y target weight
     * @param z target
     */
    public LinkTriple(final int x, final int y, final SemiUnificationNode z) {
        super(x, y, z);
    }

    public void setOwnWeight(final int weight) {
        this.x = weight;
    }

    public void setTargetWeight(final int weight) {
        this.y = weight;
    }

    public void setTarget(final SemiUnificationNode node) {
        this.z = node;
    }

    public int getOwnWeight() {
        return this.x;
    }

    public int getTargetWeight() {
        return this.y;
    }

    public SemiUnificationNode getTarget() {
        return this.z;
    }

    @Override
    public boolean equals(final Object other) {
        if (this == other) {
            return true;
        }
        if (other == null) {
            return false;
        }
        if (other instanceof LinkTriple) {
            final LinkTriple that = (LinkTriple) other;
            if (this.x.equals(that.x) && this.y.equals(that.y) && this.z.equals(that.z)) {
                return true;
            }
        }
        return false;
    }
}
