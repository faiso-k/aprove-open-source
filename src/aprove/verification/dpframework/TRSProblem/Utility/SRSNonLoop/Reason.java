package aprove.verification.dpframework.TRSProblem.Utility.SRSNonLoop;

import java.util.*;

/**
 * this class provides the possibility to store why a
 * {@link DerivationStructure} is generated and on which
 * {@link DerivationStructure} it's based
 * @author Tim Enger
 */
public class Reason {

    private final String reason;
    private final List<DerivationStructure> parents;
    public final Object additionalInfo;
    public final ReasonType type;

    public Reason(final String reason, final ReasonType type, final DerivationStructure... parents) {
        this(reason, null, type, parents);
    }

    public Reason(final String reason, final Object info, final ReasonType type, final DerivationStructure... parents) {
        final ArrayList<DerivationStructure> temp =
            new ArrayList<DerivationStructure>();
        for (final DerivationStructure ds : parents) {
            temp.add(ds);
        }
        this.parents = temp;
        this.reason = reason;
        this.type = type;
        this.additionalInfo = info;
    }

    @Override
    public String toString() {
        return this.reason;
    }

    public String smallString() {
        return this.reason;
    }

    public List<DerivationStructure> getParents() {
        return this.parents;
    }
}
