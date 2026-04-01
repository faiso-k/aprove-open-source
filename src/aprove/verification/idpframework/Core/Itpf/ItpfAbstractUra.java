package aprove.verification.idpframework.Core.Itpf;

import aprove.verification.idpframework.Algorithms.UsableRules.*;
import aprove.verification.idpframework.Polynomials.*;

public abstract class ItpfAbstractUra extends ItpfAtom.ItpfAtomSkeleton {

    protected final IUsableRulesEstimation usableRulesEstimation;
    protected final RelDependency relDependency;
    protected final ItpRelation relation;
    protected final ItpfFactory factory;

    public ItpfAbstractUra(final IUsableRulesEstimation eu, final RelDependency k,
        final ItpRelation rel, final ItpfFactory factory) {
        this.usableRulesEstimation = eu;
        this.relDependency = k;
        this.relation = rel;
        this.factory = factory;
    }

    public RelDependency getRelationalDependency() {
        return this.relDependency;
    }

    public ItpRelation getRelation() {
        return this.relation;
    }

    public IUsableRulesEstimation getUsableRulesEstimation() {
        return this.usableRulesEstimation;
    }

}