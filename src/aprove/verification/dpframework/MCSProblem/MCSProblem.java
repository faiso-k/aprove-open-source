package aprove.verification.dpframework.MCSProblem;

import java.util.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Encapsulates a monotonicity constraint transition system (MCS)
 * as defined in the ICLP'11 paper by Ben-Amram et al.
 *
 * @author fuhs
 */
public class MCSProblem extends DefaultBasicObligation implements
                        Exportable, HasFunctionSymbols, HasVariables {

    private final ImmutableSet<MCRule> rules;

    private MCSProblem(ImmutableSet<MCRule> rules) {
        super("MCS","Monotonicity Constraint Transition System");
        this.rules = rules;
    }

    public static MCSProblem create(ImmutableSet<MCRule> rules) {
        return new MCSProblem(rules);
    }

    public ImmutableSet<MCRule> getRules() {
        return this.rules;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Termination");
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder sb = new StringBuilder();
        sb.append(o.set(this.rules, Export_Util.RULES));
        sb.append(o.linebreak());
        return sb.toString();
    }

    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        return aprove.verification.dpframework.BasicStructures.CollectionUtils.getFunctionSymbols(this.rules);
    }

    @SuppressWarnings("unchecked")
    @Override
    public Set<TRSVariable> getVariables() {
        return (Set<TRSVariable>)aprove.verification.dpframework.BasicStructures.CollectionUtils.getVariables(this.rules);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "mcs";
    }
}
