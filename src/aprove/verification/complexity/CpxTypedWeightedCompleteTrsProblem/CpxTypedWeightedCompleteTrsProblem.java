package aprove.verification.complexity.CpxTypedWeightedCompleteTrsProblem;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.complexity.CpxTypedWeightedTrsProblem.*;

/**
 * A wrapper around a CpxTypedWeightedTrsProblem to indicate that the TRS
 * is (partially) completely defined. This is useful to write proper
 * `isApplicable` methods or strategies.
 *
 *  * If `allowPartialDerivations` is false, then *all* functions are completely
 *    defined and it suffices to consider complete derivations for the (i)rc
 *    (i.e. derivations that end in ground normal forms).
 *
 *  * If `allowPartialDerivations` is true, then only *critical* functions are
 *    ensured to be completely defined (partial derivations are still important).
 *    A function is critical iff it can occur inside another function
 *    (in a derivation starting from a basic term).
 *
 * @author mnaaf
 *
 */
public class CpxTypedWeightedCompleteTrsProblem extends DefaultBasicObligation
{
    private final boolean allowPartialDerivations;
    private final CpxTypedWeightedTrsProblem trs;

    public CpxTypedWeightedCompleteTrsProblem(
            CpxTypedWeightedTrsProblem trs,
            boolean partialDerivations) {
        super("CpxTypedWeightedCompleteTrs","CpxTypedWeightedCompleteTrs");
        this.trs = trs;
        this.allowPartialDerivations = partialDerivations;
    }

    public CpxTypedWeightedTrsProblem getTypedWeightedTrs() {
        return this.trs;
    }

    @Override
    public String getStrategyName() {
        return "cpxtypedweightedcompletetrs";
    }

    //returns true iff partial derivations have to be considered for the (i)rc.
    //if false is returned, complete derivations (ending in ground normal forms)
    //are sufficient for (innermost) complexity analysis.
    public boolean allowsPartialDerivations() {
        return this.allowPartialDerivations;
    }

    @Override
    public String export(Export_Util eu) {
        StringBuilder s = new StringBuilder();
        s.append(eu.escape("Runtime Complexity Weighted TRS where "));
        if (this.allowPartialDerivations) {
            s.append(eu.escape("critical"));
        } else {
            s.append(eu.escape("all"));
        }
        s.append(eu.escape(" functions are completely defined. The underlying TRS is:"));
        s.append(eu.paragraph());
        s.append(eu.indent(this.trs.export(eu)));
        return s.toString();
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return this.trs.getProofPurposeDescriptor();
    }
}
