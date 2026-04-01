package aprove.verification.complexity.LowerBounds.BasicStructures;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.complexity.TruthValue.*;

/**
 * Just a pair of an obligation obl and a lower bound which has been proven for obl previously.
 * See {@code LowerBoundPropagationProcessor}.
 */
public class ProvenLowerBound extends DefaultBasicObligation {

    private BasicObligation obl;
    private ComplexityValue bound;

    public ProvenLowerBound(BasicObligation obl, ComplexityValue bound) {
        super("proven lower bound", "proven lower bound");
        this.obl = obl;
        this.bound = bound;
    }

    @Override
    public String getStrategyName() {
        return "propagatelowerbound";
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return obl.getProofPurposeDescriptor();
    }

    @Override
    public String export(Export_Util eu) {
        String res = "Proved the lower bound " + bound.export(eu) + " for the following obligation:" + eu.newline();
        return res + obl.export(eu);
    }

    public ComplexityValue getBound() {
        return bound;
    }

}
