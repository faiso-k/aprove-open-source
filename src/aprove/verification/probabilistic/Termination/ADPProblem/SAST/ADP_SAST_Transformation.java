package aprove.verification.probabilistic.Termination.ADPProblem.SAST;

import aprove.prooftree.Export.Utility.*;

/**
 * @author J-C Kassing & Leon Spitzer
 * @version $Id$
 */
public enum ADP_SAST_Transformation {

        Instantiation("instantiating", Citation.FLOPS24),
        ForwardInstantiation("forward instantiating", Citation.FLOPS24),
        RuleOverlapInstantiation("rule overlap instantiation", Citation.FLOPS24),
        Rewriting("rewriting", Citation.FLOPS24),
        Narrowing("narrowing", Citation.FLOPS24);

    private final String predicate;
    private final Citation citation;

    private ADP_SAST_Transformation(final String predicate, final Citation citation) {
        this.predicate = predicate;
        this.citation = citation;
    }

    public String getPredicate() {
        return this.predicate;
    }

    public Citation getCitation() {
        return this.citation;
    }

}
