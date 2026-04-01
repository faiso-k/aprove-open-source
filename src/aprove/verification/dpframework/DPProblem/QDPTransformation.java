package aprove.verification.dpframework.DPProblem;

import aprove.prooftree.Export.Utility.*;

public enum QDPTransformation {
    Instantiation("instantiating"),
    ForwardInstantiation("forward instantiating", Citation.JAR06),
    Rewriting("rewriting"),
    Narrowing("narrowing");

    private final String predicate;
    private final Citation citation;

    private QDPTransformation(String predicate) {
        this(predicate, Citation.LPAR04);
    }

    private QDPTransformation(String predicate, Citation citation) {
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