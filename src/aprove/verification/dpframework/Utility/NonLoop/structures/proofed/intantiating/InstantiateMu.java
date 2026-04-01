package aprove.verification.dpframework.Utility.NonLoop.structures.proofed.intantiating;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * @author Tim Enger
 */

public class InstantiateMu extends ProofedRule {

    /**
     * The substitution theta used for instantiating mu
     */
    private final TRSSubstitution theta;

    /**
     * Parent used for instantiation.
     */
    private final ProofedRule parent;

    private InstantiateMu(final PatternTerm lhs, final PatternTerm rhs, final ProofedRule parentArg,
            final TRSSubstitution thetaArg) {
        super(lhs, rhs, parentArg.getR(), parentArg.getP(), parentArg.hasPStep());
        this.theta = thetaArg;
        this.parent = parentArg;
    }

    public static ProofedRule create(final ProofedRule lr, final TRSSubstitution theta) {
        final PatternRule pRule = lr.getPatternRule();
        final PatternTerm l = pRule.getLhs();
        final PatternTerm r = pRule.getRhs();

        final PatternTerm lhs = new PatternTerm(l.getT(), l.getSigma(), l.getMu().compose(theta));
        final PatternTerm rhs = new PatternTerm(r.getT(), r.getSigma(), r.getMu().compose(theta));

        if (l.equals(lhs) && r.equals(rhs)) {
            // it's still the same rule, so just return it
            return lr;
        }

        return new InstantiateMu(lhs, rhs, lr, theta);
    }
    
    @Override
    public int getProofStepCount() {
        return 1 + this.parent.getProofStepCount();
    }

    @Override
    public ImmutableList<Pair<Position, Rule>> reconstructSequence() {
        return parent.reconstructSequence();
    }

    @Override
    public String exportProof(final Export_Util eu) {
        return "Instantiate mu with theta: " + this.theta.export(eu);
    }

    @Override
    public String exportProofShort(final Export_Util eu) {
        return "Instantiate mu";
    }

    /**
     * @return The {@link ProofedRule parent} used for instantiation of mu.
     */
    public ProofedRule getParent() {
        return this.parent;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String exportParents(final Export_Util eu,
        final String indent,
        final String addIndent,
        final boolean firstIntermediate,
        final boolean fullProof) {
        return this.parent.export(eu, indent, addIndent, firstIntermediate, fullProof);
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element instantiation = XMLTag.INSTANTIATION.createElement(doc);
        instantiation.appendChild(this.getPatternRule().toDOM(doc, xmlMetaData));
        instantiation.appendChild(this.parent.toDOM(doc, xmlMetaData));
        instantiation.appendChild(this.theta.toDOM(doc, xmlMetaData));
        instantiation.appendChild(XMLTag.CLOSING.createElement(doc));
        final Element proofedRule = XMLTag.PROOFED_RULE.createElement(doc);
        proofedRule.appendChild(instantiation);
        return proofedRule;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element instantiation = CPFTag.INSTANTIATION.create(doc,
                this.parent.toCPF(doc, xmlMetaData),
                this.theta.toCPF(doc, xmlMetaData),
                CPFTag.CLOSING.create(doc));
        return CPFTag.PATTERN_RULE.create(doc,
                this.getPatternRule().getLhs().toCPF(doc, xmlMetaData),
                this.getPatternRule().getRhs().toCPF(doc, xmlMetaData),
                instantiation);
    }

}
