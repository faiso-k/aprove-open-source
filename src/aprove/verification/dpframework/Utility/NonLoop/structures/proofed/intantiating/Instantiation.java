package aprove.verification.dpframework.Utility.NonLoop.structures.proofed.intantiating;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.NonLoop.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * @author Tim Enger
 */

public class Instantiation extends ProofedRule {

    /**
     * The substitution rho used for instantiation
     */
    private final TRSSubstitution rho;

    /**
     * Parent used for instantiation.
     */
    private final ProofedRule parent;

    private Instantiation(final PatternTerm lhs, final PatternTerm rhs, final ProofedRule parentArg,
            final TRSSubstitution rho) {
        super(lhs, rhs, parentArg.getR(), parentArg.getP(), parentArg.hasPStep());
        this.parent = parentArg;
        this.rho = rho;
    }

    public static ProofedRule create(final ProofedRule lr, final TRSSubstitution rho) {

        final PatternRule pRule = lr.getPatternRule();
        final PatternTerm lhs = pRule.getLhs();
        final PatternTerm rhs = pRule.getRhs();

        final TRSTerm l = lhs.getT();
        final TRSSubstitution sigmaL = lhs.getSigma();
        final TRSSubstitution muL = lhs.getMu();

        final TRSTerm r = rhs.getT();
        final TRSSubstitution sigmaR = rhs.getSigma();
        final TRSSubstitution muR = rhs.getMu();

        final Set<TRSVariable> vars = new LinkedHashSet<>(sigmaL.getDomain());
        vars.addAll(muL.getDomain());
        vars.addAll(sigmaR.getDomain());
        vars.addAll(muR.getDomain());
        vars.retainAll(rho.getVariables());

        if (!vars.isEmpty()) {
            return null;
        }

        final PatternTerm lhsN =
            new PatternTerm(l.applySubstitution(rho), Utils.applyInRange(sigmaL, rho), Utils.applyInRange(muL, rho));

        final PatternTerm rhsN =
            new PatternTerm(r.applySubstitution(rho), Utils.applyInRange(sigmaR, rho), Utils.applyInRange(muR, rho));

        if (lhsN.equals(lhs) && rhsN.equals(rhs)) {
            // it's still the same rule, so just return it
            return lr;
        }

        return new Instantiation(lhsN, rhsN, lr, rho);
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
        return "Instantiation with rho: " + this.rho.export(eu);
    }

    @Override
    public String exportProofShort(final Export_Util eu) {
        return "Instantiation";
    }

    /**
     * @return The {@link ProofedRule parent} used for instantiation..
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
        instantiation.appendChild(this.rho.toDOM(doc, xmlMetaData));
        instantiation.appendChild(XMLTag.BASE.createElement(doc));
        final Element proofedRule = XMLTag.PROOFED_RULE.createElement(doc);
        proofedRule.appendChild(instantiation);
        return proofedRule;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element instantiation = CPFTag.INSTANTIATION.create(doc,
                this.parent.toCPF(doc, xmlMetaData),
                this.rho.toCPF(doc, xmlMetaData),
                CPFTag.BASE.create(doc));
        return CPFTag.PATTERN_RULE.create(doc,
                this.getPatternRule().getLhs().toCPF(doc, xmlMetaData),
                this.getPatternRule().getRhs().toCPF(doc, xmlMetaData),
                instantiation);
    }

}
