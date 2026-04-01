package aprove.verification.dpframework.Utility.NonLoop.structures.proofed.creation;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
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

public class PatternCreationI extends ProofedRule {

    /**
     * Substitution delta used for creation
     */
    private final TRSSubstitution delta;

    /**
     * Substitution theta used for creation
     */
    private final TRSSubstitution theta;

    /**
     * Substitution sigma used for creation
     */
    private final TRSSubstitution sigma;

    /**
     * Parent used for creation
     */
    private final ProofedRule parent;

    private PatternCreationI(final PatternTerm lhs, final PatternTerm rhs, final ProofedRule parentArg,
            final TRSSubstitution deltaArg, final TRSSubstitution thetaArg, final TRSSubstitution sigmaArg) {
        super(lhs, rhs, parentArg.getR(), parentArg.getP(), parentArg.hasPStep());
        this.parent = parentArg;
        this.delta = deltaArg;
        this.theta = thetaArg;
        this.sigma = sigmaArg;
        this.setShowRule();
    }

    public static ProofedRule create(final ProofedRule lr,
        final TRSSubstitution delta,
        final TRSSubstitution theta,
        final TRSSubstitution sigma) {

        if (!Utils.commutative(sigma, theta)) {
            if (Globals.DEBUG_NEX) {
                System.err.println("PatternCreationI: not commutative");
            }
            return null;
        }

        final PatternRule pRule = lr.getPatternRule();
        final PatternTerm lhs = pRule.getLhs();
        final PatternTerm rhs = pRule.getRhs();

        if (!(lhs.isSigmaAndMuEmpty() && rhs.isSigmaAndMuEmpty())) {
            return null;
        }
        final TRSTerm l = lhs.getT();
        final TRSTerm r = rhs.getT();

        if (!l.applySubstitution(delta).applySubstitution(theta).equals(
            r.applySubstitution(delta).applySubstitution(sigma))) {
            if (Globals.DEBUG_NEX) {
                System.err.println("PatternCreationI: not equal");
            }
            return null;
        }

        final PatternTerm lhsN = new PatternTerm(l.applySubstitution(delta), sigma);
        final PatternTerm rhsN = new PatternTerm(r.applySubstitution(delta), theta);

        return new PatternCreationI(lhsN, rhsN, lr, delta, theta, sigma);
    }
    
    @Override
    public int getProofStepCount() {
        return 1 + this.parent.getProofStepCount();
    }
    

    @Override
    public ImmutableList<Pair<Position, Rule>> reconstructSequence() {
        
        ArrayList<Pair<Position, Rule>> res = new ArrayList<Pair<Position, Rule>>();
        ImmutableList<Pair<Position, Rule>> rewSequence = parent.reconstructSequence();
        
        for(Pair<Position, Rule> step : rewSequence) {
            res.add(new Pair<>(step.x, step.y));
        }
                
        return ImmutableCreator.create(res);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String exportProof(final Export_Util eu) {
        return "PatternCreation I with delta: " + this.delta.export(eu) + ", theta: " + this.theta.export(eu)
            + ", sigma: " + this.sigma.export(eu);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String exportProofShort(final Export_Util eu) {
        return "PatternCreation I";
    }

    /**
     * @return The {@link TRSSubstitution delta} used for creation.
     */
    public TRSSubstitution getDelta() {
        return this.delta;
    }

    /**
     * @return The {@link TRSSubstitution theta} used for creation.
     */
    public TRSSubstitution getTheta() {
        return this.theta;
    }

    /**
     * @return The {@link TRSSubstitution sigma} used for creation.
     */
    public TRSSubstitution getSigma() {
        return this.sigma;
    }

    /**
     * @return The {@link ProofedRule parent} used for creation.
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
        final Element initialPumping = XMLTag.INITIAL_PUMPING.createElement(doc);
        initialPumping.appendChild(this.getPatternRule().toDOM(doc, xmlMetaData));
        initialPumping.appendChild(this.parent.toDOM(doc, xmlMetaData));
        initialPumping.appendChild(this.sigma.toDOM(doc, xmlMetaData));
        initialPumping.appendChild(this.theta.toDOM(doc, xmlMetaData));
        final Element proofedRule = XMLTag.PROOFED_RULE.createElement(doc);
        proofedRule.appendChild(initialPumping);
        return proofedRule;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element initialPumping = CPFTag.INITIAL_PUMPING.createElement(doc);
        initialPumping.appendChild(this.parent.toCPF(doc, xmlMetaData));
        initialPumping.appendChild(this.sigma.toCPF(doc, xmlMetaData));
        initialPumping.appendChild(this.theta.toCPF(doc, xmlMetaData));
        final Element proofedRule = CPFTag.PATTERN_RULE.createElement(doc);
        proofedRule.appendChild(this.getPatternRule().getLhs().toCPF(doc, xmlMetaData));
        proofedRule.appendChild(this.getPatternRule().getRhs().toCPF(doc, xmlMetaData));
        proofedRule.appendChild(initialPumping);
        return proofedRule;
    }

}
