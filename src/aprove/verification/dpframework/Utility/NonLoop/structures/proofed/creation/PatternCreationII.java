package aprove.verification.dpframework.Utility.NonLoop.structures.proofed.creation;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * @author Tim Enger
 */

public class PatternCreationII extends ProofedRule {

    /**
     * The position used for creation.
     */
    private final Position pi;

    /**
     * The sigma used for creation
     */
    private final TRSSubstitution sigma;

    /**
     * The parent used for creation.
     */
    private final ProofedRule parent;

    /**
     * a fresh variable for the xml xport
     */
    private final TRSVariable fresh;

    private PatternCreationII(final PatternTerm lhs, final PatternTerm rhs, final ProofedRule parentArg,
            final Position piArg, final TRSSubstitution sigmaArg, final TRSVariable freshArg) {
        super(lhs, rhs, parentArg.getR(), parentArg.getP(), parentArg.hasPStep());
        this.pi = piArg;
        this.sigma = sigmaArg;
        this.parent = parentArg;
        this.fresh = freshArg;
        this.setShowRule();
    }

    public static ProofedRule create(final ProofedRule lr, final Position pi, final TRSSubstitution sigma) {

        final PatternRule pRule = lr.getPatternRule();
        final PatternTerm lhs = pRule.getLhs();
        final PatternTerm rhs = pRule.getRhs();

        if (lr.hasPStep() && !Position.create().equals(pi)) {
            return null;
        }

        if (!(lhs.isSigmaAndMuEmpty() && rhs.isSigmaAndMuEmpty())) {
            return null;
        }
        final TRSTerm l = lhs.getT();
        final TRSTerm r = rhs.getT();

        if (!r.getPositions().contains(pi)) {
            return null;
        }
        final TRSTerm rPi = r.getSubterm(pi);

        if (!l.equals(rPi.applySubstitution(sigma))) {
            return null;
        }

        final PatternTerm lhsN = new PatternTerm(l, sigma);

        final FreshVarGenerator gen = new FreshVarGenerator(pRule.getAllVariables());

        final TRSVariable fresh = gen.getFreshVariable(TRSTerm.createVariable("z"), false);

        final TRSTerm rReplaced = r.replaceAt(pi, fresh);

        final Map<TRSVariable, TRSTerm> sigmaMap = new LinkedHashMap<>(sigma.toMap());
        sigmaMap.put(fresh, rReplaced);
        final TRSSubstitution sigmaR = TRSSubstitution.create(ImmutableCreator.create(sigmaMap));

        final TRSSubstitution muR = TRSSubstitution.create(fresh, rPi);
        final PatternTerm rhsN = new PatternTerm(rReplaced, sigmaR, muR);

        return new PatternCreationII(lhsN, rhsN, lr, pi, sigma, fresh);
    }
    
    @Override
    public int getProofStepCount() {
        return 1 + this.parent.getProofStepCount();
    }
    
    @Override
    public ImmutableList<Pair<Position, Rule>> reconstructSequence() {
        
        ArrayList<Pair<Position, Rule>> res = new ArrayList<Pair<Position, Rule>>();
        ImmutableList<Pair<Position, Rule>> rewSequence = parent.reconstructSequence();
        
        res.addAll(rewSequence);
        for(Pair<Position, Rule> step : rewSequence) {
            res.add(new Pair<>(pi.append(step.x), step.y));
        }
                
        return ImmutableCreator.create(res);
    }

    @Override
    public String exportProof(final Export_Util eu) {
        return "PatternCreation II with pi: " + this.pi.export(eu) + ", sigma: " + this.sigma.export(eu);
    }

    @Override
    public String exportProofShort(final Export_Util eu) {
        return "PatternCreation II";
    }

    /**
     * @return The {@link Position} used for creation.
     */
    public Position getPi() {
        return this.pi;
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
        final Element initialPumpingContext = XMLTag.INITIAL_PUMPING_CONTEXT.createElement(doc);
        initialPumpingContext.appendChild(this.getPatternRule().toDOM(doc, xmlMetaData));
        initialPumpingContext.appendChild(this.parent.toDOM(doc, xmlMetaData));
        initialPumpingContext.appendChild(this.sigma.toDOM(doc, xmlMetaData));
        initialPumpingContext.appendChild(this.pi.toDOM(doc, xmlMetaData));
        initialPumpingContext.appendChild(this.fresh.toDOM2(doc, xmlMetaData));
        final Element proofedRule = XMLTag.PROOFED_RULE.createElement(doc);
        proofedRule.appendChild(initialPumpingContext);
        return proofedRule;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element initialPumpingContext = CPFTag.INITIAL_PUMPING_CONTEXT.createElement(doc);
        initialPumpingContext.appendChild(this.parent.toCPF(doc, xmlMetaData));
        initialPumpingContext.appendChild(this.sigma.toCPF(doc, xmlMetaData));
        initialPumpingContext.appendChild(this.pi.toCPF(doc, xmlMetaData));
        initialPumpingContext.appendChild(this.fresh.toCPF2(doc, xmlMetaData));
        final Element proofedRule = CPFTag.PATTERN_RULE.createElement(doc);
        proofedRule.appendChild(this.getPatternRule().getLhs().toCPF(doc, xmlMetaData));
        proofedRule.appendChild(this.getPatternRule().getRhs().toCPF(doc, xmlMetaData));
        proofedRule.appendChild(initialPumpingContext);
        return proofedRule;
    }

}
