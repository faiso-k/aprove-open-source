package aprove.verification.dpframework.Utility.NonLoop.structures.proofed.creation;

import java.util.*;

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

public final class RuleFromTRS extends ProofedRule {

    /**
     * Flag if the rule originally comes from R
     */
    private final boolean fromR;

    /**
     * the original rule
     */
    private final Rule origRule;

    /**
     * Constructor
     *
     * @param rule The original {@link Rule}
     * @param r The {@link ImmutableSet set} R
     * @param p The {@link ImmutableSet set} P
     * @param hasPStep Indicates whether the rule comes from R or not.
     */
    private RuleFromTRS(final Rule rule, final ImmutableSet<Rule> r, final ImmutableSet<Rule> p, final boolean hasPStep) {
        super(new PatternTerm(rule.getLeft()), new PatternTerm(rule.getRight()), r, p, hasPStep);
        this.setShowRule();
        this.origRule = rule;
        this.fromR = !hasPStep;
    }

    /**
     * Factory method
     *
     * @param rule
     *            The original {@link Rule}
     * @param r
     *            The {@link ImmutableSet set} R
     * @param p
     *            The {@link ImmutableSet set} P
     * @return The created {link ProofedRule}
     */
    public static ProofedRule create(final Rule rule, final ImmutableSet<Rule> r, final ImmutableSet<Rule> p) {
        if (r.contains(rule)) {
            return new RuleFromTRS(rule, r, p, false);
        }

        if (p.contains(rule)) {
            return new RuleFromTRS(rule, r, p, true);
        }

        assert false;
        return null;
    }
    
    @Override
    public int getProofStepCount() {
        return 1;
    }

    @Override
    public ImmutableList<Pair<Position, Rule>> reconstructSequence() {
        Pair<Position, Rule> first = new Pair<>(Position.EPSILON, origRule);
        ArrayList<Pair<Position, Rule>> res = new ArrayList<Pair<Position, Rule>>();
        res.add(first);
        return ImmutableCreator.create(new ArrayList<Pair<Position, Rule>>(res));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String exportProof(final Export_Util eu) {
        return "Rule from TRS " + (this.fromR ? "R" : "P");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String exportProofShort(final Export_Util eu) {
        return "RuleFromTRS";
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
        return "";
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element originalRule = XMLTag.ORIGINAL_RULE.createElement(doc);
        originalRule.appendChild(this.getPatternRule().toDOM(doc, xmlMetaData));
        originalRule.appendChild(this.origRule.toDOM(doc, xmlMetaData));
        originalRule.appendChild(XMLTag.createBoolean(doc, !this.fromR));
        final Element proofedRule = XMLTag.PROOFED_RULE.createElement(doc);
        proofedRule.appendChild(originalRule);
        return proofedRule;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element originalRule = CPFTag.ORIGINAL_RULE.createElement(doc);
        originalRule.appendChild(this.origRule.toCPF(doc, xmlMetaData));
        final Element isPair = CPFTag.IS_PAIR.createElement(doc);
        isPair.appendChild(doc.createTextNode("" + !this.fromR));
        originalRule.appendChild(isPair);
        final Element proofedRule = CPFTag.PATTERN_RULE.createElement(doc);
        proofedRule.appendChild(this.getPatternRule().getLhs().toCPF(doc, xmlMetaData));
        proofedRule.appendChild(this.getPatternRule().getRhs().toCPF(doc, xmlMetaData));
        proofedRule.appendChild(originalRule);
        return proofedRule;
    }

}
