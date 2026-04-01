package aprove.verification.dpframework.Utility.NonLoop.structures.proofed.rewriting;

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
 * Rewrite the {@link TRSTerm} t.
 *
 * @author Tim Enger
 */

public final class RewriteT extends ProofedRule {

    /**
     * Parent the sequence is applied to
     */
    private final ProofedRule parent;

    /**
     * /** The rewrite sequence applied
     */
    private final ImmutableList<Pair<Position, Rule>> rewriteSeq;

    /**
     * the intermediate steps to be given for the xml export
     */
    private final List<TRSTerm> intermediateSteps;

    /**
     * Constructor
     *
     * @param lhs {@link PatternTerm Left-hand side}
     * @param rhs {@link PatternTerm Right-hand side}
     * @param rewriteSeqArg The rewrite sequence applied
     * @param parentArg The parent rule
     * @param intermediateStepsArg for having the steps in xml export
     */
    private RewriteT(final PatternTerm lhs, final PatternTerm rhs,
            final ImmutableList<Pair<Position, Rule>> rewriteSeqArg, final ProofedRule parentArg,
            final List<TRSTerm> intermediateStepsArg) {
        super(lhs, rhs, parentArg.getR(), parentArg.getP(), parentArg.hasPStep());
        this.rewriteSeq = rewriteSeqArg;
        this.parent = parentArg;
        this.intermediateSteps = intermediateStepsArg;
        this.setShowRule();
    }

    /**
     * Factory method
     *
     * @param lr
     *            {@link ProofedRule} to work with
     * @param rewriteSeq
     *            The rewrite sequence to be applied
     * @return The created {@link ProofedRule}
     */
    public static ProofedRule create(final ProofedRule lr, final ImmutableList<Pair<Position, Rule>> rewriteSeq) {
        final PatternRule pRule = lr.getPatternRule();
        final PatternTerm rhs = pRule.getRhs();

        final ImmutableSet<Rule> r = lr.getR();

        // get Term to rewrite
        TRSTerm toRewrite = rhs.getT();

        // unfortunately we need the list of intermediate steps for the xml
        // export
        final Pair<TRSTerm, List<TRSTerm>> rewrittenPair = Utils.rewriteSequence(toRewrite, rewriteSeq, r);

        toRewrite = rewrittenPair.x;

        if (toRewrite == null) {
            return null;
        }

        // build new rhs
        final PatternTerm rhsN = new PatternTerm(toRewrite, rhs.getSigma(), rhs.getMu());

        if (rhsN.equals(rhs)) {
            // it's still the same rule, so just return it
            if (Globals.DEBUG_NEX) {
                System.err.println("RewriteT: Same rule as before!");
            }
            return lr;
        }

        return new RewriteT(pRule.getLhs(), rhsN, rewriteSeq, lr, rewrittenPair.y);
    }
    
    @Override
    public int getProofStepCount() {
        return 1 + this.parent.getProofStepCount();
    }
    
    @Override
    public ImmutableList<Pair<Position, Rule>> reconstructSequence() {
        ArrayList<Pair<Position, Rule>> res = new ArrayList<Pair<Position, Rule>>();
        ImmutableList<Pair<Position, Rule>> oldRewriteSeq = parent.reconstructSequence();
        
        res.addAll(oldRewriteSeq);
        res.addAll(rewriteSeq);
                
        return ImmutableCreator.create(res);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String exportProof(final Export_Util eu) {
        return "Rewrite t with the rewrite sequence <Pos,Rule>: " + this.rewriteSeq;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String exportProofShort(final Export_Util eu) {
        return "Rewrite t";
    }

    /**
     * @return The {@link ProofedRule parent} the rewrite sequence was applied
     *         to.
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
        final Element rewrite = XMLTag.REWRITING.createElement(doc);
        rewrite.appendChild(this.getPatternRule().toDOM(doc, xmlMetaData));
        final Iterator<TRSTerm> stepIterator = this.intermediateSteps.iterator();
        final TRSTerm startTerm = stepIterator.next();
        rewrite.appendChild(startTerm.toDOM(doc, xmlMetaData));
        rewrite.appendChild(this.parent.toDOM(doc, xmlMetaData));
        for (final Pair<Position, Rule> pair : this.rewriteSeq) {
            final Element step = XMLTag.STEP.createElement(doc);
            step.appendChild(pair.x.toDOM(doc, xmlMetaData));
            step.appendChild(pair.y.toDOM(doc, xmlMetaData));
            final TRSTerm term = stepIterator.next();
            step.appendChild(term.toDOM(doc, xmlMetaData));
            rewrite.appendChild(step);
        }
        rewrite.appendChild(XMLTag.BASE.createElement(doc));
        final Element proofedRule = XMLTag.PROOFED_RULE.createElement(doc);
        proofedRule.appendChild(rewrite);
        return proofedRule;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element rewrite = CPFTag.REWRITING.createElement(doc);
        final Iterator<TRSTerm> stepIterator = this.intermediateSteps.iterator();
        final TRSTerm startTerm = stepIterator.next();
        final Element startTermTag = CPFTag.START_TERM.createElement(doc);
        startTermTag.appendChild(startTerm.toCPF(doc, xmlMetaData));
        rewrite.appendChild(this.parent.toCPF(doc, xmlMetaData));
        final Element rewriteSequence = CPFTag.REWRITE_SEQUENCE.create(doc, startTermTag);
        for (final Pair<Position, Rule> pair : this.rewriteSeq) {
            final Element step = CPFTag.REWRITE_STEP.createElement(doc);
            step.appendChild(pair.x.toCPF(doc, xmlMetaData));
            step.appendChild(pair.y.toCPF(doc, xmlMetaData));
            final TRSTerm term = stepIterator.next();
            step.appendChild(term.toCPF(doc, xmlMetaData));
            rewriteSequence.appendChild(step);
        }
        rewrite.appendChild(rewriteSequence);
        final Element base = CPFTag.BASE.createElement(doc);
        rewrite.appendChild(base);
        final Element proofedRule = CPFTag.PATTERN_RULE.createElement(doc);
        proofedRule.appendChild(this.getPatternRule().getLhs().toCPF(doc, xmlMetaData));
        proofedRule.appendChild(this.getPatternRule().getRhs().toCPF(doc, xmlMetaData));
        proofedRule.appendChild(rewrite);
        return proofedRule;
    }

}
