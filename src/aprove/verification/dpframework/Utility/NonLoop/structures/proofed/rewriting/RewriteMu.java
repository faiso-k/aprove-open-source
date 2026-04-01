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
 * @author Tim Enger
 */

public class RewriteMu extends ProofedRule {

    /**
     * The variable whose substitution should be rewrited.
     */
    private final TRSVariable x;

    /**
     * The rewrite sequence to be applied.
     */
    private final ImmutableList<Pair<Position, Rule>> rewriteSeq;

    /**
     * Parent used for rewriting.
     */
    private final ProofedRule parent;

    /**
     * the intermediate steps to be given for the xml export
     */
    private final List<TRSTerm> intermediateSteps;

    private RewriteMu(final PatternTerm lhs, final PatternTerm rhs, final TRSVariable xArg,
            final ImmutableList<Pair<Position, Rule>> rewriteSeqArg, final ProofedRule parentArg,
            final List<TRSTerm> intemediateStepsArg) {
        super(lhs, rhs, parentArg.getR(), parentArg.getP(), parentArg.hasPStep());
        this.parent = parentArg;
        this.rewriteSeq = rewriteSeqArg;
        this.x = xArg;
        this.intermediateSteps = intemediateStepsArg;
        this.setShowRule();
    }

    public static ProofedRule create(final ProofedRule lr,
        final TRSVariable x,
        final ImmutableList<Pair<Position, Rule>> rewriteSeq) {

        final PatternRule pRule = lr.getPatternRule();
        final PatternTerm rhs = pRule.getRhs();
        final TRSSubstitution muR = rhs.getMu();

        final ImmutableSet<Rule> r = lr.getR();

        // get Term to rewrite
        TRSTerm toRewrite = muR.substitute(x);

        // unfortunately we need the list of intermediate steps for the xml
        // export
        final Pair<TRSTerm, List<TRSTerm>> rewrittenPair = Utils.rewriteSequence(toRewrite, rewriteSeq, r);

        toRewrite = rewrittenPair.x;

        if (toRewrite == null) {
            return null;
        }

        // build new sigma
        final Map<TRSVariable, TRSTerm> newMuRMap = new LinkedHashMap<>(muR.toMap());
        newMuRMap.put(x, toRewrite);

        // build new rhs
        final PatternTerm rhsN =
            new PatternTerm(rhs.getT(), rhs.getSigma(), TRSSubstitution.create(ImmutableCreator.create(newMuRMap)));

        if (rhsN.equals(rhs)) {
            // it's still the same rule, so just return it
            if (Globals.DEBUG_NEX) {
                System.err.println("RewriteMu: Same rule as before!");
            }
            return lr;
        }

        return new RewriteMu(pRule.getLhs(), rhsN, x, rewriteSeq, lr, rewrittenPair.y);
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

    @Override
    public String exportProof(final Export_Util eu) {
        return "Rewrite mu at the term of variable: " + this.x.export(eu) + " with the rewrite sequence <Pos,Rule>: "
            + this.rewriteSeq;
    }

    @Override
    public String exportProofShort(final Export_Util eu) {
        return "Rewrite mu";
    }

    /**
     * @return The {@link ProofedRule parent} used for rewriting.
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
        XMLAttribute.COLLAPSE.setAttribute(rewrite, "THE SIZE IS: " + this.rewriteSeq.size());
        for (final Pair<Position, Rule> pair : this.rewriteSeq) {
            final Element step = XMLTag.STEP.createElement(doc);
            step.appendChild(pair.x.toDOM(doc, xmlMetaData));
            step.appendChild(pair.y.toDOM(doc, xmlMetaData));
            final TRSTerm term = stepIterator.next();
            step.appendChild(term.toDOM(doc, xmlMetaData));
            rewrite.appendChild(step);
        }
        final Element closing = XMLTag.CLOSING.createElement(doc);
        closing.appendChild(this.x.toDOM2(doc, xmlMetaData));
        rewrite.appendChild(closing);
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
        final Element rewriteSequence = CPFTag.REWRITE_SEQUENCE.create(doc,startTermTag);
        for (final Pair<Position, Rule> pair : this.rewriteSeq) {
            final Element step = CPFTag.REWRITE_STEP.createElement(doc);
            step.appendChild(pair.x.toCPF(doc, xmlMetaData));
            step.appendChild(pair.y.toCPF(doc, xmlMetaData));
            final TRSTerm term = stepIterator.next();
            step.appendChild(term.toCPF(doc, xmlMetaData));
            rewriteSequence.appendChild(step);
        }
        rewrite.appendChild(rewriteSequence);
        final Element closing = CPFTag.CLOSING.createElement(doc);
        closing.appendChild(this.x.toCPF2(doc, xmlMetaData));
        rewrite.appendChild(closing);
        final Element proofedRule = CPFTag.PATTERN_RULE.createElement(doc);
        proofedRule.appendChild(this.getPatternRule().getLhs().toCPF(doc, xmlMetaData));
        proofedRule.appendChild(this.getPatternRule().getRhs().toCPF(doc, xmlMetaData));
        proofedRule.appendChild(rewrite);
        return proofedRule;
    }

}
