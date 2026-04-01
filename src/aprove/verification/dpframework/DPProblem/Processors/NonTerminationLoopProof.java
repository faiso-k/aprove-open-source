package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Processors.*;
import aprove.verification.dpframework.DPProblem.Processors.NonTerminationProcessor.*;
import aprove.verification.dpframework.TRSProblem.Utility.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

/**
 * Proof of the nontermination processor
 *
 * @author Matthias Sondermann
 */
public class NonTerminationLoopProof extends QDPProof {

    /**
     *
     */
    protected QDPProblem qdpProblem;
    protected NarrowPair narrowPair;
    private final TRSSubstitution semiUnifier;
    private final TRSSubstitution matcher;
    private final Direction dir;
    private final BasicObligation origObl;

    protected NonTerminationLoopProof(final QDPProblem qdpProblem, final NarrowPair narrowPair,
            final Pair<TRSSubstitution, TRSSubstitution> subst, final Direction dir, final BasicObligation origObl) {

        this.qdpProblem = qdpProblem;
        this.narrowPair = narrowPair;
        this.semiUnifier = subst.y;
        this.matcher = subst.x;
        this.dir = dir;
        this.origObl = origObl;
    }

    public static NonTerminationLoopProof create(final QDPProblem qdpProblem,
        final NarrowPair narrowPair,
        final Pair<TRSSubstitution, TRSSubstitution> subst,
        final Direction dir,
        final BasicObligation origObl) {
        return new NonTerminationLoopProof(qdpProblem, narrowPair, subst, dir, origObl);
    }

    @Override
    public String export(final Export_Util eu, final VerbosityLevel level) {

        final StringBuilder retStr = new StringBuilder();
        retStr.append("We used the non-termination processor " + eu.cite(Citation.FROCOS05)
            + " to show that the DP problem is infinite.");
        retStr.append(eu.linebreak());
        if (this.dir == Direction.LEFT) {
            retStr.append("Found a loop by narrowing to the left:");
        } else if (this.dir == Direction.RIGHT) {
            retStr.append("Found a loop by narrowing to the right:");
        } else {
            retStr.append("Found a loop by semiunifying a rule from P directly.");
        }
        retStr.append(eu.linebreak());
        retStr.append(eu.linebreak());
        //retStr.append(eu.math("The TRS P consists of the following rules:"));
        //retStr.append(eu.set(this.qdpProblem.getP(),Export_Util.RULES));
        //retStr.append(eu.linebreak());
        //retStr.append(eu.math("The TRS R consists of the following rules:"));
        //retStr.append(eu.set(this.qdpProblem.getR(),Export_Util.RULES));
        //retStr.append(eu.linebreak());
        //retStr.append(eu.linebreak());
        retStr.append(eu.math("s = " + eu.export(this.narrowPair.x)));
        retStr.append(" evaluates to ");
        retStr.append(eu.math(" t =" + eu.export(this.narrowPair.y)));
        retStr.append(eu.linebreak());
        retStr.append(eu.linebreak());
        retStr.append("Thus s starts an infinite chain as s semiunifies with t with the following substitutions:");
        retStr.append(eu.linebreak());
        final Set<Object> bothSubst = new LinkedHashSet<Object>();
        bothSubst.add(eu.wrapAsRaw(" Matcher: " + this.matcher.export(eu)));
        bothSubst.add(eu.wrapAsRaw(" Semiunifier: " + this.semiUnifier.export(eu)));
        retStr.append(eu.set(bothSubst, Export_Util.ITEMIZE));
        retStr.append(eu.linebreak());
        retStr.append(eu.linebreak());
        retStr.append(this.printRewritingSequence(eu));
        if (level == VerbosityLevel.HIGH) {
            retStr.append(this.printNarrowingSequence(eu));
        }
        retStr.append(eu.linebreak());
        retStr.append(eu.linebreak());

        return retStr.toString();
    }

    @Override
    public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
        final Element proofTag = CPFTag.LOOP.createElement(doc);

        proofTag.appendChild(this.toCPFRewritingSequence(doc, xmlMetaData));
        proofTag.appendChild(this.matcher.toCPF(doc, xmlMetaData));
        proofTag.appendChild(Context.BOX.toCPF(doc, xmlMetaData));
        return CPFTag.DP_NONTERMINATION_PROOF.create(doc, proofTag);
    }

    @Override
    public boolean isCPFCheckableProof(final CPFModus modus) {
        return !modus.isPositive();
    }


    private Element toCPFRewritingSequence(final Document doc, final XMLMetaData xmlMetaData) {
        final Element rewriteSequenceTag = CPFTag.REWRITE_SEQUENCE.createElement(doc);

        final Element startTerm = CPFTag.START_TERM.createElement(doc);

        final TRSTerm dpLhs = this.narrowPair.dp.getLeft();
        final TRSTerm dpRhs = this.narrowPair.dp.getRight();

        List<Triple<Rule, Position, Trs>> narrowList = this.narrowPair.getNarrowList();
        // if the dp directly semiunifies nothing is to check
        if (narrowList.isEmpty()) {
            startTerm.appendChild(dpLhs.applySubstitution(this.semiUnifier).toCPF(doc, xmlMetaData));
            rewriteSequenceTag.appendChild(startTerm);
            final Element step = CPFTag.REWRITE_STEP.createElement(doc);
            final Element rule =
                CPFTag.RULE.create(
                    doc,
                    CPFTag.LHS.create(doc, this.narrowPair.x.toCPF(doc, xmlMetaData)),
                    CPFTag.RHS.create(doc, this.narrowPair.y.toCPF(doc, xmlMetaData)));
            step.appendChild(Position.EPSILON.toCPF(doc, xmlMetaData));
            step.appendChild(rule);
            step.appendChild(dpRhs.applySubstitution(this.semiUnifier).toCPF(doc, xmlMetaData));
            rewriteSequenceTag.appendChild(step);
            return rewriteSequenceTag;
        }
        final Direction dir = this.narrowPair.narrowDir;
        TRSTerm actTerm = null;
        TRSTerm newTerm = null;
        // check narrowing direction to know how to narrow
        // forward narrowing: start with rhs of the initial dp and narrow up
        // to pair.y
        if (dir == Direction.RIGHT) {

            actTerm = this.narrowPair.x.applySubstitution(this.semiUnifier);
            startTerm.appendChild(actTerm.toCPF(doc, xmlMetaData));
            rewriteSequenceTag.appendChild(startTerm);
            final Element step = CPFTag.REWRITE_STEP.createElement(doc);
            step.appendChild(Position.EPSILON.toCPF(doc, xmlMetaData));
            step.appendChild(this.narrowPair.dp.toCPF(doc, xmlMetaData));

            final TRSSubstitution ma = dpLhs.getMatcher(actTerm);
            newTerm = actTerm.replaceAll(dpLhs.applySubstitution(ma), dpRhs.applySubstitution(ma));
            step.appendChild(newTerm.toCPF(doc, xmlMetaData));
            rewriteSequenceTag.appendChild(step);
            actTerm = newTerm;
        }
        // backward narrowing: start with pair.x and narrow up to the lhs of
        // the initial dp
        else {
            actTerm = this.narrowPair.x.applySubstitution(this.semiUnifier);
            startTerm.appendChild(actTerm.toCPF(doc, xmlMetaData));
            rewriteSequenceTag.appendChild(startTerm);
            // reverse the list to get the forward narrowing steps
            final List<Triple<Rule, Position, Trs>> dummyList = new ArrayList<Triple<Rule, Position, Trs>>();
            for (final Triple<Rule, Position, Trs> rTriple : narrowList) {
                dummyList.add(0, rTriple);
            }
            narrowList = dummyList;
        }
        // both cases (forward and backward narrowing) are equal now
        TRSSubstitution actMatcher;
        Position actPos;
        Rule actRule;
        TRSTerm actL;
        TRSTerm actR;
        // check the whole narrowing list
        for (final Triple<Rule, Position, Trs> actTriple : narrowList) {
            actRule = actTriple.x;
            actPos = actTriple.y;
            // get subterm where the unification succeeded and check if this
            // is an innermost step
            final TRSTerm actSubterm = actTerm.getSubterm(actPos);
            // do the narrowing
            final Set<TRSVariable> vars = actTerm.getVariables();
            actRule = actRule.renameVariables(vars);
            actL = actRule.getLeft();
            actR = actRule.getRight();
            actMatcher = actL.getMatcher(actSubterm);
            newTerm = actTerm.replaceAt(actPos, actR.applySubstitution(actMatcher));
            // now fill the string with information
            final Element step = CPFTag.REWRITE_STEP.createElement(doc);
            step.appendChild(actPos.toCPF(doc, xmlMetaData));
            step.appendChild(actRule.toCPF(doc, xmlMetaData));
            if (this.qdpProblem.getR().contains(actRule)) {
                step.appendChild(CPFTag.RELATIVE_STEP.createElement(doc));
            }
            step.appendChild(newTerm.toCPF(doc, xmlMetaData));
            rewriteSequenceTag.appendChild(step);
            actTerm = newTerm;
        }
        if (this.dir == Direction.LEFT) {
            actMatcher = dpLhs.getMatcher(actTerm);
            newTerm = dpRhs.applySubstitution(actMatcher);
            final Element step = CPFTag.REWRITE_STEP.createElement(doc);
            step.appendChild(Position.EPSILON.toCPF(doc, xmlMetaData));
            step.appendChild(this.narrowPair.dp.toCPF(doc, xmlMetaData));
            step.appendChild(newTerm.toCPF(doc, xmlMetaData));
            rewriteSequenceTag.appendChild(step);
        }

        // check if the rewrite sequence really loops
        if (Globals.useAssertions) {
            assert (newTerm.equals(this.narrowPair.x.applySubstitution(this.semiUnifier).applySubstitution(this.matcher)));
        }

        return rewriteSequenceTag;
    }

    private Element toDOMRewritingSequence(final Document doc, final XMLMetaData xmlMetaData) {

        final Element rewriteSequenceTag = XMLTag.QDP_REWRITE_SEQUENCE.createElement(doc);

        final TRSTerm dpLhs = this.narrowPair.dp.getLeft();
        final TRSTerm dpRhs = this.narrowPair.dp.getRight();

        List<Triple<Rule, Position, Trs>> narrowList = this.narrowPair.getNarrowList();
        // if the dp directly semiunifies nothing is to check
        if (narrowList.isEmpty()) {
            rewriteSequenceTag.appendChild(dpLhs.applySubstitution(this.semiUnifier).toDOM(doc, xmlMetaData));
            final Element step = XMLTag.STEP.createElement(doc);
            final Element rule = XMLTag.RULE.createElement(doc);
            step.appendChild(Position.EPSILON.toDOM(doc, xmlMetaData));
            rule.appendChild(this.narrowPair.x.toDOM(doc, xmlMetaData));
            rule.appendChild(this.narrowPair.y.toDOM(doc, xmlMetaData));
            step.appendChild(rule);
            step.appendChild(dpRhs.applySubstitution(this.semiUnifier).toDOM(doc, xmlMetaData));
            rewriteSequenceTag.appendChild(step);
            return rewriteSequenceTag;
        }
        final Direction dir = this.narrowPair.narrowDir;
        TRSTerm actTerm = null;
        TRSTerm newTerm = null;
        // check narrowing direction to know how to narrow
        // forward narrowing: start with rhs of the initial dp and narrow up
        // to pair.y
        if (dir == Direction.RIGHT) {

            actTerm = this.narrowPair.x.applySubstitution(this.semiUnifier);
            rewriteSequenceTag.appendChild(actTerm.toDOM(doc, xmlMetaData));
            final Element step = XMLTag.STEP.createElement(doc);
            step.appendChild(Position.EPSILON.toDOM(doc, xmlMetaData));
            step.appendChild(this.narrowPair.dp.toDOM(doc, xmlMetaData));

            final TRSSubstitution ma = dpLhs.getMatcher(actTerm);
            newTerm = actTerm.replaceAll(dpLhs.applySubstitution(ma), dpRhs.applySubstitution(ma));
            step.appendChild(newTerm.toDOM(doc, xmlMetaData));
            rewriteSequenceTag.appendChild(step);
            actTerm = newTerm;
        }
        // backward narrowing: start with pair.x and narrow up to the lhs of
        // the initial dp
        else {
            actTerm = this.narrowPair.x.applySubstitution(this.semiUnifier);
            rewriteSequenceTag.appendChild(actTerm.toDOM(doc, xmlMetaData));
            // reverse the list to get the forward narrowing steps
            final List<Triple<Rule, Position, Trs>> dummyList = new ArrayList<Triple<Rule, Position, Trs>>();
            for (final Triple<Rule, Position, Trs> rTriple : narrowList) {
                dummyList.add(0, rTriple);
            }
            narrowList = dummyList;
        }
        // both cases (forward and backward narrowing) are equal now
        TRSSubstitution actMatcher;
        Position actPos;
        Rule actRule;
        TRSTerm actL;
        TRSTerm actR;
        // check the whole narrowing list
        for (final Triple<Rule, Position, Trs> actTriple : narrowList) {
            actRule = actTriple.x;
            actPos = actTriple.y;
            // get subterm where the unification succeeded and check if this
            // is an innermost step
            final TRSTerm actSubterm = actTerm.getSubterm(actPos);
            // do the narrowing
            final Set<TRSVariable> vars = actTerm.getVariables();
            actRule = actRule.renameVariables(vars);
            actL = actRule.getLeft();
            actR = actRule.getRight();
            actMatcher = actL.getMatcher(actSubterm);
            newTerm = actTerm.replaceAt(actPos, actR.applySubstitution(actMatcher));
            // now fill the string with information
            final Element step = XMLTag.STEP.createElement(doc);
            step.appendChild(actPos.toDOM(doc, xmlMetaData));
            step.appendChild(actRule.toDOM(doc, xmlMetaData));
            if (this.qdpProblem.getR().contains(actRule)) {
                step.appendChild(XMLTag.RELATIVE_STEP.createElement(doc));
            }
            step.appendChild(newTerm.toDOM(doc, xmlMetaData));
            rewriteSequenceTag.appendChild(step);
            actTerm = newTerm;
        }
        if (this.dir == Direction.LEFT) {
            actMatcher = dpLhs.getMatcher(actTerm);
            newTerm = dpRhs.applySubstitution(actMatcher);
            final Element step = XMLTag.STEP.createElement(doc);
            step.appendChild(Position.EPSILON.toDOM(doc, xmlMetaData));
            step.appendChild(this.narrowPair.dp.toDOM(doc, xmlMetaData));
            step.appendChild(newTerm.toDOM(doc, xmlMetaData));
            rewriteSequenceTag.appendChild(step);
        }

        // check if the rewrite sequence really loops
        if (Globals.useAssertions) {
            assert (newTerm.equals(this.narrowPair.x.applySubstitution(this.semiUnifier).applySubstitution(this.matcher)));
        }

        return rewriteSequenceTag;
    }

    private String printRewritingSequence(final Export_Util eu) {

        final TRSTerm dpLhs = this.narrowPair.dp.getLeft();
        final TRSTerm dpRhs = this.narrowPair.dp.getRight();

        final StringBuilder retStr = new StringBuilder();
        retStr.append(eu.hline() + eu.linebreak());
        retStr.append(eu.bold("Rewriting sequence") + eu.linebreak() + eu.linebreak());
        List<Triple<Rule, Position, Trs>> narrowList = this.narrowPair.getNarrowList();
        // if the dp directly semiunifies nothing is to check
        if (narrowList.isEmpty()) {
            retStr.append("The DP semiunifies directly so there is only one rewrite step from "
                + dpLhs.applySubstitution(this.semiUnifier) + " to " + dpRhs.applySubstitution(this.semiUnifier) + ".");
            retStr.append(eu.linebreak() + eu.linebreak());
            return retStr.toString();
        }
        final Direction dir = this.narrowPair.narrowDir;
        TRSTerm actTerm = null;
        TRSTerm newTerm = null;
        // check narrowing direction to know how to narrow
        // forward narrowing: start with rhs of the initial dp and narrow up to pair.y
        if (dir == Direction.RIGHT) {
            actTerm = this.narrowPair.x.applySubstitution(this.semiUnifier);
            final TRSSubstitution ma = dpLhs.getMatcher(actTerm);
            newTerm = actTerm.replaceAll(dpLhs.applySubstitution(ma), dpRhs.applySubstitution(ma));
            retStr.append(eu.bold(actTerm.export(eu)) + " " + eu.rightarrow() + " " + newTerm.export(eu)
                + eu.linebreak() + " with rule " + this.narrowPair.dp.export(eu) + " and matcher " + ma.export(eu)
                + "." + eu.linebreak() + eu.linebreak());
            actTerm = newTerm;
        }
        // backward narrowing: start with pair.x and narrow up to the lhs of the initial dp
        else {
            actTerm = this.narrowPair.x.applySubstitution(this.semiUnifier);
            // reverse the list to get the forward narrowing steps
            final List<Triple<Rule, Position, Trs>> dummyList = new ArrayList<Triple<Rule, Position, Trs>>();
            for (final Triple<Rule, Position, Trs> rTriple : narrowList) {
                dummyList.add(0, rTriple);
            }
            narrowList = dummyList;
        }
        // both cases (forward and backward narrowing) are equal now
        TRSSubstitution actMatcher;
        Position actPos;
        Rule actRule;
        TRSTerm actL;
        TRSTerm actR;
        // check the whole narrowing list
        for (final Triple<Rule, Position, Trs> actTriple : narrowList) {
            actRule = actTriple.x;
            actPos = actTriple.y;
            // get subterm where the unification succeeded and check if this is an innermost step
            final TRSTerm actSubterm = actTerm.getSubterm(actPos);
            // do the narrowing
            final Set<TRSVariable> vars = actTerm.getVariables();
            actRule = actRule.renameVariables(vars);
            actL = actRule.getLeft();
            actR = actRule.getRight();
            actMatcher = actL.getMatcher(actSubterm);
            newTerm = actTerm.replaceAt(actPos, actR.applySubstitution(actMatcher));
            // now fill the string with information
            retStr.append(eu.bold(actTerm.export(eu)));
            retStr.append(" " + eu.rightarrow() + " ");
            retStr.append(newTerm.export(eu) + eu.linebreak());
            //retStr.append("Subterm: " + actSubterm + o.linebreak());
            retStr.append("with rule " + actRule.export(eu));
            retStr.append(" at position " + actPos.export(eu));
            retStr.append(" and matcher " + actMatcher.export(eu) + eu.linebreak() + eu.linebreak());
            actTerm = newTerm;
        }
        if (this.dir == Direction.LEFT) {
            actMatcher = dpLhs.getMatcher(actTerm);
            newTerm = dpRhs.applySubstitution(actMatcher);
            retStr.append(eu.bold(actTerm.export(eu)) + " " + eu.rightarrow() + " " + newTerm.export(eu)
                + eu.linebreak() + "with rule " + this.narrowPair.dp.export(eu) + eu.linebreak() + eu.linebreak());
        }
        retStr.append("Now applying the matcher to the start term leads to a term which is equal to the last term in the rewriting sequence"
            + eu.linebreak());

        // check if the rewrite sequence really loops
        if (Globals.useAssertions) {
            assert (newTerm.equals(this.narrowPair.x.applySubstitution(this.semiUnifier).applySubstitution(this.matcher)));
        }

        retStr.append(eu.linebreak() + eu.linebreak());
        retStr.append("All these steps are and every following step will be a correct step w.r.t to Q."
            + eu.linebreak() + eu.linebreak());
        return retStr.toString();
    }

    private String printNarrowingSequence(final Export_Util eu) {
        final StringBuilder retStr = new StringBuilder();

        retStr.append(eu.hline());
        retStr.append(eu.linebreak());
        retStr.append(eu.bold("Narrowing sequence"));
        retStr.append(eu.linebreak());
        retStr.append(eu.linebreak());
        retStr.append("Initially we have the P-rule "
            + eu.math(this.narrowPair.dp.getLeft().export(eu) + " " + eu.rightarrow() + " "
                + eu.bold(this.narrowPair.dp.getRight().export(eu))));
        retStr.append(eu.linebreak());
        retStr.append(eu.linebreak());
        TRSTerm actS = this.narrowPair.dp.getLeft();
        TRSTerm actT = this.narrowPair.dp.getRight();
        TRSTerm actL = null;
        TRSTerm actR = null;
        TRSTerm actTsub = null;
        TRSTerm actSsub = null;
        Position actPos = null;
        for (final Triple<Rule, Position, Trs> actTriple : this.narrowPair.getNarrowList()) {
            actPos = actTriple.y;
            actL = actTriple.x.getLeft();
            actR = actTriple.x.getRight();
            // direction = right
            if (this.dir == Direction.RIGHT) {
                actTsub = actT.getSubterm(actPos);
                final TRSSubstitution actMgu = actTsub.getMGU(actL);
                final TRSTerm newS = actS.applySubstitution(actMgu);
                final TRSTerm newT = actT.replaceAt(actPos, actR).applySubstitution(actMgu);

                retStr.append(newS.export(eu) + " " + eu.rightarrow() + " " + eu.bold(newT.export(eu)) + ".");
                retStr.append(eu.linebreak());
                retStr.append("with rule " + eu.math(actTriple.x.export(eu)) + " at position "
                    + eu.math(actTriple.y.export(eu)) + " and mgu " + eu.math(actMgu.export(eu)));
                retStr.append(eu.linebreak());
                retStr.append(eu.linebreak());

                actS = newS;
                actT = newT;
            }
            // direction = left
            else {
                actSsub = actS.getSubterm(actPos);
                final TRSSubstitution actMgu = actSsub.getMGU(actR);
                final TRSTerm newT = actT.applySubstitution(actMgu);
                final TRSTerm newS = actS.replaceAt(actPos, actL).applySubstitution(actMgu);

                retStr.append(newS.export(eu) + " " + eu.rightarrow() + " " + eu.bold(newT.export(eu)) + ",");
                retStr.append(eu.linebreak());
                retStr.append("with the inverse of the rule " + eu.math(actTriple.x.export(eu)) + " at position "
                    + eu.math(actTriple.y.export(eu)) + " and mgu " + eu.math(actMgu.export(eu)));
                retStr.append(eu.linebreak());
                retStr.append(eu.linebreak());

                actS = newS;
                actT = newT;
            }
        }
        retStr.append("And after that " + eu.math(actS.export(eu)) + " semiunifies with " + eu.math(actT.export(eu)));
        return retStr.toString();
    }

    public String toBibTeX() {
        // No citations are given.
        return "";
    }
    
    public NarrowPair getNarrowPair() {
        return this.narrowPair;
    }
}
