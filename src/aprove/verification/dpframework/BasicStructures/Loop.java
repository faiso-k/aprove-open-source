package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.TRSProblem.Utility.*;
import aprove.xml.*;

/**
 * this class represents a TRS-Loop
 *
 * @author Sebastian Weise
 */

public class Loop implements XMLObligationExportable {
    /**
     * "terms", "rules", "positions" and "substitutions" represent a reduction sequence;
     * iff the method "check()" below returns "true" then this reduction sequence is sound
     *      and "terms.getFirst().applySubstitution(matcher).equals(terms.getLast().getSubterm(pos)) == true"
     */
    private final ArrayList<TRSTerm> terms;
    private final ArrayList<Rule> rules;
    private final ArrayList<Position> positions;
    private final ArrayList<TRSSubstitution> substitutions;
    private Position pos;
    private TRSSubstitution matcher;
    private Context context;

    /**
     * the lists and the Context Position are initialized
     */
    public Loop() {
        this.terms = new ArrayList<TRSTerm>();
        this.rules = new ArrayList<Rule>();
        this.positions = new ArrayList<Position>();
        this.substitutions = new ArrayList<TRSSubstitution>();

        this.pos = Position.create();
    }

    /**
     * self-speaking constructor
     */
    public Loop(final ArrayList<TRSTerm> terms, final ArrayList<Rule> rules,
            final ArrayList<Position> positions,
            final ArrayList<TRSSubstitution> substitutions, final Position pos,
            final TRSSubstitution matcher) {
        this.terms = terms;
        this.rules = rules;
        this.positions = positions;
        this.substitutions = substitutions;
        this.pos = pos;
        this.matcher = matcher;
    }

    public ArrayList<TRSTerm> getTerms() {
        return this.terms;
    }

    public ArrayList<Rule> getRules() {
        return this.rules;
    }

    public ArrayList<Position> getPositions() {
        return this.positions;
    }

    public ArrayList<TRSSubstitution> getSubstitutions() {
        return this.substitutions;
    }

    public Position getPosition() {
        return this.pos;
    }

    public TRSSubstitution getMatcher() {
        return this.matcher;
    }

    /**
     * this method should only be used if the "check()"-method below was done before,
     *      otherwise the result may be incorrect or even runtime errors may occur !
     */
    public Context getContext() {
        if (this.context == null) {
            this.context = Context.create(this.getLast(), this.pos);
        }

        return this.context;
    }

    public void setPosition(final Position pos) {
        this.pos = pos;
    }

    public void setMatcher(final TRSSubstitution matcher) {
        this.matcher = matcher;
    }

    /**
     * returns the last Term of the Rewriting Sequence (this.terms) and "null" if there is no such Term!
     */
    public TRSTerm getLast() {
        final int length = this.terms.size();
        if (length > 0) {
            return this.terms.get(this.terms.size() - 1);
        } else {
            return null;
        }
    }

    /**
     * checks the Loop for soundness;
     * no runtime errors should occur at "false" loops!
     */
    public boolean check() {
        // avoid runtime errors
        if (this.terms == null || this.rules == null || this.positions == null
                || this.substitutions == null || this.pos == null
                || this.matcher == null) {
            return false;
        }

        final int termsLength = this.terms.size();
        if (termsLength < 2) {
            return false;
        }
        if (this.rules.size() != termsLength - 1
                || this.positions.size() != termsLength - 1
                || this.substitutions.size() != termsLength - 1) {
            return false;
        }

        // check reduction sequence for soundness

        TRSTerm actTerm, actNextTerm, actSubTerm, actLhs, actRhs;
        Rule actRule;
        Position actPosition;
        TRSSubstitution actMatcher;

        for (int i = 0; i <= this.rules.size() - 1; i++) {
            actTerm = this.terms.get(i);
            actNextTerm = this.terms.get(i + 1);
            actRule = this.rules.get(i);
            actPosition = this.positions.get(i);
            actMatcher = this.substitutions.get(i);

            actSubTerm = actTerm.getSubterm(actPosition);
            actLhs = actRule.getLeft();
            actRhs = actRule.getRight();

            if (!actSubTerm.equals(actLhs.applySubstitution(actMatcher))) {
                return false;
            }

            if (!actNextTerm.equals(actTerm.replaceAt(actPosition, actRhs
                    .applySubstitution(actMatcher)))) {
                return false;
            }
        }

        // check whether the reduction sequence really loops
        return (this.terms.get(0).applySubstitution(this.matcher).equals(this
                .getLast().getSubterm(this.pos)));
    }

    /**
     * returns a shallow copy of this loop
     */
    public Loop shallowCopy() {
        return new Loop(new ArrayList<TRSTerm>(this.terms), new ArrayList<Rule>(
                this.rules), new ArrayList<Position>(this.positions),
                new ArrayList<TRSSubstitution>(this.substitutions), this.pos,
                this.matcher);
    }

    /**
     * this method should only be used if the "check()"-method above was done before,
     *      otherwise the given statements may be incorrect or even runtime errors may occur !
     */
    public String export(final Export_Util eu) {
        final StringBuilder temp = new StringBuilder();

        temp.append("---------- Loop: ----------" + eu.linebreak()
                + eu.linebreak());

        TRSTerm actTerm, actNextTerm;
        Rule actRule;
        Position actPosition;
        TRSSubstitution actMatcher;

        for (int i = 0; i <= this.rules.size() - 1; i++) {
            actTerm = this.terms.get(i);
            actNextTerm = this.terms.get(i + 1);
            actRule = this.rules.get(i);
            actPosition = this.positions.get(i);
            actMatcher = this.substitutions.get(i);

            temp.append(actTerm.export(eu) + " " + eu.rightarrow() + " "
                    + actNextTerm.export(eu) + " with rule "
                    + actRule.export(eu) + " at position " + actPosition
                    + " and matcher " + actMatcher.export(eu) + eu.linebreak()
                    + eu.linebreak());
        }

        temp.append("Now an instance of the first term with Matcher "
                + this.matcher.export(eu)
                + " occurs in the last term at position " + this.pos.export(eu)
                + "." + eu.linebreak() + eu.linebreak());

        temp.append("Context: " + this.getContext().getAsTerm().export(eu)
                + eu.linebreak());

        return temp.toString();
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element loopTag = XMLTag.LOOP.createElement(doc);

        for (int i = 0; i <= this.rules.size() - 1; i++) {
            final TRSTerm actTerm = this.terms.get(i);
            final TRSTerm actNextTerm = this.terms.get(i + 1);
            final Rule actRule = this.rules.get(i);
            final Position actPosition = this.positions.get(i);
            final TRSSubstitution actMatcher = this.substitutions.get(i);

            final Element stepTag = XMLTag.STEP.createElement(doc);
            stepTag.appendChild(actTerm.toDOM(doc, xmlMetaData));
            stepTag.appendChild(actNextTerm.toDOM(doc, xmlMetaData));
            stepTag.appendChild(actRule.toDOM(doc, xmlMetaData));
            stepTag.appendChild(actPosition.toDOM(doc, xmlMetaData));
            stepTag.appendChild(actMatcher.toDOM(doc, xmlMetaData));

            loopTag.appendChild(stepTag);
        }
        loopTag.appendChild(this.pos.toDOM(doc, xmlMetaData));
        loopTag.appendChild(this.getContext().toDOM(doc, xmlMetaData));
        loopTag.appendChild(this.matcher.toDOM(doc, xmlMetaData));
        final Element last = XMLTag.TERM.createElement(doc);
        loopTag.appendChild(last);
        return loopTag;
    }

    public Element relativeToDOM(final Document doc, final Set<Rule> R, final Set<Rule> S, final XMLMetaData xmlMetaData) {
        final Element loopTag = XMLTag.LOOP.createElement(doc);

        int i = 0, sSteps = 0;
        Element sStepsTag = XMLTag.S_STEPS.createElement(doc);
        while (i < this.rules.size()) {

            final TRSTerm actTerm = this.terms.get(i);
            final TRSTerm actNextTerm = this.terms.get(i + 1);
            final Rule actRule = this.rules.get(i);
            final Position actPosition = this.positions.get(i);
            final TRSSubstitution actMatcher = this.substitutions.get(i);

            final Element stepTag = XMLTag.STEP.createElement(doc);
            stepTag.appendChild(actTerm.toDOM(doc, xmlMetaData));
            stepTag.appendChild(actNextTerm.toDOM(doc, xmlMetaData));
            stepTag.appendChild(actRule.toDOM(doc, xmlMetaData));
            stepTag.appendChild(actPosition.toDOM(doc, xmlMetaData));
            stepTag.appendChild(actMatcher.toDOM(doc, xmlMetaData));

            if (S.contains(actRule)) { // S-step
                sStepsTag.appendChild(stepTag);
                ++sSteps;
            } else { // R-step
                final Element relStepTag = XMLTag.RELATIVE_STEP.createElement(doc);
                if (sSteps > 0) {
                    relStepTag.appendChild(sStepsTag);
                    sSteps = 0;
                    sStepsTag = XMLTag.S_STEPS.createElement(doc);
                }
                relStepTag.appendChild(stepTag);
                loopTag.appendChild(relStepTag);
            }

            ++i;
        }
        if (sSteps > 0) {
            // loop does not end with an R-step: append remaining S-steps
            final Element relStepTag = XMLTag.RELATIVE_STEP.createElement(doc);
            relStepTag.appendChild(sStepsTag);
            loopTag.appendChild(relStepTag);
        }
        loopTag.appendChild(this.pos.toDOM(doc, xmlMetaData));
        loopTag.appendChild(this.getContext().toDOM(doc, xmlMetaData));
        loopTag.appendChild(this.matcher.toDOM(doc, xmlMetaData));
        return loopTag;
    }

    /**
     * exports this loop to CPF
     * @param doc non-null
     * @param xmlMetaData non-null
     * @param origR non-null
     * @param origS maybe null, if loop only considers steps in R
     * @return
     */
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData, final Set<Rule> origR, Set<Rule> origS) {
        final Element rewriteSequence =
                CPFTag.REWRITE_SEQUENCE.create(
                        doc,
                        CPFTag.START_TERM.create(doc, this.terms.get(0).toCPF(doc, xmlMetaData)));
        TRSTerm actNextTerm;
        GeneralizedRule actRule;
        Position actPosition;
        final Map<GeneralizedRule, GeneralizedRule> RMap = new HashMap<>(origR.size());
        for (final GeneralizedRule rule : origR) {
            RMap.put(rule, rule);
        }
        if (origS == null) {
            origS = new HashSet<Rule>(0);
        }
        final Map<GeneralizedRule, GeneralizedRule> SMap = new HashMap<>(origS.size());
        for (final GeneralizedRule rule : origS) {
            SMap.put(rule, rule);
        }
        for (int i = 0; i <= this.rules.size() - 1; i++) {
            actNextTerm = this.terms.get(i + 1);
            actPosition = this.positions.get(i);
            actRule = this.rules.get(i);
            GeneralizedRule origRule = RMap.get(actRule);
            if (origRule != null) {
                rewriteSequence.appendChild(CPFTag.REWRITE_STEP.create(
                        doc,
                        actPosition.toCPF(doc, xmlMetaData),
                        origRule.toCPF(doc, xmlMetaData),
                        actNextTerm.toCPF(doc, xmlMetaData)));
            } else {
                origRule = SMap.get(actRule);
                rewriteSequence.appendChild(CPFTag.REWRITE_STEP.create(
                        doc,
                        actPosition.toCPF(doc, xmlMetaData),
                        origRule.toCPF(doc, xmlMetaData),
                        CPFTag.RELATIVE.create(doc),
                        actNextTerm.toCPF(doc, xmlMetaData)));
            }
        }
        return CPFTag.LOOP.create(
                doc,
                rewriteSequence,
                this.getMatcher().toCPF(doc, xmlMetaData),
                this.getContext().toCPF(doc, xmlMetaData));
    }


    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }
}
