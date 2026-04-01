package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.TRSProblem.Utility.*;
import aprove.xml.*;

/**
 * the same as the class "Loop", but for GENERALIZED Rules !
 *
 * @author Sebastian Weise
 */

public class GeneralizedLoop {
    /**
     * "terms", "rules", "positions" and "substitutions" represent a reduction sequence;
     * iff the method "check()" below returns "true" then this reduction sequence is sound
     *      and "terms.getFirst().applySubstitution(matcher).equals(terms.getLast().getSubterm(pos)) == true"
     */
    private final ArrayList<TRSTerm> terms;
    private final ArrayList<GeneralizedRule> rules;
    private final ArrayList<Position> positions;
    private final ArrayList<TRSSubstitution> substitutions;
    private Position pos;
    private TRSSubstitution matcher;
    private Context context;

    /**
     * the lists and the Context Position are initialized
     */
    public GeneralizedLoop() {
        this.terms = new ArrayList<TRSTerm>();
        this.rules = new ArrayList<GeneralizedRule>();
        this.positions = new ArrayList<Position>();
        this.substitutions = new ArrayList<TRSSubstitution>();

        this.pos = Position.create();
    }

    /**
     * self-speaking constructor
     */
    public GeneralizedLoop(final ArrayList<TRSTerm> terms,
            final ArrayList<GeneralizedRule> rules,
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

    /**
     * transforms a "Simple" Loop into a Generalized Loop;
     * ! note: "side-effects" on the Simple Loop !
     */
    public GeneralizedLoop(final Loop simpleLoop) {
        this.terms = simpleLoop.getTerms();

        this.rules = new ArrayList<GeneralizedRule>();
        this.rules.addAll(simpleLoop.getRules());

        this.positions = simpleLoop.getPositions();
        this.substitutions = simpleLoop.getSubstitutions();
        this.pos = simpleLoop.getPosition();
        this.matcher = simpleLoop.getMatcher();
    }

    /**
     * get- & set-methods
     */

    public ArrayList<TRSTerm> getTerms() {
        return this.terms;
    }

    public ArrayList<GeneralizedRule> getRules() {
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
        GeneralizedRule actRule;
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
    public GeneralizedLoop shallowCopy() {
        return new GeneralizedLoop(new ArrayList<TRSTerm>(this.terms),
                new ArrayList<GeneralizedRule>(this.rules),
                new ArrayList<Position>(this.positions),
                new ArrayList<TRSSubstitution>(this.substitutions), this.pos,
                this.matcher);
    }

    /**
     * this method should only be used if the "check()"-method above was done before,
     *      otherwise the given statements may be incorrect or even runtime errors may occur !
     */
    public String export(final Export_Util eu) {
        final StringBuffer temp = new StringBuffer();

        temp.append("---------- Loop: ----------" + eu.linebreak()
                + eu.linebreak());

        TRSTerm actTerm, actNextTerm;
        GeneralizedRule actRule;
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

    public Element toCPF(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final Set<? extends GeneralizedRule> origRules)
    {
        final Element rewriteSequence =
            CPFTag.REWRITE_SEQUENCE.create(
                doc,
                CPFTag.START_TERM.create(doc, this.terms.get(0).toCPF(doc, xmlMetaData)));
        TRSTerm actNextTerm;
        GeneralizedRule actRule;
        Position actPosition;
        final Map<GeneralizedRule, GeneralizedRule> ruleMap = new HashMap<>(origRules.size());
        for (final GeneralizedRule rule : origRules) {
            ruleMap.put(rule, rule);
        }
        for (int i = 0; i <= this.rules.size() - 1; i++) {
            actNextTerm = this.terms.get(i + 1);
            actRule = this.rules.get(i);
            actRule = ruleMap.get(actRule); // find original rule to this rule, with original variables
            actPosition = this.positions.get(i);
            rewriteSequence.appendChild(CPFTag.REWRITE_STEP.create(
                doc,
                actPosition.toCPF(doc, xmlMetaData),
                actRule.toCPF(doc, xmlMetaData),
                actNextTerm.toCPF(doc, xmlMetaData)));
        }
        return CPFTag.LOOP.create(
            doc,
            rewriteSequence,
            this.getMatcher().toCPF(doc, xmlMetaData),
            this.getContext().toCPF(doc, xmlMetaData));
    }
}
