package aprove.verification.dpframework.Utility.NonLoop.structures;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.*;
import aprove.xml.*;
import immutables.*;

/**
 * A PatternRule consists of:
 * <ol>
 * <li>A left-hand side {@link PatternTerm} l</li>
 * <li>A right-hand side {@link PatternTerm} r</li>
 * </ol>
 *
 * @author Tim Enger
 */

public class PatternRule implements Exportable, Immutable, XMLObligationExportable, CPFAdditional {

    private final PatternTerm lhs;
    private final PatternTerm rhs;
    private final int hashCode;

    public PatternRule(final PatternTerm lhs, final PatternTerm rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
        this.hashCode = lhs.hashCode() * 17 + rhs.hashCode() * 23;

        if (Globals.useAssertions) {
            assert this.checkLhsandRhs();
        }
    }

    private boolean checkLhsandRhs() {
        final Set<TRSVariable> rhsVars = this.rhs.getInstanceVariables();
        rhsVars.removeAll(this.lhs.getInstanceVariables());
        return rhsVars.isEmpty();
    }

    /**
     * @return if sigma_l and mu_l of lhs and sigma_r and mu_r of rhs are all
     *         empty substitutions.
     */
    public boolean isSigmaAndMuEmpty() {
        return this.lhs.isSigmaAndMuEmpty() && this.rhs.isSigmaAndMuEmpty();
    }

    /**
     * @return Left-hand side {@link PatternTerm} of this rule.
     */
    public PatternTerm getLhs() {
        return this.lhs;
    }

    /**
     * @return Right-hand side {@link PatternTerm} of this rule.
     */
    public PatternTerm getRhs() {
        return this.rhs;
    }

    /**
     * @return A {@link Set} of all used {@link TRSVariable Variables} in the ·
     *         {@link PatternTerm left-hand} and {@link PatternTerm right-hand}
     *         side of this {@link PatternRule}.
     */
    public Set<TRSVariable> getAllVariables() {
        final Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>();

        vars.addAll(this.lhs.getAllVariables());
        vars.addAll(this.rhs.getAllVariables());

        return vars;
    }

    /**
     * <p>
     * A {@link PatternRule} s\sigma_s^n\mu_s is <b>already represented</b> if:<br>
     * <br>
     * There is a {@link PatternRule} t'\sigma'^n\mu' in the {@link Set}
     * <tt>toCheck</tt> where \sigma = \sigma' and \mu = \mu' and t = t'\sigma'.
     * </p>
     *
     * @param toCheck
     *            The {@link Set} to check against.
     * @return <tt>True</tt> if <tt>this</tt> is already represented in the
     *         {@link Set} <tt>toCheck</tt>, else <tt>false</tt>.
     */
    public boolean isAlreadyRepresented(final Set<ProofedRule> toCheck) {
        for (final ProofedRule pOld : toCheck) {
            final PatternTerm lOld = pOld.getPatternRule().getLhs();
            final PatternTerm l = this.getLhs();

            if (l.getSigma().equals(lOld.getSigma())
                && l.getMu().equals(lOld.getMu())) {
                if (lOld.getT().applySubstitution(l.getSigma()).equals(l.getT())) {
                    return true;
                }
            }
        }
        return false;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String export(final Export_Util eu) {
        return this.getLhs().export(eu) + " " + eu.rightarrow() + " "
            + this.getRhs().export(eu);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public boolean equals(final Object o) {
        if (this == o) {
            return true;
        }

        if (o == null) {
            return false;
        }

        if (this.hashCode == o.hashCode()) {
            if (o instanceof PatternRule) {
                final PatternRule other = (PatternRule) o;
                if (this.getLhs().equals(other.getLhs())
                    && this.getRhs().equals(other.getRhs())) {
                    return true;
                }
            }
        }
        return false;
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element patternRule = XMLTag.PATTERN_RULE.createElement(doc);
        patternRule.appendChild(this.lhs.toDOM(doc, xmlMetaData));
        patternRule.appendChild(this.rhs.toDOM(doc, xmlMetaData));
        return patternRule;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element patternRule = CPFTag.PATTERN_RULE.createElement(doc);
        patternRule.appendChild(this.lhs.toCPF(doc, xmlMetaData));
        patternRule.appendChild(this.rhs.toCPF(doc, xmlMetaData));
        return patternRule;
    }

}
