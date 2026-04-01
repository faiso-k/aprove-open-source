package aprove.verification.dpframework.Utility.NonLoop.structures.proofed.nontermination;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Utility.NonLoop.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.*;
import aprove.verification.dpframework.Utility.NonLoop.structures.proofed.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

/**
 * @author Tim Enger
 */

public class NonLoopProof extends QDPProof {

    private static final String INDENT_HTML = "&nbsp;&nbsp;&nbsp;&nbsp;";
    private static final String INDENT_PLAIN = "    ";

    /**
     * we need the original obligation for having the metadata
     */
    private BasicObligation origObl;

    private final ProofedRule pr;
    private final Position pi;
    private final int m;
    private final int b;
    private final TRSSubstitution sigmaPrime;
    private final TRSSubstitution muPrime;
    
    public ProofedRule getProofedRule() {
        return pr;
    }

    private NonLoopProof(final ProofedRule pr, final Position pi, final int m, final int b,
            final TRSSubstitution sigmaPrime, final TRSSubstitution muPrime) {
        if (m < 0 || b < 0) {
            throw new RuntimeException("invalid m or b");
        }
        final PatternTerm lhs = pr.getPatternRule().getLhs();
        final PatternTerm rhs = pr.getPatternRule().getRhs();
        final TRSSubstitution sigma = lhs.getSigma();
        final TRSSubstitution mu = lhs.getMu();
        final TRSSubstitution sigmaT = rhs.getSigma();
        final TRSSubstitution muT = rhs.getMu();

        TRSSubstitution sigmaM = TRSSubstitution.EMPTY_SUBSTITUTION;
        for (int i = 0; i < m; ++i) {
            sigmaM = sigmaM.compose(sigma);
        }

        if (!sigmaT.equals(sigmaM.compose(sigmaPrime))) {
            throw new RuntimeException("invalid sigmaPrime or m");
        }

        if (!muT.equals(mu.compose(muPrime))) {
            throw new RuntimeException("invalid muPrime");
        }

        if (!Utils.commutative(sigmaPrime, sigma) || !Utils.commutative(sigmaPrime, mu)) {
            throw new RuntimeException("sigmaPrime does not commute");
        }

        final TRSTerm tPi = rhs.getT().getSubterm(pi);

        TRSTerm sSigmaB = lhs.getT();
        for (int i = 0; i < b; ++i) {
            sSigmaB = sSigmaB.applySubstitution(sigma);
        }

        if (!sSigmaB.equals(tPi)) {
            throw new RuntimeException("s sigma^b != t|pi");
        }

        this.pr = pr;
        this.pi = pi;
        this.m = m;
        this.b = b;
        this.sigmaPrime = sigmaPrime;
        this.muPrime = muPrime;
    }

    /**
     * set it to have it in export
     *
     * @param origOblArg the original obligation
     */
    public void setObligation(final BasicObligation origOblArg) {
        this.origObl = origOblArg;
    }

    public static NonLoopProof create(final ProofedRule pr,
        final Position pi,
        final int m,
        final int b,
        final TRSSubstitution sigmaPrime,
        final TRSSubstitution muPrime) {
        return new NonLoopProof(pr, pi, m, b, sigmaPrime, muPrime);
    }

    @Override
    public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {

        final Element nonLoopTag = CPFTag.NON_LOOP.createElement(doc);
        nonLoopTag.appendChild(this.pr.toCPF(doc, xmlMetaData));
        nonLoopTag.appendChild(this.sigmaPrime.toCPF(doc, xmlMetaData));
        nonLoopTag.appendChild(this.muPrime.toCPF(doc, xmlMetaData));
        final Element natural1 = CPFTag.NATURAL.createElement(doc);
        natural1.appendChild(doc.createTextNode("" + this.m));
        nonLoopTag.appendChild(natural1);
        final Element natural2 = CPFTag.NATURAL.createElement(doc);
        natural2.appendChild(doc.createTextNode("" + this.b));
        nonLoopTag.appendChild(natural2);
        nonLoopTag.appendChild(this.pi.toCPF(doc, xmlMetaData));

        return CPFTag.DP_NONTERMINATION_PROOF.create(doc, nonLoopTag);
    }

    @Override
    public boolean isCPFCheckableProof(final CPFModus modus) {
        return !modus.isPositive();
    }


    @Override
    public String export(final Export_Util eu) {
        return this.export(eu, VerbosityLevel.MIDDLE);
    }

    @Override
    public String export(final Export_Util eu, final VerbosityLevel level) {
        if (this.pr == null) {
            return "invalid proof object";
        }

        final StringBuilder sb = new StringBuilder();

        sb.append("By Theorem 8 " + eu.cite(Citation.NONLOOP) + " we deduce infiniteness of the QDP.");
        sb.append(eu.linebreak());
        sb.append("We apply the theorem with m = " + this.m + ", b = " + this.b + ", " + eu.linebreak() + "\u03c3' = "
            + this.sigmaPrime.export(eu) + ", and " + "\u03bc' = " + this.muPrime.export(eu));
        sb.append(" on the rule" + eu.linebreak() + this.pr.export(eu));

        sb.append(eu.linebreak());
        sb.append("This rule is correct for the QDP as the following derivation shows:");
        sb.append(eu.linebreak());

        // show the first rule again at the top of the proof.
        this.pr.setShowRule();

        final boolean fullProof = VerbosityLevel.HIGH.equals(level);
        if (eu instanceof HTML_Util) {
            sb.append(this.pr.export(eu, "", NonLoopProof.INDENT_HTML, true, fullProof));
        } else {
            sb.append(this.pr.export(eu, "", NonLoopProof.INDENT_PLAIN, true, fullProof));
        }

        return sb.toString();
    }
}
