package aprove.verification.oldframework.IntTRS.SafetyRedPair;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.SafetyRedPair.Tools.Solvers.Termination.CooperationGraph.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Proof for the SafetyIntTRSPolynomialOrderProcessor.
 * @author marinag, cryingshadow
 */
public class SafetyIntTRSPoloRedPairProof extends DefaultProof {

    /**
     * Lexicographic ranking found.
     */
    private final Map<TRSFunctionApplication, List<SimplePolynomial>> lexRanking;

    /**
     * Non-termination witness.
     */
    private final ErrorPath path;

    /**
     * Collection of rules that have been removed due to a decrease & bounded proof w.r.t. the start term.
     */
    private final Collection<IGeneralizedRule> droppedRules;

    /**
     * Initialize the names for this proof.
     */
    private void initNames() {
        this.shortName = "SafetyPolynomialOrderProcessor";
        this.longName = "SafetyPolynomialOrderProcessor";
    }

    /**
     * @param ranking The ranking function found.
     * @param dropped The rules dropped.
     */
    public SafetyIntTRSPoloRedPairProof(
        Map<TRSFunctionApplication, List<SimplePolynomial>> ranking,
        Collection<IGeneralizedRule> dropped
    ) {
        super();
        this.initNames();
        this.droppedRules = dropped;
        this.lexRanking = ranking;
        this.path = null;
    }

    /**
     * @param ranking The ranking function found.
     */
    public SafetyIntTRSPoloRedPairProof(Map<TRSFunctionApplication, List<SimplePolynomial>> ranking) {
        super();
        this.initNames();
        this.droppedRules = null;
        this.lexRanking = ranking;
        this.path = null;
    }

    /**
     * @param p The non-termination witness found.
     */
    public SafetyIntTRSPoloRedPairProof(ErrorPath p) {
        super();
        this.initNames();
        this.droppedRules = null;
        this.lexRanking = null;
        this.path = p;
    }

    @Override
    public String export(final Export_Util eu, final VerbosityLevel level) {
        final StringBuilder builder = new StringBuilder();
        if (this.path == null) {
            builder.append(eu.indent(eu.bold(eu.tttext("Found the following linear ranking:"))));
            for (final Entry<TRSFunctionApplication, List<SimplePolynomial>> entry : this.lexRanking.entrySet()) {
                if (entry.getValue().isEmpty()) {
                    continue;
                }
                builder.append(eu.linebreak());
                builder.append(entry.getKey().export(eu));
                builder.append(eu.appSpace());
                builder.append(eu.eqSign());
                builder.append(eu.appSpace());
                builder.append(eu.indent(eu.bold(eu.tttext("["))));
                builder.append(eu.appSpace());
                for (final SimplePolynomial f : entry.getValue()) {
                    builder.append(eu.indent(eu.bold(eu.tttext("("))));
                    builder.append(f.export(eu));
                    builder.append(eu.indent(eu.bold(eu.tttext(")"))));
                    builder.append(eu.appSpace());
                }
                builder.append(eu.appSpace());
                builder.append(eu.indent(eu.bold(eu.tttext("]"))));
            }
            builder.append(eu.linebreak());
            if (this.droppedRules == null) {
                builder.append("This proves termination of the whole problem.");
            } else {
                builder.append("Thus, the following rules could be removed:");
                for (IGeneralizedRule rule : this.droppedRules) {
                    builder.append(eu.linebreak());
                    builder.append(eu.export(rule));
                }
            }
        } else {
            builder.append("Proved non-termination by the following feasible error path");
            builder.append(", whose loop can be repeated infinitely often:");
            builder.append(eu.linebreak());
            builder.append(eu.export(this.path));
        }
        return builder.toString();
    }

}