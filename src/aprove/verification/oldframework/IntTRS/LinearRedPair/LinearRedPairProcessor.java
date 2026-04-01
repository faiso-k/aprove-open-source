package aprove.verification.oldframework.IntTRS.LinearRedPair;

import java.math.*;
import java.util.*;
import java.util.Map.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Export.Utility.Export_Util.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;

/**
 * This processor tries to synthesize some linear rankings, which can be used to
 * simplify the given int-TRS.
 *
 * Docu-guess (fuhs):
 * By now essentially superseded by the more modern RankingRedPairProcessor.
 *
 * @author Matthias Hoelzel
 */
public class LinearRedPairProcessor extends Processor.ProcessorSkeleton {
    /** Some arguments */
    private final Arguments arguments;

    /** Some arguments */
    public static class Arguments {
        /** Export the (huge) prepared rules? */
        public boolean exportPreparedRules;

        /** Export some (huge) LCSs? */
        public boolean exportLCSs;

        /** Use constants? */
        public boolean useConstants;
    }

    /**
     * A constructor.
     * @param args Arguments for the processor.
     */
    public LinearRedPairProcessor(final Arguments args) {
        this.arguments = args;
    }

    /**
     * A constructor without arguments.
     */
    public LinearRedPairProcessor() {
        this.arguments = new Arguments();
    }

    /**
     * Setter for the argument exportPreparedRules
     * @param val a boolean value
     */
    public void setExportPreparedRules(final boolean val) {
        this.arguments.exportPreparedRules = val;
    }

    /**
     * Setter for the argument exportLCSs
     * @param val a boolean value
     */
    public void setExportLCSs(final boolean val) {
        this.arguments.exportLCSs = val;
    }

    /**
     * Setter for the argument useConstants
     * @param val a boolean value
     */
    public void setUseConstants(final boolean val) {
        this.arguments.useConstants = val;
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSwTProblem && ((IRSwTProblem) obl).isIRS();
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        assert obl instanceof IRSwTProblem : "Wrong obligation type!";
        final IRSProblem problem;
        if (obl instanceof IRSProblem) {
            problem = (IRSProblem) obl;
        } else {
            problem = new IRSProblem((IRSwTProblem) obl);
        }
        final LinearRankingProof proof = new LinearRankingProof(this.arguments.useConstants);
        final LinearRedPairWorker lrw = new LinearRedPairWorker(problem, proof, this.arguments, aborter);

        final IRSProblem newProb = lrw.work();

        if (!(lrw.hasChanged())) {
            return ResultFactory.unsuccessful();
        } else if (newProb.getRules().isEmpty()) {
            return ResultFactory.proved(proof);
        } else {
            return ResultFactory.proved(newProb, YNMImplication.EQUIVALENT, proof);
        }
    }

    /**
     * A very fine proof.
     * @author cotto (don't blame me), Matthias Hoelzel
     */
    class LinearRankingProof extends DefaultProof {
        /** Collection of dropped rules. Can also be null. */
        private Collection<IGeneralizedRule> droppedRules;

        /** The linear ranking */
        private Map<FunctionSymbol, ArrayList<PreciseRational>> interpretation;

        /** Rules obtained by preparation */
        private Set<IGeneralizedRule> preparedRules;

        /** The LCSs we created */
        private LinkedList<LCS> lcss;

        /** Did we use some affine interpretations? */
        private final boolean usedConstants;

        /**
         * Create the proof.
         * @param constantsEnabled we need to know the resulting interpretation
         * might use some constants or not
         */
        public LinearRankingProof(final boolean constantsEnabled) {
            super();
            this.shortName = LinearRedPairProcessor.class.getSimpleName();
            this.longName = this.shortName;

            this.usedConstants = constantsEnabled;
        }

        /**
         * Setter for interpretation.
         * @param ranking the linear ranking, maps functions symbols to
         * coefficients.
         */
        public void setInterpretation(final Map<FunctionSymbol, ArrayList<PreciseRational>> ranking) {
            this.interpretation = ranking;
        }

        /**
         * Sets the dropped rules.
         * @param dropped collection of rules
         */
        public void setDroppedRules(final Collection<IGeneralizedRule> dropped) {
            this.droppedRules = dropped;
        }

        /**
         * Setter for preparedRules.
         * @param rules some set of rules
         */
        public void setPreparedRules(final Set<IGeneralizedRule> rules) {
            this.preparedRules = rules;
        }

        /**
         * Setter for lcss.
         * @param systems a list of linear constraint systems
         */
        public void setLCSs(final LinkedList<LCS> systems) {
            this.lcss = systems;
        }

        /**
         * @param eu export helper
         * @param level unused
         * @return a useless string
         */
        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();

            // Export the prepared rules:
            if (this.preparedRules != null) {
                sb.append(eu.indent(eu.bold(eu.tttext("After preparation, we obtained the following rules:"))));
                sb.append(eu.linebreak());
                for (final IGeneralizedRule rule : this.preparedRules) {
                    sb.append(rule.export(eu));
                    sb.append(eu.linebreak());
                }
                sb.append(eu.linebreak());
            }

            // Export the LCSs:
            if (this.lcss != null) {
                sb.append(eu.indent(eu.bold(eu.tttext("Obtained the following linear constraint systems:"))));
                sb.append(eu.linebreak());
                for (final LCS lcs : this.lcss) {
                    sb.append(lcs.export(eu));
                    sb.append(eu.linebreak());
                }
                sb.append(eu.linebreak());
            }

            // Export interpretation:
            this.exportInterpretation(eu, sb);

            return sb.toString();
        }

        /**
         * Export the interpretation. This method is called by export().
         * @param eu some export helper
         * @param sb some string builder
         */
        private void exportInterpretation(final Export_Util eu, final StringBuilder sb) {
            if (this.interpretation != null) {
                sb.append(eu.indent(eu.bold(eu.tttext("Linear ranking:"))));
                sb.append(eu.linebreak());
                for (final Entry<FunctionSymbol, ArrayList<PreciseRational>> entry : this.interpretation.entrySet()) {
                    sb.append(eu.escape("["));
                    sb.append(entry.getKey().export(eu));
                    sb.append(eu.escape("(") + eu.fontcolor(eu.escape("x"), Color.RED) + eu.escape(")"));
                    sb.append(eu.escape("] "));
                    sb.append(eu.eqSign());
                    sb.append(eu.escape(" "));

                    final ArrayList<PreciseRational> rationals = entry.getValue();
                    boolean first = true;
                    boolean allZero = true;
                    for (int i = 0; i < rationals.size(); i++) {
                        final PreciseRational r = rationals.get(i);
                        if (r.getNumerator().equals(BigInteger.ZERO)) {
                            continue;
                        }
                        allZero = false;
                        if (!first) {
                            sb.append(eu.escape(" + "));
                        }
                        first = false;
                        final String ratString = r.export(eu);

                        // The first index is the constant, if we used some constants:
                        if (!(this.usedConstants && i == 0)) {
                            sb.append(eu.fontcolor(ratString, Color.BLUE));
                            sb.append(eu.multSign());
                            final int realIndex = this.usedConstants ? i : i + 1;
                            sb.append(eu.fontcolor(eu.escape("x") + eu.sub("" + realIndex), Color.RED));
                        } else {
                            sb.append(eu.fontcolor(ratString, Color.BLUE));
                        }
                    }
                    if (allZero) {
                        sb.append(eu.escape("0"));
                    }
                    sb.append(eu.linebreak());
                }
                sb.append(eu.indent(eu.escape("where ")
                    + eu.fontcolor("x ", Color.RED)
                    + eu.eqSign()
                    + eu.escape(" (")
                    + eu.fontcolor(eu.escape("x") + eu.sub("1"), Color.RED)
                    + eu.escape(", ")
                    + eu.fontcolor(eu.escape("..."), Color.RED)
                    + eu.escape(" ,")
                    + eu.fontcolor(eu.escape("x") + eu.sub("n"), Color.RED)
                    + eu.escape(").")));
                sb.append(eu.linebreak());
            }

            if (this.droppedRules != null && this.droppedRules.size() > 0) {
                sb.append(eu.linebreak());
                sb.append(eu.indent(eu.bold(eu.tttext("Therefore the following rule(s) have been dropped:"))));
                sb.append(eu.linebreak());
                for (final IGeneralizedRule rule : this.droppedRules) {
                    sb.append(rule.export(eu));
                    sb.append(eu.linebreak());
                }
            }
        }
    }
}
