package aprove.verification.dpframework.TRSProblem.Processors;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Utility.SRSNonLoop.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;

/**
 * SRSNonLoop Processor <br>
 * based on the dimploma thesis "Automatische Erkennung von Ableitungsmustern in
 * nichtterminierenden Wortersetzungssystemen" by Martin Oppelt
 *
 * @author Tim Enger
 */

public class SRSNonLoopProcessor extends QTRSProcessor {

    /**
     * until this size of newStructures <br>
     * every "size" is checked if overlapsWith with OC1 rules
     */
    private final int compareWithOC1;

    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        return SRSNonLoopProcessor.getSRSInfo(qtrs) && qtrs.getQ().isEmpty();
    }

    /**
     * check if QTRS is a SRS
     *
     * @param qtrs
     *        QTRSProblem
     * @return true, if the QTRS is a SRS
     */
    private static boolean getSRSInfo(final QTRSProblem qtrs) {
        for (final FunctionSymbol funsym : qtrs.getSignature()) {
            if (!(funsym.getArity() == 1)) {
                return false;
            }
        }
        return true;
    }

    @ParamsViaArgumentObject
    public SRSNonLoopProcessor(final Arguments args) {
        this.compareWithOC1 = args.compareWithOC1;
    }

    @Override
    protected Result processQTRS(final QTRSProblem qtrs,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException {

        final long start = System.currentTimeMillis();

        final NonLoopFinder nonLoopFinder =
            new NonLoopFinder(aborter, qtrs, this.compareWithOC1);

        final DerivationStructure nonLoop = nonLoopFinder.findNonLoop();

        if (Globals.DEBUG_NEX) {
            System.err.println("Needed Time:"
                + ((System.currentTimeMillis() - start) / 1000.0) + "s");
        }

        return ResultFactory.disproved(new NonTerminationProof(qtrs, nonLoop));
    }

    /**
     * Proof of the NonLoop processor
     *
     * @author Tim Enger
     */
    private class NonTerminationProof extends QTRSProof {

        final private DerivationStructure nonLoop;
        final private QTRSProblem origTrs;

        public NonTerminationProof(final QTRSProblem origTrs, final DerivationStructure nonLoop) {
            this.nonLoop = nonLoop;
            this.origTrs = origTrs;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {

            final StringBuilder sb = new StringBuilder();
            sb.append("We used the non-termination processor "
                + eu.cite(Citation.OPPELT08)
                + " to show that the SRS problem is infinite.");
            sb.append(eu.linebreak());
            sb.append(eu.linebreak());
            sb.append("Found the self-embedding DerivationStructure: ");
            sb.append(eu.linebreak());
            sb.append(eu.quote(this.exportDerivationStructure(this.nonLoop, eu)));
            sb.append(eu.linebreak());
            sb.append(this.exportStructure(this.nonLoop, 0, eu));
            sb.append(eu.linebreak());

            return sb.toString();
        }

        private String exportStructure(final DerivationStructure ds,
            final int depth,
            final Export_Util eu) {
            final StringBuilder sb = new StringBuilder();

            sb.append(this.exportDerivationStructure(ds, eu));
            sb.append(eu.linebreak());
            sb.append("by ");
            sb.append(ds.getReason());

            for (final DerivationStructure ds1 : ds.getReason().getParents()) {
                sb.append(eu.quote(this.exportStructure(ds1, depth + 1, eu)));
            }
            return sb.toString();
        }

        private String exportStringPattern(final StringPattern sp, final Export_Util eu) {
            final StringBuilder sb = new StringBuilder();
            int i;
            for (i = 0; i < sp.getList().size() - 1; i++) {
                sb.append(sp.getList().get(i).export(eu));
                sb.append(" ");
            }
            if (sp.getList().size() > 0) {
                sb.append(sp.getList().get(i).export(eu));
            }
            return sb.toString();
        }

        private String exportWordPattern(final WordPattern wp, final Export_Util eu) {
            final StringBuilder sb = new StringBuilder();

            if (wp.getL().size() > 0) {
                sb.append(this.exportStringPattern(wp.getL(), eu));
                sb.append(" ");
            }

            sb.append("(");
            sb.append(this.exportStringPattern(wp.getM(), eu));
            sb.append(")");
            sb.append(eu.sup(wp.getF().toString()));

            if (wp.getR().size() > 0) {
                sb.append(" ");
                sb.append(this.exportStringPattern(wp.getR(), eu));
            }

            return sb.toString();
        }

        private String exportDerivationStructure(final DerivationStructure ds,
            final Export_Util eu) {
            final StringBuilder sb = new StringBuilder();
            if (ds instanceof DerivationPattern) {
                final DerivationPattern dp = (DerivationPattern) ds;
                sb.append(this.exportWordPattern(dp.getLhs(), eu));
                sb.append(" ");
                sb.append(eu.rightarrow());
                sb.append(" ");
                sb.append(this.exportWordPattern(dp.getRhs(), eu));
            } else {
                final OverlapClosure oc = (OverlapClosure) ds;
                sb.append(this.exportStringPattern(oc.getLhs(), eu));
                sb.append(" ");
                sb.append(eu.rightarrow());
                sb.append(" ");
                sb.append(this.exportStringPattern(oc.getRhs(), eu));
            }
            return sb.toString();
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            return CPFTag.TRS_NONTERMINATION_PROOF.create(doc,
                    this.nonLoop.toNontermCPF(doc, xmlMetaData));
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return !modus.isPositive();
        }

        @Override
        public String getNonCPFExportableReason(final CPFModus modus) {
            return super.getNonCPFExportableReason(modus) + " contains " + this.nonLoop.getClass().getCanonicalName();
        }


    }

    @SuppressWarnings("unused")
    public static class Arguments {
        private final int NEVER = 0;

        private final int EVERYTIME = 5000000;

        public int compareWithOC1 = this.EVERYTIME;
    }
}