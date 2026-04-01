package aprove.verification.dpframework.DPProblem.Processors;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.Utility.SRSNonLoop.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

/**
 * QDPNonLoop Processor <br>
 * for QDPProblems in SRS form with empty Q<br>
 * Using NonLoopFinder on QDPProblem<br>
 * <br>
 * based on the dimploma thesis "Automatische Erkennung von Ableitungsmustern in
 * nichtterminierenden Wortersetzungssystemen" by Martin Oppelt
 *
 * @author Tim Enger
 */

public class QDP_SRSNonLoopProcessor extends QDPProblemProcessor {

    /**
     * until this size of newStructures <br>
     * every "size" is checked if overlapsWith with OC1 rules
     */
    private final int compareWithOC1;

    @ParamsViaArgumentObject
    public QDP_SRSNonLoopProcessor(final Arguments args) {
        this.compareWithOC1 = args.compareWithOC1;
    }

    @Override
    public boolean isQDPApplicable(QDPProblem qdp) {
        return QDP_SRSNonLoopProcessor.getSRSInfo(qdp) && qdp.getQ().isEmpty();
    }

    /**
     * check if QTRS is a SRS
     *
     * @param qtrs
     *        QTRSProblem
     * @return true, if the QTRS is a SRS
     */
    private static boolean getSRSInfo(QDPProblem qdp) {
        for (FunctionSymbol funsym : qdp.getSignature()) {
            if (!(funsym.getArity() == 1)) {
                return false;
            }
        }
        return true;
    }

    @Override
    protected Result processQDPProblem(QDPProblem qdp, Abortion aborter)
            throws AbortionException {

        long start = System.currentTimeMillis();

        NonLoopFinder nonLoopFinder =
            new NonLoopFinder(aborter, qdp, this.compareWithOC1);

        DerivationStructure nonLoop = nonLoopFinder.findNonLoop();

        if (Globals.DEBUG_NEX) {
            System.err.println("Needed Time:"
                + ((System.currentTimeMillis() - start) / 1000.0) + "s");
        }

        return ResultFactory.disproved(new NonTerminationProof(qdp, nonLoop));
    }

    /**
     * Proof of the NonLoop processor
     *
     * @author Tim Enger
     */
    private class NonTerminationProof extends QDPProof {

        final QDPProblem qdp;
        DerivationStructure nonLoop;

        public NonTerminationProof(
            QDPProblem qdp, DerivationStructure nonLoop) {
            this.qdp = qdp;
            this.nonLoop = nonLoop;
        }

        @Override
        public String export(Export_Util eu, VerbosityLevel level) {

            StringBuilder sb = new StringBuilder();
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

        private String exportStructure(DerivationStructure ds,
            int depth,
            Export_Util eu) {
            StringBuilder sb = new StringBuilder();

            sb.append(this.exportDerivationStructure(ds, eu));
            sb.append(eu.linebreak());
            sb.append("by ");
            sb.append(ds.getReason());

            for (DerivationStructure ds1 : ds.getReason().getParents()) {
                sb.append(eu.quote(this.exportStructure(ds1, depth + 1, eu)));
            }
            return sb.toString();
        }

        private String exportStringPattern(StringPattern sp, Export_Util eu) {
            StringBuilder sb = new StringBuilder();
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

        private String exportWordPattern(WordPattern wp, Export_Util eu) {
            StringBuilder sb = new StringBuilder();

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

        private String exportDerivationStructure(DerivationStructure ds,
            Export_Util eu) {
            StringBuilder sb = new StringBuilder();
            if (ds instanceof DerivationPattern) {
                DerivationPattern dp = (DerivationPattern) ds;
                sb.append(this.exportWordPattern(dp.getLhs(), eu));
                sb.append(" ");
                sb.append(eu.rightarrow());
                sb.append(" ");
                sb.append(this.exportWordPattern(dp.getLhs(), eu));
            } else {
                OverlapClosure oc = (OverlapClosure) ds;
                sb.append(this.exportStringPattern(oc.getLhs(), eu));
                sb.append(" ");
                sb.append(eu.rightarrow());
                sb.append(" ");
                sb.append(this.exportStringPattern(oc.getRhs(), eu));
            }
            sb.append(" [");
            sb.append(ds.getType());
            sb.append("]");

            return sb.toString();
        }

    }

    @SuppressWarnings("unused")
    public static class Arguments {
        private final int NEVER = 0;

        private final int EVERYTIME = 5000000;

        public int compareWithOC1 = this.EVERYTIME;
    }

}
