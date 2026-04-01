package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Utility.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * Non-termination processor for relative termination.
 * Attempts to find a loop in R \cup S which contains
 * at least one R step.
 * @author Ulrich Schmidt-Goertz
 * @version $Id$
 */
public class RelTRSLoopFinder extends RelTRSProcessor {

    private final int totalLimit, leftLimit, rightLimit;

    @ParamsViaArguments({"TotalLimit", "LeftLimit", "RightLimit"})
    public RelTRSLoopFinder(final int totalLimit, final int leftLimit, final int rightLimit) {
        this.totalLimit = totalLimit;
        this.leftLimit = leftLimit;
        this.rightLimit = rightLimit;
    }

    @Override
    public Result processRelTRS(RelTRSProblem problem, Abortion aborter, RuntimeInformation rti) throws AbortionException {

        Set<Rule> RandS = new LinkedHashSet<Rule>(problem.getR());
        RandS.addAll(problem.getS());

        LoopFinder loopFinder = new LoopFinder(ImmutableCreator.create(RandS),
                LoopFinder.Heuristic.NORMAL, this.totalLimit, this.leftLimit, this.rightLimit);
        Set<Loop> loops;
        while ((loops = loopFinder.getLoops(aborter)) != null) {
            for (Loop loop : loops) {
                List<Rule> usedRules = loop.getRules();
                for (Rule rRule : problem.getR()) {
                    if (usedRules.contains(rRule)) {
                        boolean srsProof = Options.certifier.isRainbow() && Boolean.TRUE.equals(rti.getMetadata(Metadata.IS_SRS));
                        return ResultFactory.disproved(new RelTRSLoopFinderProof(loop, problem, srsProof));
                    }
                }
            }
        }
        return ResultFactory.unsuccessful();
    }

    public static class RelTRSLoopFinderProof extends RelTRSProof {

        private final Loop loop;
        private final RelTRSProblem problem;
        private final boolean srs;

        public RelTRSLoopFinderProof(final Loop loop, final RelTRSProblem problem, final boolean srs) {
            this.loop = loop;
            this.problem = problem;
            this.srs = srs;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {

            StringBuilder sb = new StringBuilder("The following loop was found:");
            sb.append(o.linebreak());
            sb.append(o.linebreak());
            sb.append(this.loop.export(o));
            sb.append(o.linebreak());
            sb.append("Therefore, the relative TRS problem does not terminate.");
            return sb.toString();
        }

        @Override
        public Element toDOM(Document doc, XMLMetaData xmlMetaData) {

            Element result;
            if (this.srs) {
                result = XMLTag.RELSRS_NONTERMINATION_PROOF.createElement(doc);
            } else {
                result = XMLTag.RELTRS_NONTERMINATION_PROOF.createElement(doc);
            }
            result.appendChild(this.loop.relativeToDOM(doc, this.problem.getR(), this.problem.getS(), xmlMetaData));
            return result;
        }

        @Override
        public Element toCPF(
                final Document doc,
                final Element[] childrenProofs,
                final XMLMetaData xmlMetaData,
                final CPFModus modus)
        {
            return CPFTag.RELATIVE_NONTERMINATION_PROOF.create(doc, this.loop.toCPF(doc, xmlMetaData, this.problem.getR(), this.problem.getS()));
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return !modus.isPositive();
        }

    }
}
