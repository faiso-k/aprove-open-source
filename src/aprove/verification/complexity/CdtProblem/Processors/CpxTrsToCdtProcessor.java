package aprove.verification.complexity.CdtProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.CpxTrsProblem.Processors.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;

public class CpxTrsToCdtProcessor extends RuntimeComplexityTrsProcessor {

    @Override
    protected boolean isRuntimeComplexityTrsApplicable(final RuntimeComplexityTrsProblem obl) {
        return obl.getRewriteStrategy() == RewriteStrategy.INNERMOST
                || obl.getRewriteStrategy() == RewriteStrategy.PARALLEL_INNERMOST;
    }

    @Override
    public Result processRuntimeComplexityTrs(final RuntimeComplexityTrsProblem cpxTrs, final Abortion aborter)
            throws AbortionException {
        final Pair<Map<Cdt, Rule>, CdtProblem> mapCdtp =
                CdtProblem.create(cpxTrs.getR(),
                    cpxTrs.getRewriteStrategy() == RewriteStrategy.PARALLEL_INNERMOST);
        // For non-confluent cpxTrs, this processor is not always sound
        // for lower bounds, see Ex. 11 in JAR paper "Analyzing Innermost
        // Runtime Complexity of Term Rewriting by Dependency Pairs" by
        // Noschinski, Emmes, Giesl (2013).
        // TODO use sufficient criteria for confluence of rewrite relation
        // so that BothBounds.create() can be used in these case.
        return ResultFactory.proved(mapCdtp.y, UpperBound.create(),
                new CpxTrsToCdtProof(mapCdtp.x, mapCdtp.y, cpxTrs.getRewriteStrategy()));
    }

    public static class CpxTrsToCdtProof extends CpxProof {

        final Map<Cdt, Rule> cdtRuleMap;
        final CdtProblem cdtProb;
        final RewriteStrategy rewriteStrategy;

        public CpxTrsToCdtProof(final Map<Cdt, Rule> map, final CdtProblem prob,
                final RewriteStrategy rewriteStrategy) {
            this.cdtRuleMap = map;
            this.cdtProb = prob;
            this.rewriteStrategy = rewriteStrategy;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            // FIXME real proof
            return "Converted Cpx (relative) TRS with rewrite strategy "
                        + this.rewriteStrategy + " to CDT";
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            xmlMetaData = this.adaptMetaData(xmlMetaData);
            final Element res = CPFTag.DT_TRANSFORMATION.create(doc);
            final Element strict = CPFTag.STRICT_DTS.create(doc);
            final Element weak = CPFTag.WEAK_DTS.create(doc);
            final Set<Cdt> S = this.cdtProb.getS();
            for (final Map.Entry<Cdt, Rule> entry : this.cdtRuleMap.entrySet()) {
                final Cdt cdt = entry.getKey();
                final Rule rule = entry.getValue();
                final Element elem =
                    CPFTag.RULE_WITH_DT.create(doc, rule.toCPF(doc, xmlMetaData), cdt.toCPF(doc, xmlMetaData));
                if (S.contains(cdt)) {
                    strict.appendChild(elem);
                } else {
                    weak.appendChild(elem);
                }
            }
            res.appendChild(strict);
            res.appendChild(weak);
            final Element innermost = CPFTag.INNERMOST_LHSS.create(doc);
            for (final Cdt cdt : this.cdtProb.getTuples()) {
                innermost.appendChild(cdt.getRuleLHS().toCPF(doc, xmlMetaData));
            }
            res.appendChild(innermost);
            res.appendChild(childrenProofs[0]);
            return this.positiveTag().create(doc, res);
        }

        @Override
        public XMLMetaData adaptMetaData(final XMLMetaData xmlPreMetaData) {
            final Map<FunctionSymbol, FunctionSymbol> tupleToDefined = new HashMap<>();
            for (final Map.Entry<Cdt, Rule> cdtToRule : this.cdtRuleMap.entrySet()) {
                tupleToDefined.put(cdtToRule.getKey().getRuleLHS().getRootSymbol(), cdtToRule
                    .getValue()
                    .getRootSymbol());
            }
            return DependencyPairsProcessor.adaptMetaData(xmlPreMetaData, tupleToDefined, this.cdtProb.getSignature());

        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }

    }

}
