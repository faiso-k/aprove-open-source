
package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.DPProblem.Processors.*;
import aprove.verification.dpframework.DPProblem.Processors.QDPUncurryingProcessor.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * Uncurrying for termination, adapted QDPUncurryingProcessor to work on TRSs.
 * Hardcoded to use generalized uncurrying since this subsumes HMZ-uncurrying.
 *
 * Also applicable for innermost termination by ignoring strategy.
 * BeComplete flag is used to guarantee that ignoring strategy
 * is complete (i.e., if innermost and beComplete, then we require
 * locally confluent overlay TRS)
 *
 * @author Rene Thiemann
 * @version $Id$
 */
public class QTRSUncurryingProcessor extends QTRSProcessor {

    private final boolean noEta;
    private final boolean beComplete;
    private final boolean applicativeSignature;
    private final int limit = 1;

    @ParamsViaArgumentObject
    public QTRSUncurryingProcessor(final Arguments arguments) {
        this.noEta = arguments.noeta;
        this.beComplete = arguments.becomplete;
        this.applicativeSignature = arguments.applicativeSignature;
    }

    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        if (this.applicativeSignature) {
            // check whether there are only constants + exactly one binary symbol
            boolean gotBinary = false;
            for (FunctionSymbol f : qtrs.getRSignature()) {
                int a = f.getArity();
                if (a != 0) {
                    if (a != 2 || gotBinary) {
                        return false;
                    }
                    gotBinary = true;
                }
            }
            if (!gotBinary) {
                return false;
            }
        }
        return QTRSUncurryingProcessor.isUncurryingApplicable(qtrs).x;
    }

    /**
     * determines whether uncurrying is applicable, i.e., if there is application symbol such that
     * all left-hand sides is left-head-variable free.
     *
     * @param qtrs
     * @return the application symbol and a boolean whether its applicable.
     */
    private static Pair<Boolean, FunctionSymbol> isUncurryingApplicable(final QTRSProblem qtrs) {
        final Pair<Boolean, FunctionSymbol> applicable = QDPUncurryingProcessor.getApplicativeInfoGeneralizedR(qtrs.getR());
        final FunctionSymbol appSymbol = applicable.y;
        if (!applicable.x) {
            return new Pair<>(false, appSymbol);
        }
        return new Pair<>(true, appSymbol);
    }

    @Override
    protected Result processQTRS(final QTRSProblem qtrs, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        final boolean complete;
        if (qtrs.getQ().isEmpty()) {
            complete = true;
        } else {
            if (qtrs.isExactlyInnermost()) {
                final CriticalPairs critPairs = qtrs.getCriticalPairs();
                complete = critPairs.isOverlay(aborter) && critPairs.isLocallyConfluent(this.limit, aborter) == YNM.YES;
            } else {
                complete = false;
            }
        }
        if (this.beComplete && !complete) {
            return ResultFactory.unsuccessful();
        }
        // store export information
        final Set<Pair<FunctionSymbol, Set<FunctionSymbol>>> informationSet =
            new LinkedHashSet<>();
        final Set<Rule> R = qtrs.getR();

        final Map<FunctionSymbol, Integer> aa = new LinkedHashMap<>();
        final Set<Rule> u = new LinkedHashSet<>();
        Set<Rule> rEta = new LinkedHashSet<>();
        final Set<Rule> rplus = new LinkedHashSet<>();
        final FreshNameGenerator fg = new FreshNameGenerator(qtrs.getRSignature(), FreshNameGenerator.APPEND_NUMBERS);

        // compute signature F and get the "applicative Symbol"
        final FunctionSymbol appSymbol = QTRSUncurryingProcessor.isUncurryingApplicable(qtrs).y;
        final UncurryMethod method = UncurryMethod.GENERALIZED;

        // applicative arities
        QDPUncurryingProcessor.computeApplicativeArities(R, aa, false, appSymbol, method);
        aa.remove(appSymbol);


        QDPUncurryingProcessor.computeU(u, aa, appSymbol, fg, informationSet);
        final ImmutableSet<Rule> uImmutable = ImmutableCreator.create(u);

        // rEta = R and eta-saturation
        rEta.addAll(R);
        final Set<Rule> newEtaRules = new LinkedHashSet<Rule>();
        QDPUncurryingProcessor.computeREta(rEta, aa, appSymbol, newEtaRules, method);
        if (this.noEta && !newEtaRules.isEmpty()) {
            return ResultFactory.unsuccessful();
        }

        // normalize rEta w.r.t U
        rEta = QDPUncurryingProcessor.evalRules(uImmutable, rEta);
        // R+ = eEta u U
        rplus.addAll(rEta);
        rplus.addAll(uImmutable);

        // nothing happened?
        if (R.equals(rplus)) {
            return ResultFactory.unsuccessful();
        }

        final QTRSProblem newQtrs = QTRSProblem.create(ImmutableCreator.create(rplus));

        final Proof proof =
            new QTRSUncurryingProof(
                qtrs,
                newQtrs,
                appSymbol,
                informationSet,
                uImmutable,
                newEtaRules,
                this.limit);
        final Implication direction = complete ? YNMImplication.EQUIVALENT : YNMImplication.SOUND;
        return ResultFactory.proved(newQtrs, direction, proof);
    }

    public static Element uncurryInformation(
            final Document doc,
            final XMLMetaData xmlMetaData,
            final FunctionSymbol applicationSymbol,
            final Set<Pair<FunctionSymbol, Set<FunctionSymbol>>> informationSet,
            final Set<Rule> uncurryRules,
            final Set<Rule> etaRules) {
        final Element uncurriedSymbols = CPFTag.UNCURRIED_SYMBOLS.create(doc);
        for (final Pair<FunctionSymbol, Set<FunctionSymbol>> entry : informationSet) {
            final FunctionSymbol f = entry.x;
            final Element e = CPFTag.UNCURRIED_SYMBOL_ENTRY.create(doc,
                    f.toCPF(doc, xmlMetaData),
                    CPFTag.ARITY.create(doc, f.getArity())
                    );
            for (final FunctionSymbol fi : entry.y) {
                e.appendChild(fi.toCPF(doc, xmlMetaData));
            }
            uncurriedSymbols.appendChild(e);
        }
        return CPFTag.UNCURRY_INFORMATION.create(doc,
                applicationSymbol.toCPF(doc, xmlMetaData),
                uncurriedSymbols,
                CPFTag.UNCURRY_RULES.create(doc, CPFTag.rules(doc, xmlMetaData, uncurryRules)),
                CPFTag.ETA_RULES.create(doc, CPFTag.rules(doc, xmlMetaData, etaRules)));
    }

}

class QTRSUncurryingProof extends QTRSProof {
    private final QTRSProblem oldQtrs;
    private final QTRSProblem newQtrs;
    private final FunctionSymbol applicationSymbol;
    private final Set<Pair<FunctionSymbol, Set<FunctionSymbol>>> informationSet;
    private final Set<Rule> uncurryRules;
    private final Set<Rule> etaRules;
    private final int limit;

    public QTRSUncurryingProof(
        final QTRSProblem oldQtrs,
        final QTRSProblem newQtrs,
            final FunctionSymbol applicationSymbol,
            final Set<Pair<FunctionSymbol, Set<FunctionSymbol>>> informationSet,
        final Set<Rule> uncurryRules,
        final Set<Rule> etaRules,
        final int limit)
    {
        this.oldQtrs = oldQtrs;
        this.newQtrs = newQtrs;
        this.applicationSymbol = applicationSymbol;
        this.informationSet = informationSet;
        this.uncurryRules = uncurryRules;
        this.etaRules = etaRules;
        this.limit = limit * 10;
        // since the limit in criticalPairs uses parallel rewriting,
        // the sequential number may be higher. Multiplying by 10 is just
        // some heuristic value.
    }

    @Override
    public String export(final Export_Util o, final VerbosityLevel level) {
        final QTRSProblem eta = QTRSProblem.create(ImmutableCreator.create(this.etaRules));
        final QTRSProblem uncurried = QTRSProblem.create(ImmutableCreator.create(this.uncurryRules));
        return "The applicative DPProblem has been uncurried according to "
            + o.cite(new Citation[] {Citation.CSRT_FROCOS11 })
                 + "." + o.linebreak() + o.cond_linebreak()
            + "The uncurried symbol is: " + this.applicationSymbol.export(o) + o.linebreak()
            + "The eta expanded rules are: " + o.linebreak() + eta.export(o) + "The uncurrying rules are: "
            + o.linebreak() + uncurried.export(o) + o.cond_linebreak() + this.newQtrs.export(o);
    }

    @Override
    public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
        Element uncurry =
            CPFTag.UNCURRY.create(doc,
                QTRSUncurryingProcessor.uncurryInformation(
                        doc,
                        xmlMetaData,
                        this.applicationSymbol,
                        this.informationSet,
                        this.uncurryRules,
                        this.etaRules),
                CPFTag.trs(doc, xmlMetaData, this.newQtrs.getR()),
                childrenProofs[0]);
        if (modus.isPositive()) {
            return this.positiveTag().create(doc, uncurry);
        } else {
            uncurry = this.negativeTag().create(doc, uncurry);
            if (this.oldQtrs.getQ().isEmpty()) {
                return uncurry;
            } else {
                return this.negativeTag().create(
                    doc,
                    CPFTag.SWITCH_FULL_STRATEGY.create(
                        doc,
                        CPFTag.WCR_PROOF.create(doc, CPFTag.JOINABLE_CRITICAL_PAIRS_B_F_S.create(doc, this.limit)),
                        uncurry));
            }
        }
    }

    @Override
    public boolean isCPFCheckableProof(final CPFModus modus) {
        return true;
    }


}
