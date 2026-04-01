package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;


/**
 * a processor implementing a better variant of GA01
 * Verification of Erlang Processes by Dependency Pairs, Thm. 16:
 *
 * What we check is the following:
 * - R must be an overlay system (The requirements in Thm. 16 also require
 *   this, although it is not written there explicitly. From R_2 non-overlapping
 *   we have no overlaps of R_2 with R_2 rules. And as roots(R_1) in Sigma and the
 *   conditions on Sigma we know that no R_1 rule can reach into another rule. Finally
 *   the restriction that R_1 and R_2 may form no critical pairs ensures that no R_2 rule
 *   reaches into an R_1 rule.)
 *
 * - we have a fixed subsignature Sigma and a partition R = R_1 cup R_2
 * - R_2 is non-collapsing, {root(l), root(r)} subseteq Sigma for all l -> r in R_2
 * - no R_1 rule contains symbols of Sigma
 * - no R_2 rule contains symbols of Sigma below the Root
 * - R_1 is locally confluent
 *
 * The difference to the original Thm. is that instead of R_2 being non-overlapping
 * we only require R_2 being overlay and locally confluent.
 *
 *  Note that this processor fully captures Overlay + loc. confluence Theorem as one can
 *  always choose R_1 = R, Sigma = R_2 = empty.
 *
 * @author thiemann
 *
 */


public class AAECCInnermostProcessor extends QTRSProcessor {

    private final int limit;
    private final boolean force;

    @ParamsViaArgumentObject
    public AAECCInnermostProcessor(final Arguments arguments) {
        this.force = arguments.force;
        this.limit = arguments.limit;
    }

    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        return qtrs.getQ().isEmpty() && !qtrs.getR().isEmpty();
    }


    @Override
    protected Result processQTRS(final QTRSProblem qtrs, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {

        // we need that TRS R is an overlay system.
        if (!qtrs.getCriticalPairs().isOverlay(aborter)) {
            if (this.force) {
                final QTRSProblem newQTRS = qtrs.createInnermost();
                return ResultFactory.proved(newQTRS, YNMImplication.COMPLETE, new AAECCInnermostProof(qtrs, newQTRS, 0));
            }
            return ResultFactory.unsuccessful();
        }

        final SortedSet<FunctionSymbol> nonSigma = new TreeSet<FunctionSymbol>(); // sorting for determinism;
        final int n = qtrs.getR().size();
        final Set<Rule> R_1 = new LinkedHashSet<Rule>(n);
        final Collection<Rule> R_2 = new LinkedList<Rule>();

        // sort according to collapsing rules,
        // and add all non-root fct-symbols to nonSigma

        // after this loop every fct-symbol of a rule in R_1 is also in nonSigma
        for (final Rule l_to_r : qtrs.getR()) {
            final TRSFunctionApplication l = l_to_r.getLeft();
            final TRSTerm r = l_to_r.getRight();
            if (r.isVariable() || Options.certifier.isCeta()) {
                R_1.add(l_to_r);
                l.collectFunctionSymbols(nonSigma);
                r.collectFunctionSymbols(nonSigma);
            } else {
                final TRSFunctionApplication fr = (TRSFunctionApplication) r;
                if (nonSigma.contains(fr.getRootSymbol()) || nonSigma.contains(l.getRootSymbol())) {
                    R_1.add(l_to_r);
                    l.collectFunctionSymbols(nonSigma);
                    fr.collectFunctionSymbols(nonSigma);
                } else {
                    R_2.add(l_to_r);
                    for (final TRSTerm arg : l.getArguments()) {
                        arg.collectFunctionSymbols(nonSigma);
                    }
                    for (final TRSTerm arg : fr.getArguments()) {
                        arg.collectFunctionSymbols(nonSigma);
                    }
                }
            }
        }

        boolean changed = !nonSigma.isEmpty();
        // now check that whenever we have a rule f(.) -> g(.) in R2 and
        // one of the symbols f or g is not in sigma, that
        // then we add both f,g to non-sigma and shift the rule into R1
        while (changed) {
            changed = false;
            final Iterator<Rule> r2Iterator = R_2.iterator();

            while (r2Iterator.hasNext()) {
                final Rule l_to_r = r2Iterator.next();
                final FunctionSymbol f = l_to_r.getRootSymbol();
                final FunctionSymbol g = ((TRSFunctionApplication) l_to_r.getRight()).getRootSymbol();
                if (nonSigma.contains(f) || nonSigma.contains(g)) {
                    r2Iterator.remove();
                    R_1.add(l_to_r);
                    final boolean newChange1 = nonSigma.add(f);
                    final boolean newChange2 = nonSigma.add(g);
                    changed |= newChange1 || newChange2;
                }
            }

        }

        // overlappingness of R1 with R2 is enforced by overlay system
        if (Globals.useAssertions) {
            for (final Rule r2Rule : R_2) {
                final TRSFunctionApplication lhs = (TRSFunctionApplication) r2Rule.getLeft().renumberVariables(TRSTerm.SECOND_STANDARD_PREFIX);
                for (final TRSTerm lhsArg : lhs.getArguments()) {
                    for (final TRSFunctionApplication subTerm : lhsArg.getNonVariableSubTerms()) {
                        final FunctionSymbol f = subTerm.getRootSymbol();
                        for (final Rule r1Rule : R_1) {
                            if (r1Rule.getRootSymbol().equals(f) && r1Rule.getLhsInStandardRepresentation().unifies(subTerm)) {
                                // okay, we have a non-root overlap, so we must put this rule into R_1.
                                // but then R_1 is not an overlay system and hence we fail!
                                assert(false);
                            }
                        }
                    }
                }
            }
        }



        // now the conditions are all satisfied, and we can compute
        // sigma

        final Set<FunctionSymbol> sigma = new LinkedHashSet<FunctionSymbol>();
        for (final FunctionSymbol f : qtrs.getRSignature()) {
            if (!nonSigma.contains(f)) {
                sigma.add(f);
            }
        }

        // okay, now we have our systems R1, R2, and Sigma
        // (the largest possible system R2)


        if (Globals.useAssertions) {
            // check that we really have a valid partition.
            for (final Rule l_to_r : R_2) {
                AAECCInnermostProcessor.checkR2(l_to_r.getLeft(), sigma);
                AAECCInnermostProcessor.checkR2(l_to_r.getRight(), sigma);
            }
            for (final Rule l_to_r : R_1) {
                final Collection<FunctionSymbol> fs = l_to_r.getFunctionSymbols();
                // no sigma-symbols in R 1
                assert(!fs.removeAll(sigma));
            }
        }

        // if R = R_1, then we can used the cached critical pairs of R.
        // (then this theorem gained us nothing, and we have regular NOC)
        final CriticalPairs critPairs = R_2.isEmpty() || Options.certifier.isCeta() ? new CriticalPairs(qtrs) : new CriticalPairs(R_1, Rule.getRuleMap(R_1));

        if (YNM.YES == critPairs.isLocallyConfluent(this.limit, aborter)) {
            // hooray, criterion is satisfied,
            // lets switch to innermost.

            final QTRSProblem newQTRS = qtrs.createInnermost();

            final Result result =
                ResultFactory.proved(newQTRS, YNMImplication.EQUIVALENT, new AAECCInnermostProof(
                    qtrs,
                    newQTRS,
                    R_1,
                    R_2,
                    sigma,
                    false,
                    this.limit));
            return result;

        } else {
            if (this.force) {
                final QTRSProblem newQTRS = qtrs.createInnermost();
                return ResultFactory.proved(newQTRS, YNMImplication.COMPLETE, new AAECCInnermostProof(qtrs, newQTRS, this.limit));
            }
            return ResultFactory.unsuccessful();
        }
    }

    private static void checkR2(final TRSTerm t, final Set<FunctionSymbol> sigma) {
        assert(!t.isVariable());
        final TRSFunctionApplication ft = (TRSFunctionApplication) t;
        assert(sigma.contains(ft.getRootSymbol()));
        for (final TRSTerm arg : ft.getArguments()) {
            for (final FunctionSymbol f : arg.getFunctionSymbols()) {
                assert(!sigma.contains(f));
            }
        }
    }

    private static class AAECCInnermostProof extends QTRSProof {

        private final QTRSProblem resultObl;
        private final QTRSProblem origObl;

        private final Collection<Rule> R_1;
        private final Collection<Rule> R_2;
        private final Set<FunctionSymbol> sigma;
        private final boolean wasForced;
        private final int testDepth;


        private AAECCInnermostProof(
            final QTRSProblem origObl,
            final QTRSProblem resultObl,
            final Collection<Rule> R_1,
            final Collection<Rule> R_2,
            final Set<FunctionSymbol> sigma,
            final boolean wasForced,
            final int testDepth)
        {
            this.origObl = origObl;
            this.resultObl = resultObl;
            this.R_1 = R_1;
            this.R_2 = R_2;
            this.sigma = sigma;
            this.wasForced = wasForced;
            if (!wasForced) {
                this.shortName = R_2.isEmpty() ? "Overlay + Local Confluence" : "AAECC Innermost";
                this.longName = this.shortName;
            }
            this.testDepth = testDepth * 10;
            // since the testDepth in criticalPairs uses parallel rewriting,
            // the sequential number may be higher. Multiplying by 10 is just
            // some heuristic value.
        }

        public AAECCInnermostProof(final QTRSProblem origObl, final QTRSProblem resultObl, final int testDepth) {
            this(origObl, resultObl, null, null, null, true, testDepth);
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            if (this.wasForced) {
                res.append("Forcing to innermost!");
            } else if (this.R_2.isEmpty()) {
                res.append("The TRS is overlay and locally confluent. By "+o.cite(Citation.NOC)+" we can switch to innermost.");
            } else {
                res.append("We have applied "+o.cite(new Citation[]{Citation.NOC, Citation.AAECCNOC})+ " to switch to innermost. " +
                "The TRS R 1 is ");
                res.append(o.set(this.R_1, Export_Util.RULES));
                res.append(o.cond_linebreak());

                res.append("The TRS R 2 is ");
                res.append(o.set(this.R_2, Export_Util.RULES));
                res.append(o.cond_linebreak());

                res.append("The signature Sigma is ");
                res.append(o.set(this.sigma, Export_Util.SIMPLESET));
            }

            return res.toString();
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (!this.isCPFCheckableProof(modus)) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            }
            if (modus.isPositive()) {
                final Element wcrProof = CPFTag.WCR_PROOF.create(
                        doc,CPFTag.JOINABLE_CRITICAL_PAIRS_B_F_S.create(
                            doc,
                            doc.createTextNode(this.testDepth + "")));
                return CPFTag.TRS_TERMINATION_PROOF.create(doc,
                    CPFTag.SWITCH_INNERMOST.create(doc,
                        wcrProof,
                        childrenProofs[0]));
            } else {
                return CPFTag.TRS_NONTERMINATION_PROOF.create(doc,
                    CPFTag.INNERMOST_LHSS_INCREASE.create(doc,
                        this.resultObl.getQ().toCPF(doc, xmlMetaData),
                        childrenProofs[0]));
            }
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return !(modus.isPositive() && this.R_2 != null && !this.R_2.isEmpty());
        }


    }

    public static class Arguments {
        public int limit = 1;
        public boolean force = false;
    }

}