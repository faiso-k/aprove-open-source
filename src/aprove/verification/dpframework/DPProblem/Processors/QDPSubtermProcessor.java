package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;
import java.util.logging.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.SAT.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

public class QDPSubtermProcessor extends QDPProblemProcessor {

    private final static Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.QDPSubtermProcessor");

    private final boolean allstrict;
    private final Engine engine;

    @ParamsViaArgumentObject
    public QDPSubtermProcessor(final Arguments arguments) {
        this.allstrict = arguments.allstrict;
        this.engine = arguments.engine;
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        return qdp.getMinimal() &&
            QDPSubtermProcessor.headSymbolsAreAtLeastUnary(qdp);
            // no simple projections possible for constants

    }

    private static boolean headSymbolsAreAtLeastUnary(final QDPProblem qdp) {
        for (final FunctionSymbol f : qdp.getHeadSymbols()) {
            if (f.getArity() == 0) {
                return false;
            }
        }
        return true;
    }

    @Override
    protected Result processQDPProblem(final QDPProblem origqdp, final Abortion aborter) throws AbortionException {
        final Set<Rule> P = origqdp.getP();
        boolean allstrict = this.allstrict;

        if (!allstrict && P.size() == 1) {
            allstrict = true;
        }

        long time = System.nanoTime();
        final ImmutableSet<FunctionSymbol> headSyms = origqdp.getHeadSymbols();
        final SUBEncoder encoder = new SUBEncoder(new FullSharingFlatteningFactory<None>(), headSyms, SUB.theSUB);
        aborter.checkAbortion();
        final Formula<None> formula = encoder.encode(P, allstrict, aborter);
        time = System.nanoTime()-time;
        long total = time;
        QDPSubtermProcessor.log.log(Level.FINER, "Encoding to propositional logic: {0} ms\n", time/1000000);

        time = System.nanoTime();
        int res[];
        aborter.checkAbortion();
        final SATChecker satChecker = this.engine.getSATChecker();
        try {
            res = satChecker.solve(formula, aborter);
        } catch (final SolverException e) {
            return ResultFactory.unsuccessful();
        }
        time = System.nanoTime()-time;
        total += time;
        QDPSubtermProcessor.log.log(Level.FINER, "SAT solving: {0} ms\n", time/1000000);

        if (res != null) {
            time = System.nanoTime();
            final Afs afs = encoder.getAfs(encoder.decode(res, formula.getId()));
            final AfsOrder order = new AfsOrder(afs, SUB.theSUB);
            time = System.nanoTime()-time;
            total += time;
            QDPSubtermProcessor.log.log(Level.FINER, "Decoding Afs and LPO: {0} ms\n", time/1000000);
            if (order != null) {
                QDPSubtermProcessor.log.log(Level.FINE, "Total time: {0} ms\n", total/1000000);
                return QDPSubtermProcessor.getResult(order, origqdp);
            }

        }
        QDPSubtermProcessor.log.log(Level.FINE, "Total time: {0} ms\n", total/1000000);
        return ResultFactory.unsuccessful();
    }

    static final class QDPSubtermProof extends QDPProof {

        private final Set<Rule> orientedPRules;
        private final Set<Rule> keptPRules;
        private final ExportableOrder<TRSTerm> order;
        private final QDPProblem origObl;
        private final QDPProblem resultObl;

        QDPSubtermProof (final Set<Rule> orientedPRules, final Set<Rule> keptPRules, final ExportableOrder<TRSTerm> order, final QDPProblem origObl, final QDPProblem resultObl) {
            this.orientedPRules = orientedPRules;
            this.order = order;
            this.keptPRules = keptPRules;
            this.origObl = origObl;
            this.resultObl = resultObl;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            result.append("We use the subterm processor "+o.cite(Citation.SUBTERM_CRITERION)+".");
            result.append(o.paragraph()+o.cond_linebreak());
            result.append("The following pairs can be oriented strictly and are deleted.");
            result.append(o.cond_linebreak());
            result.append(o.set(this.orientedPRules, Export_Util.RULES));
            result.append("The remaining pairs can at least be oriented weakly.");
            result.append(o.cond_linebreak());
            result.append(o.set(this.keptPRules, Export_Util.RULES));
            result.append("Used ordering:  ");
            result.append(this.order.export(o));
            result.append(o.cond_linebreak());
            return result.toString();
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (modus.isPositive()) {
                return CPFTag.DP_PROOF.create(doc,
                        CPFTag.SUBTERM_PROC.create(doc,
                                ((AfsOrder) this.order).getAfs().toCPF(doc, xmlMetaData),
                                CPFTag.dps(doc, xmlMetaData, this.resultObl.getP()),
                                childrenProofs[0]
                                ));
            } else {
                return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.resultObl);
            }
        }


        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }


    }

    /**
     * Standard method to compute the result of a subterm processor.
     * @param order
     * @param origqdp
     * @return
     */
    public static Result getResult(final AfsOrder order, final QDPProblem origqdp)
            throws AbortionException {
        // check which elements of P have been oriented strictly
        Set<Rule> newPRules, deletedPRules;
        newPRules = new LinkedHashSet<Rule>();
        deletedPRules = new LinkedHashSet<Rule>();
        for (final Rule rule : origqdp.getP()) {
            // only add non-strictly oriented rules
            if (!order.solves(Constraint.fromRule(rule, OrderRelation.GR))) {
                newPRules.add(rule);
            } else {
                deletedPRules.add(rule);
            }
        }

        if (Globals.useAssertions) {
            final ImmutableSet<FunctionSymbol> headSyms = origqdp.getHeadSymbols();
            final Afs afs = order.getAfs();
            for (final FunctionSymbol f : afs.getFunctionSymbols()) {
                assert(headSyms.contains(f) && afs.getFiltering(f).y);
            }
            assert(!deletedPRules.isEmpty());
        }

        // build smaller subproblem and proof
        final QDPProblem newQdp = origqdp.getSubProblem(ImmutableCreator.create(newPRules));
        final Proof proof = new QDPSubtermProof(deletedPRules, newPRules, order, origqdp, newQdp);
        return ResultFactory.proved(newQdp, YNMImplication.EQUIVALENT, proof);

    }

    public static class Arguments {
        public boolean allstrict = false;
        public Engine engine;
    }


}
