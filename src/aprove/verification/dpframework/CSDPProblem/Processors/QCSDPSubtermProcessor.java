package aprove.verification.dpframework.CSDPProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.CSDPProblem.*;
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
import immutables.*;

public class QCSDPSubtermProcessor extends QCSDPProcessor {

    private final static Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.QDPSubtermProcessor");

    private final boolean allstrict;
    private final Engine engine;

    @ParamsViaArgumentObject
    public QCSDPSubtermProcessor(Arguments arguments) {
        this.allstrict = arguments.allstrict;
        this.engine = arguments.engine;
    }

    @Override
    public boolean isQCSDPApplicable(QCSDPProblem qcsdp) {
        return qcsdp.isMinimal();
    }

    @Override
    protected Result processQCSDP(QCSDPProblem origqcsdp, Abortion aborter) throws AbortionException {
        Set<Rule> P = origqcsdp.getDp();
        boolean allstrict = this.allstrict;

        if (!allstrict && P.size() == 1) {
            allstrict = true;
        }

        long time = System.nanoTime();
        ImmutableSet<FunctionSymbol> headSyms = origqcsdp.getHeadSymbols();
        SUB muSub = SUB.create(origqcsdp.getRm());
        SUBEncoder encoder = new SUBEncoder(new FullSharingFlatteningFactory<None>(), headSyms, muSub);
        aborter.checkAbortion();
        Formula<None> formula = encoder.encode(P, allstrict, aborter);
        time = System.nanoTime()-time;
        long total = time;
        QCSDPSubtermProcessor.log.log(Level.FINER, "Encoding to propositional logic: {0} ms\n", time/1000000);

        time = System.nanoTime();
        int res[];
        aborter.checkAbortion();
        SATChecker satChecker = this.engine.getSATChecker();
        try{
            res = satChecker.solve(formula, aborter);
        } catch (SolverException e) {
            return ResultFactory.unsuccessful();
        }
        time = System.nanoTime()-time;
        total += time;
        QCSDPSubtermProcessor.log.log(Level.FINER, "SAT solving: {0} ms\n", time/1000000);

        if (res != null) {
            time = System.nanoTime();
            Afs afs = encoder.getAfs(encoder.decode(res, formula.getId()));
            AfsOrder order = new AfsOrder(afs, muSub);
            time = System.nanoTime()-time;
            total += time;
            QCSDPSubtermProcessor.log.log(Level.FINER, "Decoding Afs and LPO: {0} ms\n", time/1000000);
            if (order != null) {
                QCSDPSubtermProcessor.log.log(Level.FINE, "Total time: {0} ms\n", total/1000000);
                return QCSDPSubtermProcessor.getResult(order, origqcsdp);
            }

        }
        QCSDPSubtermProcessor.log.log(Level.FINE, "Total time: {0} ms\n", total/1000000);
        return ResultFactory.unsuccessful();
    }

    static final class QCSDPSubtermProof extends Proof.DefaultProof {

        private final Set<Rule> orientedPRules;
        private final Set<Rule> keptPRules;
        private final ExportableOrder<TRSTerm> order;
        private final BasicObligation origObl;
        private final BasicObligation resultObl;

        QCSDPSubtermProof (Set<Rule> orientedPRules, Set<Rule> keptPRules, ExportableOrder<TRSTerm> order, BasicObligation origObl, BasicObligation resultObl) {
            this.orientedPRules = orientedPRules;
            this.order = order;
            this.keptPRules = keptPRules;
            this.origObl = origObl;
            this.resultObl = resultObl;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            result.append("We use the subterm processor "+o.cite(Citation.DA_EMMES)+".");
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

    }

    /**
     * Standard method to compute the result of a subterm processor.
     * @param order
     * @param origqdp
     * @return
     */
    public static Result getResult(AfsOrder order, QCSDPProblem origqcsdp)
            throws AbortionException {
        // check which elements of P have been oriented strictly
        Set<Rule> newPRules, deletedPRules;
        newPRules = new LinkedHashSet<Rule>();
        deletedPRules = new LinkedHashSet<Rule>();
        for (Rule rule : origqcsdp.getDp()) {
            // only add non-strictly oriented rules
            if (!order.solves(Constraint.fromRule(rule, OrderRelation.GR))) {
                newPRules.add(rule);
            } else {
                deletedPRules.add(rule);
            }
        }

        if (Globals.useAssertions) {
            ImmutableSet<FunctionSymbol> headSyms = origqcsdp.getHeadSymbols();
            Afs afs = order.getAfs();
            for (FunctionSymbol f : afs.getFunctionSymbols()) {
                assert(headSyms.contains(f) && afs.getFiltering(f).y);
            }
            assert(!deletedPRules.isEmpty());
        }

        // build smaller subproblem and proof
        QCSDPProblem newQdp = QCSDPProblem.create(ImmutableCreator.create(newPRules),origqcsdp);
        Proof proof = new QCSDPSubtermProof(deletedPRules, newPRules, order, origqcsdp, newQdp);
        return ResultFactory.proved(newQdp, YNMImplication.EQUIVALENT, proof);

    }

    public static class Arguments {
        public boolean allstrict = false;
        public Engine engine;
    }

}
