package aprove.verification.dpframework.IDPProblem.Processors.nonInf;

import java.util.*;
import java.util.logging.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.Processors.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Monoids.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 *
 * @author mpluecke
 */
public class IDPNonInfStrategySelect extends IDPProcessor {

    private static Logger log = Logger.getLogger("prove.DPFramework.IDPProblem.Processors.nonInf.IDPNonInfStrategySelect");

    private String fastStrat;
    private String slowStrat;
    private String shapedStrat;
    private String natStrat;
    private int outDegreeSwitch;
    private ExportableString descr;
    private IdpShapeHeuristic poloShapeHeuristic;

    @ParamsViaArgumentObject
    public IDPNonInfStrategySelect(Arguments arguments) {
        this.fastStrat = arguments.fastStrat;
        this.slowStrat = arguments.slowStrat;
        this.shapedStrat = arguments.shapedStrat;
        this.natStrat = arguments.natStrat;
        this.outDegreeSwitch = arguments.outDegreeSwitch;
        this.poloShapeHeuristic = arguments.poloShapeHeuristic;
    }


    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode,
            Abortion aborter, RuntimeInformation rti) throws AbortionException {
        IDPProblem idp = (IDPProblem) obl; // this cast will succeed (see isApplicable)
        // FIXME: We will probably have some simple abortion cases here
        // (cached, empty, ...) cf. QDPProblemProcessor
        String stratName;

        // multiply out degrees
        int outDegrees = 1;
        for (IIDependencyGraph scc : idp.getIdpGraph().splitIntoSCCs(this)) {
            for (Node node : scc.getNodes()) {
                outDegrees *= scc.getSuccessors(node).size();
            }
        }
        if (this.outDegreeSwitch > outDegrees) {
            // slow strategies possible

            // check if shape heuristic applies
            CoeffOrder<BigIntImmutable> coeffOrder =
                new BigIntImmutableOrder();
            GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> outerPolyFactory =
                new FullSharingFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>();
            GPolyFactory<BigIntImmutable, GPolyVar> coeffFactory =
                new FullSharingFactory<BigIntImmutable, GPolyVar>();
            ConstraintFactory<BigIntImmutable> constraintFactory =
                new SimpleFactory<BigIntImmutable>();
            Ring<BigIntImmutable> ring =
                new BigIntImmutableRing();
            CMonoid<GMonomial<GPolyVar>> monoid =
                new GMonomialMonoid<GPolyVar>();
            GPolyFlatRing<BigIntImmutable, GPolyVar> flatRing =
                new SimpleGPolyFlatRing<BigIntImmutable, GPolyVar>(ring, monoid);
            FlatteningVisitor<BigIntImmutable, GPolyVar> fvInner =
                new FlatteningVisitor<BigIntImmutable, GPolyVar>(flatRing);
            GPolyFactory<BigIntImmutable, GPolyVar> innerPolyFactory =
                new FullSharingFactory<BigIntImmutable, GPolyVar>();
            GPolyFlatRing<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> flatRing2 =
                new SimpleGPolyFlatRing<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>(innerPolyFactory, monoid);
            FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> fvOuter =
                new FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>(flatRing2);

            List<Citation> citations = new ArrayList<Citation>(1);
            citations.add(Citation.POLO);
            OPCRange<BigIntImmutable> range = new OPCRange<BigIntImmutable>(BigIntImmutable.MINUS_ONE, BigIntImmutable.TWO);

            IDPNonInfInterpretation interpretation =
                IDPNonInfInterpretation.create(
                        false, false, idp.getRuleAnalysis(), this.poloShapeHeuristic, outerPolyFactory, coeffFactory, constraintFactory,
                        fvInner, fvOuter, coeffOrder, citations, range, range.getList().get(0).y, aborter);

            if (this.poloShapeHeuristic.applies(interpretation)) {
                stratName = this.shapedStrat;
            } else {
                stratName = this.slowStrat;
            }
        } else {
            // only fast strategies
            stratName = this.fastStrat;
        }
        ExecutableStrategy strat = rti.getProgram().lookup(stratName).getExecutableStrategy(oblNode, rti);
        System.err.println("Selected " + stratName);
        return ResultFactory.justANewStrategy(strat);
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (obl instanceof IDPProblem) {
            return this.isIDPApplicable((IDPProblem) obl);
        }
        return false;
    }

    @Override
    public boolean isIDPApplicable(IDPProblem idp) {
        return true;
    }

    @Override
    protected Result processIDPProblem(IDPProblem idp, Abortion aborter)
            throws AbortionException {
        // TODO Auto-generated method stub
        return null;
    }

    public static class Arguments {

        public int outDegreeSwitch = 20;
        public IdpShapeHeuristic poloShapeHeuristic = new IdpCand1ShapeHeuristic(new IdpCand1ShapeHeuristic.Arguments());
        public String fastStrat = "idpNonInfIntFast";
        public String slowStrat = "idpNonInfIntSlow";
        public String shapedStrat = "idpNonInfIntShaped";
        public String natStrat = "idpNonInfNat";

    }



}
