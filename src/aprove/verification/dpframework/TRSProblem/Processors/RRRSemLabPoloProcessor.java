package aprove.verification.dpframework.TRSProblem.Processors;

import java.math.*;
import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.Processors.QDPSemanticPOLOLabellingProcessor.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BooleanSemanticLabelling.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;


/**
 * Semantic Labelling RRR processor for term rewrite systems.
 * Labels systems by tuples of bools, then applies monotonous POLO and removes the labelling.
 * @author Ulrich Schmidt-Goertz, Patrick Kabasci
 * @version $Id$
 *
 */
public class RRRSemLabPoloProcessor extends QTRSProcessor {

    private final BigInteger range;
    private final QUASI_MODE quasiState;
    private final int dimension;

    @ParamsViaArgumentObject
    public RRRSemLabPoloProcessor(final Arguments arguments) {
        this.dimension = arguments.dimension;
        this.range = BigInteger.valueOf(arguments.range);
        this.quasiState = arguments.quasi;
    }

    @Override
    public Result processQTRS(final QTRSProblem qtrs, final Abortion aborter, final RuntimeInformation rti) throws AbortionException {
        // First get the P signature of the QDP.
        final Set<Rule> R = qtrs.getR();


        final Set<FunctionSymbol> signature = new LinkedHashSet<FunctionSymbol>();
        final Set<TRSVariable> variables = new LinkedHashSet<TRSVariable>();


        for (final Rule r : R) {
            r.getLeft().collectFunctionSymbols(signature);
            if (r.getRight() instanceof TRSFunctionApplication) {
                ((TRSFunctionApplication) r.getRight()).collectFunctionSymbols(signature);
            }
            variables.addAll(r.getVariables());
        }
        final BSLAutoSearchTermInterpretor ti = new BSLAutoSearchTermInterpretor(this.quasiState);

        final FormulaFactory<Diophantine> ff = NonCountingCircuitFactory.create(SplitMode.FLATTEN, SplitMode.LEFT_COMB);
        ti.init(ff, this.dimension, signature, variables, true);


        for (final Rule r : R) {
            ti.interpretRule(r, true);
        }

        // Now get the monster into the SAT-solver
        final Formula<Diophantine> masterF = ti.getSATFormula();

        final PlainSPCToCircuitConverter spcc =
            PlainSPCToCircuitConverter.create(
                ff.<None>toTheory(),
                new DefaultValueMap<String, BigInteger>(this.range),
                this.range,
                new PoloSatConfigInfo());
        final MINISATEngine.Arguments args = new MINISATEngine.Arguments();
        args.version = 2;
        args.simp = true;
        final MINISATEngine mse = new MINISATEngine(args);
        final SatSearch eng = SatSearch.create(mse, spcc);
        final Map<String, BigInteger> goalState = eng.search(masterF, aborter, ti.interestingVars);

        if (goalState == null) {
            return ResultFactory.unsuccessful();
        }
        ti.result = goalState;
        ti.dump();

        final Set<Rule> newR = new LinkedHashSet<Rule>();
        final Set<Rule> delR = new LinkedHashSet<Rule>();
        final Iterator<Rule> iter = R.iterator();
        while (iter.hasNext()) {
            final Rule cur = iter.next();
            if (!ti.solves(cur)) {
                newR.add(cur);
            } else {
                delR.add(cur);
            }
        }


        final QTRSProblem newQTRS = qtrs.createSubProblem(ImmutableCreator.create(newR));

        // Now check for correctness.
        // First let's see whether we actually found a model.
        ti.checkModel(R);
        // Now check the polynomial interpretation.
        ti.checkPOLO(R, goalState, false);
        ti.checkPOLO(delR, goalState, true);

        ti.specialize(R, goalState);



        return ResultFactory.proved(newQTRS, YNMImplication.EQUIVALENT, new RRRSemanticLabellingPOLOProof(
            qtrs,
            newQTRS,
            ti,
            delR));

    }



    static final class RRRSemanticLabellingPOLOProof extends QTRSProof {

        BSLAutoSearchTermInterpretor ti;
        Set<Rule> deletedRRules, deletedSRules;
        private final QTRSProblem origTrs, resultTrs;

        RRRSemanticLabellingPOLOProof(
            final QTRSProblem origTrs,
            final QTRSProblem resultTrs,
            final BSLAutoSearchTermInterpretor ti,
            final Set<Rule> delR)
        {
            this.origTrs = origTrs;
            this.resultTrs = resultTrs;
            this.ti = ti;
            this.deletedRRules = delR;

        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            result.append("We use Semantic Labelling over tuples of bools combined with a polynomial order " + o.cite(Citation.SEMLAB));
            result.append(this.ti.getProof(o));
            result.append(o.linebreak());
            result.append("The following rules were deleted from R:");
            result.append(o.linebreak());
            result.append(o.set(this.deletedRRules, Export_Util.RULES));
            result.append(o.linebreak());


            return result.toString();
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            if (modus.isPositive()) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            } else {
                return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.resultTrs);
            }
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return !modus.isPositive();
        }

    }

    public static class Arguments {
        public int dimension = 1;
        public int range = 1;
        public QUASI_MODE quasi = QUASI_MODE.DISABLE;
    }



    @Override
    public boolean isQTRSApplicable(final QTRSProblem qtrs) {
        return true;
    }


}