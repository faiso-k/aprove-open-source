package aprove.verification.complexity.CpxIntTrsProblem.Processors;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.IndefiniteCIPI.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class CpxIntTrsRedPairProcessor extends CpxIntTrsProcessor {

    private static class CIPIProof extends Proof.DefaultProof {

        private final CIPI cipi;
        private final Set<CpxIntTupleRule> removedTuples;
        private final CpxIntTrsProblem obl;
        private final Arguments args;

        public CIPIProof(
            final Set<CpxIntTupleRule> removedTuples,
            final CpxIntTrsProblem obl,
            final CIPI cipi,
            Arguments args)
        {
            this.obl = obl;
            this.removedTuples = removedTuples;
            this.cipi = cipi;
            this.args = args;
            if (this.args.useSizeBounds) {
                this.setShortName("CIPISizeBoundsProof");
                this.setLongName("CIPISizeBoundsProof");
            }
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();

            sb.append("Using a Complexity Integer Polynomial Interpretation, "
                + "the following complexity tuples could  be removed:");
            sb.append(o.cond_linebreak());
            sb.append(o.set(this.removedTuples, Export_Util.RULES));
            sb.append(o.cond_linebreak());
            sb.append(o.export(this.cipi));

            if (this.args.useSizeBounds) {
                sb.append(o.cond_linebreak());
                sb
                    .append("Rules marked as known were not oriented, but their size estimated as depicted in the graph.");
            }

            sb.append(o.cond_linebreak());
            sb.append("Information about each rule (for debugging):" + o.cond_linebreak());
            for (CpxIntTupleRule rule : this.obl.getK().keySet()) {
                sb.append(rule.export(o));
                if (this.removedTuples.contains(rule)) {
                    sb.append(o.bold(" (strict)"));
                }
                sb.append(o.cond_linebreak());
                RationalPolynomial Ilhs = this.cipi.interpretTerm(rule.getLeft());
                sb.append("lhs: " + Ilhs.export(o) + o.linebreak());
                sb.append("rhss:" + o.linebreak());
                for (TRSFunctionApplication rhs : rule.getRights()) {
                    RationalPolynomial Irhs = this.cipi.interpretTerm(rhs);
                    sb.append(Irhs.export(o) + o.linebreak());
                }
            }

            return sb.toString();
        }

    }

    public static final SMTEngine SMT_ENGINE = new YicesEngine();

    public static class Arguments {
        /**
         * The shape of indefinite polynomials used for defined symbols.
         */
        public IndefiniteCIPI.ShapeTemplates shape = ShapeTemplates.ShapeLinear;
        /**
         * If all rules have to be oriented strictly at once. Probably only
         * useful for experiments.
         */
        public boolean allStrict = false;
        /**
         * TODO name this technique properly :)
         */
        public boolean useSizeBounds = false;

        /**
         * Choose R', such that no argument positions must be filtered.
         */
        public boolean forceAllArgumentsAllowed;
    }

    private final Arguments args;

    @ParamsViaArgumentObject
    public CpxIntTrsRedPairProcessor(final Arguments args) {
        this.args = args;
    }

    @Override
    public Result processCpxIntTrs(
        final CpxIntTrsProblem obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        FormulaFactory<SMTLIBTheoryAtom> factory = new FullSharingFactory<>();
        Triple<CIPI,ImmutableSet<CpxIntTupleRule>,ImmutableSet<CpxIntTupleRule>> result;
        LinkedHashMap<CallArgument, ComplexityValue> bounds = new LinkedHashMap<>();
        if (this.args.useSizeBounds) {
            for (Entry<CallArgument, LocalComplexityValue> e : obl.getSizeBounds(aborter).entrySet()) {
                bounds.put(e.getKey(), e.getValue().getComplexityValue());
            }
        }
        try {
            result = IndefiniteCIPI.findCIPI(obl, bounds, factory, this.args, aborter);
        } catch (SplitHeuristicNotApplicableException e) {
            return ResultFactory.unsuccessful("SplitHeuristic not applicable.");
        }

        if (result == null) {
            return ResultFactory.unsuccessful("Could not find CIPI");
        }


        CIPI cipi = result.x;
        ImmutableSet<CpxIntTupleRule> strictTuples = result.y;
        ImmutableSet<CpxIntTupleRule> weakTuples = result.z;

        LinkedHashMap<CpxIntTupleRule, ComplexityValue> updatedTuples = new LinkedHashMap<>();
        if (this.args.useSizeBounds) {
            updatedTuples = cipi.buildTupleUpdateMapUsingSizeBounds(obl, bounds, strictTuples, weakTuples);
        } else {
            updatedTuples = cipi.buildTupleUpdateMap(obl, strictTuples);
        }

        ComplexityValue upperBound = ComplexityValue.constant();
        for (Entry<CpxIntTupleRule, ComplexityValue> e : updatedTuples.entrySet()) {
            upperBound = upperBound.max(e.getValue());
        }

        CpxIntTrsProblem newobl = obl.updateKValues(updatedTuples);

        return ResultFactory.proved(newobl, UpperBound.create(new SumComputation(upperBound)), new CIPIProof(
            strictTuples,
            obl,
            cipi,
            this.args));
    }

    @Override
    boolean isCpxIntTrsApplicable(final CpxIntTrsProblem obl) {
        return true;
    }

}
