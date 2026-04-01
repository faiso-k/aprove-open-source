package aprove.verification.complexity.CpxTrsProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * Tries to prove an upper bound for TRS derivational complexity
 * by using linear/quadratic restricted orders.
 */
public class CpxTrsDirectProcessor extends RuntimeComplexityTrsProcessor {

    private final int range;
    private final OPCSolver<BigIntImmutable> opcSolver;

    @ParamsViaArgumentObject
    public CpxTrsDirectProcessor(final Arguments arguments) {
        this.range = arguments.range;
        this.opcSolver = arguments.opcSolver;
    }

    @Override
    protected boolean isRuntimeComplexityTrsApplicable(final RuntimeComplexityTrsProblem obl) {
        return obl.getRewriteStrategy() == RewriteStrategy.INNERMOST
                || obl.getRewriteStrategy() == RewriteStrategy.PARALLEL_INNERMOST;
    }

    @Override
    protected Result processRuntimeComplexityTrs(final RuntimeComplexityTrsProblem cpxTrs, final Abortion aborter)
            throws AbortionException {
        GInterpretationMode<BigIntImmutable> iMode;
        GPoloNatSolver solver;
        ExportableOrder<TRSTerm> order;

        final Set<Rule> ruleset = new LinkedHashSet<Rule>(cpxTrs.getR());
        final ImmutableSet<FunctionSymbol> definedSymbols = cpxTrs.getDefinedSymbols();

        iMode = new GInterpretationModeRestricted<BigIntImmutable>(1, definedSymbols);
        solver = new GPoloNatSolver(iMode, this.range, StrictMode.ALLSTRICT, this.opcSolver);
        order = solver.solveDirect(ruleset, aborter);
        if (order != null) {
            return ResultFactory.provedWithValue(
                    ComplexityYNM.createUpper(ComplexityValue.linear()),
                new CpxTrsDirectProof(ruleset, order));
        }

        iMode = new GInterpretationModeRestricted<BigIntImmutable>(2, definedSymbols);
        solver = new GPoloNatSolver(iMode, this.range, StrictMode.ALLSTRICT, this.opcSolver);
        order = solver.solveDirect(ruleset, aborter);
        if (order != null) {
            return ResultFactory.provedWithValue(
                    ComplexityYNM.createUpper(ComplexityValue.quadratic()),
                new CpxTrsDirectProof(ruleset, order));
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    static class CpxTrsDirectProof extends CpxProof {

        private final Set<Rule> trs;
        private final ExportableOrder<TRSTerm> order;

        public CpxTrsDirectProof(final Set<Rule> trs, final ExportableOrder<TRSTerm> order) {
            this.trs = trs;
            this.order = order;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append(o.escape("Found linear/quadratic restricted ordering:"));
            sb.append(o.newline());
            sb.append(o.export(this.order));
            return sb.toString();
        }

        @Override
        public Element toCPF(
            final Document doc,
            final Element[] childrenProofs,
            final XMLMetaData xmlMetaData,
            final CPFModus modus)
        {
            return CPFTag.COMPLEXITY_PROOF.create(
                doc,
                CPFTag.RULE_SHIFTING.create(
                    doc,
                    this.order.toCPF(doc, xmlMetaData),
                    CPFTag.trs(doc, xmlMetaData, this.trs),
                    CPFTag.COMPLEXITY_PROOF.create(doc, CPFTag.R_IS_EMPTY.create(doc))));
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return true;
        }

    }

    public static class Arguments {
        public int range;
        public OPCSolver<BigIntImmutable> opcSolver;
    }
}
