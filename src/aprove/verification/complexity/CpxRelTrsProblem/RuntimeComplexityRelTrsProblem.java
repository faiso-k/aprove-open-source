package aprove.verification.complexity.CpxRelTrsProblem;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.complexity.TruthValue.ComplexityYNM.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * Docu-guess (fuhs):
 * A variation of the relative TRS theme for runtime complexity analysis.
 * For two TRSs R and S, the idea is not to count steps via rules which
 * are contained in S. So in standard relative rewriting, we would
 * probably be looking at "(R \ S) relative to S".
 *
 * If we were to assign costs to each rule application, these would be as follows:
 *
 * - Using a rule in S costs 0.
 * - Using a rule in R \setminus S costs 1.
 *
 * (As usual, we consider equality of rules modulo variable renamings.)
 *
 * In contrast, for "standard" relative rewriting (count steps via
 * ->_S^* \circ ->_R \circ ->_S^*, see e.g. the RTA'10 paper "Modular Complexity
 * Analysis via Relative Complexity" by H. Zankl and M. Korp) the costs would be
 * as follows (note that this is /not/ what the present class does!):
 *
 * - Using a rule in S \setminus R costs 0.
 * - Using a rule in R \setminus S costs 1.
 * - Using a rule in R \cap S costs 0 or 1. (!)
 *   For analysis of runtime complexity, which is about the /maximum/ cost of
 *   a rewrite sequence using rules from R and S, one could here equivalently
 *   assume cost 1 for rules in R \cap S (that gives a higher overall cost).
 *
 * The deviation from the standard semantics of relative rewriting thus only
 * makes a difference for instances where R \cap S != \emptyset.
 *
 * As an example for the difference, consider R = S = { f(s(x)) -> f(x) }.
 * In our semantics we have runtime complexity O(1) (all steps have 0 cost),
 * in standard semantics we have runtime complexity \theta(n) (all steps
 * have cost 1).
 */
public class RuntimeComplexityRelTrsProblem extends CpxRelTrsProblem {

    protected RuntimeComplexityRelTrsProblem(String shortname,
            String longname,
            ImmutableSet<Rule> R,
            ImmutableSet<Rule> S,
            Set<FunctionSymbol> definedSymbols,
            RewriteStrategy rewriteStrategy,
            boolean STerminatesInnermost) {
        super(shortname, longname, R, S, definedSymbols, rewriteStrategy, STerminatesInnermost);
    }

    private RuntimeComplexityRelTrsProblem(final ImmutableSet<Rule> R, final ImmutableSet<Rule> S, final RewriteStrategy rewriteStrategy, boolean STerminatesInnermost) {
        super("CpxRelTRS", "CpxRelTRS", R, S, rewriteStrategy, STerminatesInnermost);
    }

    public static RuntimeComplexityRelTrsProblem create(final ImmutableSet<Rule> R,
        final ImmutableSet<Rule> S,
        final RewriteStrategy rewriteStrategy,
        boolean STerminatesInnermost) {
        if (S.isEmpty()) {
            return RuntimeComplexityTrsProblem.create(R, rewriteStrategy);
        } else {
            return new RuntimeComplexityRelTrsProblem(R, S, rewriteStrategy, STerminatesInnermost);
        }
    }

    @Override
    public Element getCPFInput(final Document doc, final XMLMetaData xmlMetaData, final TruthValue tv) {
        final Element trs = CPFTag.TRS_INPUT.create(doc, CPFTag.trs(doc, xmlMetaData, this.getR()));
        if (this.getRewriteStrategy() == RewriteStrategy.INNERMOST) {
            trs.appendChild(CPFTag.STRATEGY.create(doc, CPFTag.INNERMOST.create(doc)));
        }
        else if (this.getRewriteStrategy() == RewriteStrategy.PARALLEL_INNERMOST) {
            trs.appendChild(CPFTag.STRATEGY.create(doc, CPFTag.PARALLEL_INNERMOST.create(doc)));
        }
        if (!this.S.isEmpty()) {
            trs.appendChild(CPFTag.RELATIVE_RULES.create(doc, CPFTag.rules(doc, xmlMetaData, this.S)));
        }
        final Set<FunctionSymbol> defined = this.getDefinedSymbols();
        final Set<FunctionSymbol> constructors = new LinkedHashSet<>(this.getSignature());
        constructors.removeAll(defined);
        final Element cm =
            CPFTag.RUNTIME_COMPLEXITY.create(
                doc,
                FunctionSymbol.cpfSignature(doc, xmlMetaData, constructors),
                FunctionSymbol.cpfSignature(doc, xmlMetaData, defined));
        int deg;
        try {
            deg = ComplexityYNM.degreeOfUpperBound(tv);
        } catch (NoPolynomialUpperBoundException e) {
            return CPFTag.UNKNOWN_PROOF.create(doc);
        }
        final Element cpx = CPFTag.POLYNOMIAL.create(doc, deg);
        final Element cpxInput = CPFTag.COMPLEXITY_INPUT.create(doc, trs, cm, cpx);
        return cpxInput;
    }

    @Override
    public Element getCPFAssumption(
        final Document doc,
        final XMLMetaData xmlMetaData,
        final CPFModus modus,
        final TruthValue tv)
    {

        return CPFTag.COMPLEXITY_PROOF.create(
            doc,
            CPFTag.COMPLEXITY_ASSUMPTION.create(doc, this.getCPFInput(doc, xmlMetaData, tv)));
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new ComplexityProofPurposeDescriptor(this, "Runtime Complexity ("
            + this.getRewriteStrategy().getRepresentation() + ')');
    }

    @Override
    public String getStrategyName() {
        // possible refinement for separate strategies for innermost and parallel-innermost rewriting
        //return this.getRewriteStrategy().contractsMultipleRedexes() ? "cpxparreltrs" : "cpxreltrs";
        return "cpxreltrs";
    }

    @Override
    public boolean isDerivational() {
        return false;
    }

    @Override
    public BasicObligation withRules(Set<Rule> R, Set<Rule> S) {
        return create(ImmutableCreator.create(R), ImmutableCreator.create(S), this.getRewriteStrategy(), STerminatesInnermost());
    }

    @Override
    public BasicObligation provedTerminationOfS() {
        return create(ImmutableCreator.create(R), ImmutableCreator.create(S), this.getRewriteStrategy(), true);
    }
}
