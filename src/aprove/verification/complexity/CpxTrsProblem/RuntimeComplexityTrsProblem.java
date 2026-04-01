/*
 * Created on 11.04.2005
 */
package aprove.verification.complexity.CpxTrsProblem;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
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
 * TRS problem for Runtime complexity analysis
 */
public final class RuntimeComplexityTrsProblem extends RuntimeComplexityRelTrsProblem {

    private RuntimeComplexityTrsProblem(
            final ImmutableSet<Rule> R,
            Set<FunctionSymbol> definedSymbols,
            final RewriteStrategy rewriteStrategy) {
        super("CpxTRS", "CpxTRS", R, ImmutableCreator.create(Collections.emptySet()), definedSymbols, rewriteStrategy, true);
    }

    public static RuntimeComplexityTrsProblem create(final ImmutableSet<Rule> R, final RewriteStrategy rewriteStrategy) {
        return new RuntimeComplexityTrsProblem(R, CollectionUtils.getRootSymbols(R), rewriteStrategy);
    }

    public static RuntimeComplexityTrsProblem createSub(final RuntimeComplexityTrsProblem p, final Set<Rule> retainedRules) {
        final LinkedHashSet<Rule> R = new LinkedHashSet<Rule>(p.getR());
        R.retainAll(retainedRules);
        return new RuntimeComplexityTrsProblem(
                ImmutableCreator.create(R),
                p.getDefinedSymbols(),
                p.getRewriteStrategy());
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
        return new ComplexityProofPurposeDescriptor(this,
                "Runtime Complexity (" + this.getRewriteStrategy().getRepresentation() + ')');
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        // possible refinement for separate strategies for innermost and parallel-innermost rewriting
        //return this.getRewriteStrategy().contractsMultipleRedexes() ? "parallelruntimecomplexity" : "runtimecomplexity";
        return "runtimecomplexity";
    }

    @Override
    public boolean offersCertifiableTechniques() {
        return this.getRewriteStrategy() == RewriteStrategy.INNERMOST;
    }

    @Override
    public boolean isDerivational() {
        return false;
    }

    @Override
    public Set<Rule> getRules() {
        return getR();
    }

}
