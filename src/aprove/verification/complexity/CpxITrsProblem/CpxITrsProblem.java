package aprove.verification.complexity.CpxITrsProblem;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * Runtime Complexity Integer TRS problem.
 *
 * Shameless copy of {@link aprove.verification.complexity.CpxTrsProblem.RuntimeComplexityTrsProblem}.
 */
public final class CpxITrsProblem extends DefaultBasicObligation implements Immutable, HTML_Able, HasTRSTerms, ExternUsable, XMLObligationExportable {

    public static CpxITrsProblem create(ImmutableSet<GeneralizedRule> rules, IDPPredefinedMap predefinedMap, IQTermSet Q) {
        return new CpxITrsProblem(new RuleAnalysis<GeneralizedRule>(rules, predefinedMap), Q);
    }

    public static CpxITrsProblem create(Collection<GeneralizedRule> rules, IQTermSet Q) {
        ImmutableSet<GeneralizedRule> rs = ImmutableCreator.create(new LinkedHashSet<GeneralizedRule>(rules));
        return CpxITrsProblem.create(rs, Q.getPreDefinedMap(), Q);
    }

    public static CpxITrsProblem create(RuleAnalysis<GeneralizedRule> rules, IQTermSet Q) {
        return new CpxITrsProblem(rules, Q);
    }


    /*
     * real valuesaprove.ProofTree.Export.Utility.HTML_Able
     */

    /**
     * RuleAnalysis<GeneralizedRule>
     */
    private final RuleAnalysis<GeneralizedRule> ruleAnalysis;

    /**
     * Q.
     */
    private final IQTermSet Q;


    /*
     * cached/computed values
     */

    private CpxITrsProblem(RuleAnalysis<GeneralizedRule> rules, IQTermSet Q) {
        super("CpxITrs", "Integer TRS Runtime Complexity Problem");
        if (Globals.useAssertions) {
            assert(Q.getPreDefinedMap().equals(rules.getPreDefinedMap())) : "pre defined maps must be equal";
        }
        this.Q = Q;
        this.ruleAnalysis = rules;
        if (Globals.useAssertions) {
            Set<FunctionSymbol> lhsSyms = CollectionUtils.getFunctionSymbols(rules.getLeftHandSides());
            IDPPredefinedMap predefinedMap = rules.getPreDefinedMap();
            for (FunctionSymbol f : lhsSyms) {
                assert ! predefinedMap.isPredefinedFunction(f);
            }
        }
    }


    public RuleAnalysis<GeneralizedRule> getRuleAnalysis() {
        return this.ruleAnalysis;
    }

    public ImmutableSet<GeneralizedRule> getR() {
        return this.ruleAnalysis.getRules();
    }

    public IQTermSet getQ() {
        return this.Q;
    }

    public IDPPredefinedMap getPredefinedMap() {
        return this.ruleAnalysis.getPreDefinedMap();
    }

    @Override
    public Set<? extends TRSTerm> getTerms() {
        Set<TRSTerm> terms = new LinkedHashSet<TRSTerm>();
        for (GeneralizedRule rule : this.getR()) {
            terms.addAll(rule.getTerms());
        }
        return terms;
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder s = new StringBuilder();
        s.append(o.export("Runtime Complexity ITRS problem:"));
        s.append(o.cond_linebreak());
        s.append(o.cond_linebreak());
        s.append("The following function symbols are pre-defined:");
        s.append(o.cond_linebreak());
        s.append(this.ruleAnalysis.getPreDefinedMap().export(o));
        s.append(o.cond_linebreak());
        if (this.getR().isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS R consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(IDPExport.exportRule(this.getR(), o, this.ruleAnalysis.getPreDefinedMap()));
            s.append(o.cond_linebreak());
        }

        if (this.Q.getExplicitTerms().isEmpty()) {
            s.append("The set Q is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The set Q consists of the following terms:"));
            s.append(o.cond_linebreak());
            s.append(IDPExport.exportTerm(this.Q.getExplicitTerms(), o, this.ruleAnalysis.getPreDefinedMap()));
            s.append(o.cond_linebreak());
        }

        return s.toString();
    }

    @Override
    public String externName() {
        return "itrs";
    }

    @Override
    public String toExternString() {
        return SaveProblemHelper.toAProVE_IDP(this.getR(), null, this.ruleAnalysis.getPreDefinedMap());
    }

    @Override
    public String toHTML() {
        return this.export(new HTML_Util());
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new ComplexityProofPurposeDescriptor(this,
                "Innermost Runtime Complexity");
    }

    /**
     * @return true iff Q is a superset of the LHS of R
     */
    public boolean isNfQSubsetEqNfR() {
        return this.Q.canAllLhsBeRewritten(this.getR());
    }

    @Override
    public String getStrategyName() {
        return "cpxITrs";
    }
}
