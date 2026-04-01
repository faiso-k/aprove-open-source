package aprove.verification.dpframework.IDPProblem;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * Integer TRS problem.
 *
 * TODO
 *
 * <p>
 * Note: If you want to create an ITRSProblem from a set of conditional rules,
 * have a look at the {@link IGeneralizedRule} class and its
 * {@link IGeneralizedRule#removeConditions(Collection)} method.
 * </p>
 *
 * @author noschinski
 *
 */
public final class ITRSProblem extends DefaultBasicObligation
    implements
        Immutable,
        HTML_Able,
        HasTRSTerms,
        ExternUsable,
        XMLObligationExportable
{

    public static ITRSProblem create(final ImmutableSet<GeneralizedRule> rules, final IDPPredefinedMap predefinedMap, final IQTermSet Q) {
        return new ITRSProblem(new RuleAnalysis<GeneralizedRule>(rules, predefinedMap), Q);
    }

    public static ITRSProblem create(final Collection<GeneralizedRule> rules, final IQTermSet Q) {
        final ImmutableSet<GeneralizedRule> rs = ImmutableCreator.create(new LinkedHashSet<GeneralizedRule>(rules));
        return ITRSProblem.create(rs, Q.getPreDefinedMap(), Q);
    }

    public static ITRSProblem create(final RuleAnalysis<GeneralizedRule> rules, final IQTermSet Q) {
        return new ITRSProblem(rules, Q);
    }


    /*
     * real values
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

    private ITRSProblem(final RuleAnalysis<GeneralizedRule> rules, final IQTermSet Q) {
        super("ITRS", "Integer TRS Problem");
        if (Globals.useAssertions) {
            assert(Q.getPreDefinedMap().equals(rules.getPreDefinedMap())) : "pre defined maps must be equal";
        }
        this.Q = Q;
        this.ruleAnalysis = rules;
        if (Globals.useAssertions) {
            final Set<FunctionSymbol> lhsSyms = CollectionUtils.getFunctionSymbols(rules.getLeftHandSides());
            final IDPPredefinedMap predefinedMap = rules.getPreDefinedMap();
            for (final FunctionSymbol f : lhsSyms) {
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
        final Set<TRSTerm> terms = new LinkedHashSet<TRSTerm>();
        for (final GeneralizedRule rule : this.getR()) {
            terms.addAll(rule.getTerms());
        }
        return terms;
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder s = new StringBuilder();
        s.append(o.export("ITRS problem:"));
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
        return new DefaultProofPurposeDescriptor(this, "Termination");
    }

    /**
     * @return true iff Q is a superset of the LHS of R
     */
    public boolean isNfQSubsetEqNfR() {
        return this.Q.canAllLhsBeRewritten(this.getR());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "itrs";
    }
}
