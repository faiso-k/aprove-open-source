package aprove.verification.oldframework.IntTRS.BoundedInts;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Represents a intTRS, that maybe uses some cast symbols (like
 * cast_32_unsigned).
 * @author Matthias Hoelzel
 */
public class BoundedIntTRSProblem extends IRSwTProblem {
    /** Some bound information! */
    private final BoundInformation boundInfo;

    /**
     * Constructs your new bounded intTRS.
     * @param rules set of rules
     * @param bi some bound information
     */
    public BoundedIntTRSProblem(final ImmutableSet<IGeneralizedRule> rules, final BoundInformation bi) {
        super(rules);
        // Power line for the win!
        this.boundInfo =
            (bi == null)
                ? (new BoundInformation(
                    ImmutableCreator.create(new LinkedHashMap<IGeneralizedRule, ImmutableLinkedHashMap<TRSVariable, IntegerType>>(
                        0)))) : bi;
    }

    /** @return true, if this uses some cast symbols. */
    @Override
    public boolean isBounded() {
        for (final IGeneralizedRule rule : this.getRules()) {
            if (BoundedSymbolFactory.containsCastSymbol(rule.getLeft())
                || BoundedSymbolFactory.containsCastSymbol(rule.getRight())
                || (rule.getCondTerm() != null && BoundedSymbolFactory.containsCastSymbol(rule.getCondTerm()))) {
                return true;
            }
        }
        return false;
    }

    /**
     * Returns the bound information.
     * @return BoundInformation
     */
    public BoundInformation getBoundInformation() {
        return this.boundInfo;
    }

    /**
     * Renames the variables & returns a renamed version of this. This object
     * itself is not touched.
     * @param substitution mapping of variables to variables
     * @return BoundedIntTRS
     */
    public BoundedIntTRSProblem renameVariables(final Map<TRSVariable, TRSVariable> substitution) {
        final ImmutableSet<IGeneralizedRule> oldRules = this.getRules();
        final LinkedHashSet<IGeneralizedRule> newRules = new LinkedHashSet<>(oldRules.size());
        final LinkedHashMap<IGeneralizedRule, IGeneralizedRule> ruleReplacement = new LinkedHashMap<>(oldRules.size());
        for (final IGeneralizedRule rule : oldRules) {
            final ImmutableMap<TRSVariable, TRSVariable> immuMap = ImmutableCreator.create(substitution);
            final TRSFunctionApplication newLeft = rule.getLeft().applySubstitution(TRSSubstitution.create(immuMap));
            final TRSTerm newRight = rule.getRight().applySubstitution(TRSSubstitution.create(immuMap));
            final TRSTerm newCond = rule.getCondTerm().applySubstitution(TRSSubstitution.create(immuMap));

            final IGeneralizedRule newRule = IGeneralizedRule.create(newLeft, newRight, newCond);
            newRules.add(newRule);
            ruleReplacement.put(rule, newRule);
        }

        final BoundInformation newBoundInformation =
            this.getBoundInformation().renameVariables(substitution, ruleReplacement);

        return new BoundedIntTRSProblem(ImmutableCreator.create(newRules), newBoundInformation);
    }

    /**
     * Renames the variables & returns a renamed version of this. This object
     * itself is not touched.
     * @param ng some name generator
     * @return BoundedIntTRS
     */
    public BoundedIntTRSProblem renameVariables(final FreshNameGenerator ng) {
        final LinkedHashMap<TRSVariable, TRSVariable> newNames = new LinkedHashMap<>();
        for (final IGeneralizedRule rule : this.getRules()) {
            for (final TRSVariable v : rule.getVariables()) {
                if (!newNames.containsKey(v)) {
                    newNames.put(v, TRSTerm.createVariable(ng.getFreshName("x", false)));
                }
            }
            for (final TRSVariable v : rule.getCondVariables()) {
                if (!newNames.containsKey(v)) {
                    newNames.put(v, TRSTerm.createVariable(ng.getFreshName("x", false)));
                }
            }
        }

        return this.renameVariables(newNames);
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        sb.append("BoundedIntTRS:\n");
        int counter = this.getRules().size();
        for (final IGeneralizedRule rule : this.getRules()) {
            sb.append(rule.toString());
            if (this.boundInfo != null) {
                String boundInfoString = null;
                final ImmutableLinkedHashMap<TRSVariable, IntegerType> domainInfo =
                    this.boundInfo.getBoundInformationMap().get(rule);
                final Set<TRSVariable> variables = rule.getVariables();
                variables.addAll(rule.getCondVariables());
                for (final TRSVariable v : variables) {
                    final IntegerType bd = domainInfo.get(v);
                    if (bd != null) {
                        if (boundInfoString == null) {
                            boundInfoString = "\n\t";
                        } else {
                            boundInfoString += ", ";
                        }
                        boundInfoString += v.toString() + " is " + bd.toString();
                    }
                }
                if (boundInfoString != null) {
                    sb.append(boundInfoString);
                    sb.append('\n');
                }
            }
            counter--;
            if (counter != 0) {
                sb.append('\n');
            }
        }
        return sb.toString();
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder res = new StringBuilder();
        res.append("Rules:").append(o.linebreak());

        for (final IGeneralizedRule r : this.getRules()) {
            res.append(r.export(o)).append(o.linebreak());
            if (this.boundInfo != null) {
                final Map<TRSVariable, IntegerType> infoMap = this.boundInfo.getBoundInformationMap().get(r);
                if (infoMap == null) {
                    continue;
                }
                final StringBuilder boundInfoStringBuilder = new StringBuilder();
                boolean empty = true;
                final Set<TRSVariable> variables = r.getCondVariables();
                variables.addAll(r.getVariables());
                for (final TRSVariable v : variables) {
                    final IntegerType bd = infoMap.get(v);
                    if (bd == null) {
                        continue;
                    }
                    if (empty) {
                        empty = false;
                    } else {
                        boundInfoStringBuilder.append(o.tttext(", "));
                    }
                    boundInfoStringBuilder.append(v.export(o)).append(o.tttext(" is ")).append(o.tttext(bd.toString()));
                }
                if (!empty) {
                    res.append(o.indent(boundInfoStringBuilder.toString())).append(o.linebreak());
                }
            }
        }

        return res.toString();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + ((this.boundInfo == null) ? 0 : this.boundInfo.hashCode());
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (!super.equals(obj)) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final BoundedIntTRSProblem other = (BoundedIntTRSProblem) obj;
        if (this.boundInfo == null) {
            if (other.boundInfo != null) {
                return false;
            }
        } else if (!this.boundInfo.equals(other.boundInfo)) {
            return false;
        }
        return true;
    }
}
