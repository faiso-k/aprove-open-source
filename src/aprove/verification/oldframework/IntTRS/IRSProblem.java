package aprove.verification.oldframework.IntTRS;

import aprove.input.Programs.llvm.states.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IRSwT.*;
import aprove.verification.oldframework.IRSwT.Digraph.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

import java.util.*;

/**
 * An Integer Rewrite System is an IRSwT without terms, i.e., no constructor symbols are allowed.
 * @author Marc Brockschmidt, Matthias Hoelzel, Carsten Fuhs, cryingshadow
 */
public class IRSProblem extends IRSwTProblem implements VariableRenaming, FunctionSymbolAbstractStateMap, CombinedRulesMap {

    /**
     * The variable renaming carried out when creating this problem
     */
    private final CollectionMap<String, String> variableRenaming = new CollectionMap<>();
    
    /**
     * The corresponding map for the functionsymbols mapped to the abstract states
     */
    private final Map<FunctionSymbol, Node<LLVMAbstractState>> functionSymbolAbstractStateMap = new HashMap<>();

    /**
     * The corresponding map for the combined rules mapped to their pair of original rules
     */
    private final Map<IGeneralizedRule, Pair<IGeneralizedRule,IGeneralizedRule>> combinedRulesMap = new HashMap<>();

    /**
     * Whether the SEGraph to the current IRSProblem over-approximates
     */
    private boolean overapproximates = false;
    
    /**
     * @param rules the rules
     */
    public IRSProblem(final ImmutableSet<IGeneralizedRule> rules) {
        this(rules, null, null);
    }

    /**
     * @param rules the rules
     * @param start the start term
     */
    public IRSProblem(final ImmutableSet<IGeneralizedRule> rules, final TRSFunctionApplication start) {
        this(rules, null, start);
    }

    /**
     * @param rules   the rules
     * @param digraph the partially computed termination digraph (will be frozen).
     */
    public IRSProblem(
        final ImmutableSet<IGeneralizedRule> rules,
        final PartiallyComputedDigraph<IGeneralizedRule> digraph) {
        this(rules, digraph, null);
    }

    /**
     * @param rules the rules
     * @param start the start term
     */
    public IRSProblem(
        final ImmutableSet<IGeneralizedRule> rules,
        final PartiallyComputedDigraph<IGeneralizedRule> digraph,
        final TRSFunctionApplication start
    ) {
        super(rules, digraph, start, "IntTRS", "InTRS problem");
        assert super.isIRS() : "Invalid IRSProblem!";
    }

    /**
     * Copies a IRSwT, which is a IRS.
     *
     * @param irswt some IRSwT
     */
    public IRSProblem(final IRSwTProblem irswt) {
        this(irswt.getRules(), irswt.getTerminationDigraph(), irswt.getStartTerm());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "irs";
    }

    @Override
    public boolean isIRS() {
        return true;
    }

    public IRSProblem linearizeLeftSides() {
        final ImmutableSet<IGeneralizedRule> rules = this.getRules();
        final Set<IGeneralizedRule> newRules =
            IRSwTFormatTransformer.makeLhsLinear(rules, IDPPredefinedMap.DEFAULT_MAP);
        return new IRSProblem(ImmutableCreator.create(new LinkedHashSet<>(newRules)));
    }

    public Set<String> getUsedNames() {
        Set<String> res = new LinkedHashSet<>();
        for (IGeneralizedRule r : getRules()) {
            for (FunctionSymbol f : r.getFunctionSymbols()) {
                res.add(f.getName());
            }
            for (TRSVariable x : r.getVariables()) {
                res.add(x.getName());
            }
        }
        return res;
    }

    @Override
    public IRSLike create(Set<IGeneralizedRule> rules, TRSFunctionApplication startTerm) {
        return new IRSProblem(ImmutableCreator.create(rules), startTerm);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public CollectionMap<String, String> getVariableRenaming() {
        return variableRenaming;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void setVariableRenaming(CollectionMap<String, String> variableRenaming) {
        this.variableRenaming.putAll(variableRenaming);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Map<FunctionSymbol, Node<LLVMAbstractState>> getFunctionSymbolAbstractStateMap() {
        return this.functionSymbolAbstractStateMap;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void setFunctionSymbolAbstractStateMap(Map<FunctionSymbol, Node<LLVMAbstractState>> map) {
        this.functionSymbolAbstractStateMap.putAll(map);
    }

    @Override
    public Map<IGeneralizedRule, Pair<IGeneralizedRule, IGeneralizedRule>> getCombinedRulesMap() {
        return this.combinedRulesMap;
    }

    @Override
    public void setCombinedRulesMap(Map<IGeneralizedRule, Pair<IGeneralizedRule, IGeneralizedRule>> map) {
        this.combinedRulesMap.putAll(map);
    }

    
    public boolean getOverapproximates() {
        return overapproximates;
    }

    
    public void setOverapproximates(boolean overapproximates) {
        this.overapproximates = overapproximates;
    }
    
    
}