package aprove.verification.dpframework.TRSProblem.Utility;

import java.io.*;
import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.*;
import aprove.verification.dpframework.TRSProblem.Utility.NodeEntry.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * this non-static class provides useful methods to build an OutermostTerminationGraph
 *
 * @author Sebastian Weise
 */

public class OTRSTermGraphUtils implements Immutable {

    /*
     * the Rules of the underlying OTRSProblem;
     * standard-renumbered with prefix OutermostTerminationGraph.ALLQ_VAR_PREFIX and
     *      with indices counted from Term.STANDARD_NUMBER
     */
    private final ImmutableSet<Rule> rulesAllq;
    private final ImmutableSet<FunctionSymbol> functionSymbols;
    private final ImmutableSet<FunctionSymbol> definedSymbols;
    private final ImmutableSet<FunctionSymbol> constructors;
    private final ImmutableSet<FunctionSymbol> constructorsArityZero;
    private final ImmutableSet<FunctionSymbol> functionSymbolsMinusConstructorsArityZero;
    private final ImmutableSet<FunctionSymbol> constructorsArityNonZero;
    // see the equally named Parameter of the Constructor of class OutermostTerminationGraph.java!
    private final boolean useExclusionSubstitutions;
    // here, our Debug-Outputs will be stored
    private final String pathForDebugOutputs;

    public OTRSTermGraphUtils(final ImmutableSet<Rule> rules,
            final boolean useExclusionSubstitutions,
            final String pathForDebugOutputs) {

        final Set<Rule> rulesAllqTemp = new LinkedHashSet<Rule>();
        final Set<FunctionSymbol> functionSymbolsTemp =
            new LinkedHashSet<FunctionSymbol>();
        final Set<FunctionSymbol> definedSymbolsTemp =
            new LinkedHashSet<FunctionSymbol>();

        for (final Rule actRule : rules) {
            rulesAllqTemp.add(actRule.getWithRenumberedVariables(OutermostTerminationGraph.ALLQ_VAR_PREFIX));
            functionSymbolsTemp.addAll(actRule.getFunctionSymbols());
            definedSymbolsTemp.add(actRule.getRootSymbol());
        }

        final Set<FunctionSymbol> constructorsTemp =
            new LinkedHashSet<FunctionSymbol>(functionSymbolsTemp);
        constructorsTemp.removeAll(definedSymbolsTemp);

        final Set<FunctionSymbol> constructorsArityZeroTemp =
            new LinkedHashSet<FunctionSymbol>();
        for (final FunctionSymbol actConstr : constructorsTemp) {
            if (actConstr.getArity() == 0) {
                constructorsArityZeroTemp.add(actConstr);
            }
        }

        final Set<FunctionSymbol> functionSymbolsMinusConstructorsArityZeroTemp =
            new LinkedHashSet<FunctionSymbol>(functionSymbolsTemp);
        functionSymbolsMinusConstructorsArityZeroTemp.removeAll(constructorsArityZeroTemp);

        final Set<FunctionSymbol> constructorsArityNonZeroTemp =
            new LinkedHashSet<FunctionSymbol>(constructorsTemp);
        constructorsArityNonZeroTemp.removeAll(constructorsArityZeroTemp);

        this.rulesAllq = ImmutableCreator.create(rulesAllqTemp);
        this.functionSymbols = ImmutableCreator.create(functionSymbolsTemp);
        this.definedSymbols = ImmutableCreator.create(definedSymbolsTemp);
        this.constructors = ImmutableCreator.create(constructorsTemp);
        this.constructorsArityZero =
            ImmutableCreator.create(constructorsArityZeroTemp);
        this.functionSymbolsMinusConstructorsArityZero =
            ImmutableCreator.create(functionSymbolsMinusConstructorsArityZeroTemp);
        this.constructorsArityNonZero =
            ImmutableCreator.create(constructorsArityNonZeroTemp);

        this.useExclusionSubstitutions = useExclusionSubstitutions;
        this.pathForDebugOutputs = pathForDebugOutputs;
    }

    public ImmutableSet<Rule> getRulesAllq() {
        return this.rulesAllq;
    }

    public ImmutableSet<FunctionSymbol> getFunctionSymbols() {
        return this.functionSymbols;
    }

    public ImmutableSet<FunctionSymbol> getDefinedSymbols() {
        return this.definedSymbols;
    }

    public ImmutableSet<FunctionSymbol> getConstructors() {
        return this.constructors;
    }

    public ImmutableSet<FunctionSymbol> getConstructorsArityZero() {
        return this.constructorsArityZero;
    }

    public ImmutableSet<FunctionSymbol> getFunctionSymbolsMinusConstructorsArityZero() {
        return this.functionSymbolsMinusConstructorsArityZero;
    }

    public ImmutableSet<FunctionSymbol> getConstructorsArityNonZero() {
        return this.constructorsArityNonZero;
    }

    public boolean getUseExclusionSubstitutions() {
        return this.useExclusionSubstitutions;
    }

    /**************************************************************************/
    /**************************************************************************/

    public Set<Position> getPositions(final TRSVariable v, final TRSTerm t) {
        return new LinkedHashSet<Position>(t.getVariablePositions().get(v));
    }

    public Set<Position> getVariablePositions(final TRSTerm t) {
        final LinkedHashSet<Position> result = new LinkedHashSet<Position>();
        for (final List<Position> actVarPositions : t.getVariablePositions().values()) {
            result.addAll(actVarPositions);
        }
        return result;
    }

    public Set<Position> getNonVariablePositions(final TRSTerm t) {
        final LinkedHashSet<Position> result = new LinkedHashSet<Position>();
        for (final Pair<Position, TRSFunctionApplication> actPosFapp : t.getNonRootNonVariablePositionsWithSubTerms()) {
            result.add(actPosFapp.x);
        }
        if (t instanceof TRSFunctionApplication) {
            result.add(Position.create());
        }
        return result;
    }

    /**
     * @param pos must be a valid Position of "t"!
     */
    public boolean isRewritable(final TRSTerm t,
        final Position pos,
        final Rule rule) {
        return rule.getLeft().getMatcher(t.getSubterm(pos)) != null;
    }

    /**
     * @param pos must be a valid Position of "t"!
     */
    public boolean isRewritable(final TRSTerm t, final Position pos) {
        for (final Rule actRule : this.rulesAllq) {
            if (this.isRewritable(t, pos, actRule)) {
                return true;
            }
        }
        return false;
    }

    /**
     * @param subst must be a Variable-Renaming !!
     * @return {varRenaming(x) | x in vars}
     */
    public Set<TRSVariable> applyVariableRenaming(final Set<TRSVariable> vars,
        final TRSSubstitution varRenaming) {
        final Set<TRSVariable> result = new LinkedHashSet<TRSVariable>();
        for (final TRSVariable actVar : vars) {
            result.add((TRSVariable) varRenaming.substitute(actVar));
        }
        return result;
    }

    /**
     * checks whether we have "from superset domain(subst)" and "to = subst(from)" and
     *      whether "subst: from -> to" is a Variable-Renaming where
     *          we suppose a Variable-Renaming to be BIJECTIVE
     */
    public boolean isVariableRenaming(final TRSSubstitution subst,
        final Set<TRSVariable> from,
        final Set<TRSVariable> to) {
        if (!(subst.getDomain().size() == subst.getCodomain().size())) {
            return false;
        }
        if (!(from.containsAll(subst.getDomain()))) {
            return false;
        }
        if (!to.containsAll(subst.getCodomain())) {
            return false;
        }
        final Set<TRSVariable> fromMinusDomain = new LinkedHashSet<TRSVariable>(from);
        fromMinusDomain.removeAll(subst.getDomain());
        final Set<TRSVariable> toMinusCodomain = new LinkedHashSet<TRSVariable>(to);
        toMinusCodomain.removeAll(subst.getCodomain());
        return fromMinusDomain.equals(toMinusCodomain);
    }

    /**
     * @param varRenaming must be a Variable-Renaming!
     */
    public TRSSubstitution applyToDomainAndCodomain(final TRSSubstitution origin,
        final TRSSubstitution varRenaming) {
        final Map<TRSVariable, TRSTerm> newMap = new LinkedHashMap<TRSVariable, TRSTerm>();
        for (final Map.Entry<TRSVariable, ? extends TRSTerm> actEntry : origin.toMap().entrySet()) {
            newMap.put((TRSVariable) varRenaming.substitute(actEntry.getKey()),
                actEntry.getValue().applySubstitution(varRenaming));
        }
        return TRSSubstitution.create(ImmutableCreator.create(newMap));
    }

    public int complexity(final TRSTerm term) {
        int result = 1;
        if (term instanceof TRSFunctionApplication) {
            for (final TRSTerm actArg : ((TRSFunctionApplication) term).getArguments()) {
                result += this.complexity(actArg);
            }
        }
        return result;
    }

    /**
     * looksup a tuple symbol for a defined symbol f;
     * if it is not defined, a new symbol is created (which is not contained in allSyms),
     *      the mapping is stored and the new symbol is added to allSyms;
     *
     * this method has been taken from QTRSProblem.java
     */
    public FunctionSymbol getTupleSymbol(final FunctionSymbol f,
        final Map<FunctionSymbol, FunctionSymbol> defToTup,
        final Set<FunctionSymbol> allSyms) {
        FunctionSymbol tf = defToTup.get(f);
        if (tf == null) {
            final String wishedName = f.getName().toUpperCase();
            final int arity = f.getArity();
            int nr = 1;
            tf = FunctionSymbol.create(wishedName, arity);
            while (!allSyms.add(tf)) {
                tf = FunctionSymbol.create(wishedName + "^" + nr, arity);
                nr++;
            }
            defToTup.put(f, tf);
        }
        return tf;
    }

    public boolean isConstructorSystem() {
        for (final Rule actRule : this.rulesAllq) {
            for (final TRSTerm actArg : actRule.getLeft().getArguments()) {
                if (!this.constructors.containsAll(actArg.getFunctionSymbols())) {
                    return false;
                }
            }
        }
        return true;
    }

    /**************************************************************************/

    public TRSVariable getFreshMetaVariable(final MyInteger toUseNext) {
        final TRSVariable result =
            TRSTerm.createVariable(OutermostTerminationGraph.META_VAR_PREFIX
                + Integer.toString(toUseNext.getIntValue()));
        toUseNext.increase();
        return result;
    }

    public TRSVariable getAllqVariable(final int index) {
        return TRSTerm.createVariable(OutermostTerminationGraph.ALLQ_VAR_PREFIX
            + Integer.toString(index));
    }

    public boolean isMetaVariable(final Object o) {
        if (o instanceof TRSVariable) {
            final TRSVariable oVar = (TRSVariable) o;
            return oVar.getName().startsWith(
                OutermostTerminationGraph.META_VAR_PREFIX);
        }
        return false;
    }

    public boolean isAllqVariable(final Object o) {
        if (o instanceof TRSVariable) {
            final TRSVariable oVar = (TRSVariable) o;
            return oVar.getName().startsWith(
                OutermostTerminationGraph.ALLQ_VAR_PREFIX);
        }
        return false;
    }

    /**
     * @return a new set which contains all Metavariables from "set"
     */
    public Set<TRSVariable> getMetaVariables(final Set<TRSVariable> set) {
        final Set<TRSVariable> result = new LinkedHashSet<TRSVariable>();
        for (final TRSVariable actVar : set) {
            if (this.isMetaVariable(actVar)) {
                result.add(actVar);
            }
        }
        return result;
    }

    /**
     * @return a new set which contains all allquantified Variables from "set"
     */
    public Set<TRSVariable> getAllqVariables(final Set<TRSVariable> set) {
        final Set<TRSVariable> result = new LinkedHashSet<TRSVariable>();
        for (final TRSVariable actVar : set) {
            if (this.isAllqVariable(actVar)) {
                result.add(actVar);
            }
        }
        return result;
    }

    /**
     * @return f(x0, ..., xn) where x0, ..., xn are fresh and pairwise disjunct Metavariables
     */
    public TRSTerm getPatternTermWithFreshMetaVariables(final FunctionSymbol f,
        final MyInteger toUseNext) {
        final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(f.getArity());
        for (int i = 1; i <= f.getArity(); i++) {
            args.add(this.getFreshMetaVariable(toUseNext));
        }
        return TRSTerm.createFunctionApplication(f, ImmutableCreator.create(args));
    }

    /**
     * restricts a Substitution to Metavariables
     */
    public TRSSubstitution restrictToVmeta(final TRSSubstitution subst) {
        final Map<TRSVariable, TRSTerm> newMap = new LinkedHashMap<TRSVariable, TRSTerm>();
        for (final Map.Entry<TRSVariable, ? extends TRSTerm> actEntry : subst.toMap().entrySet()) {
            if (this.isMetaVariable(actEntry.getKey())) {
                newMap.put(actEntry.getKey(), actEntry.getValue());
            }
        }
        return TRSSubstitution.create(ImmutableCreator.create(newMap));
    }

    public Rule getWithFreshMetaVariables(final Rule rule,
        final MyInteger toUseNext) {
        return this.getWithFreshMetaVariables(null, rule, toUseNext).y;
    }

    /**
     * replace all allquantified Variables of a Substitution by
     *      fresh and pairwise disjunkt Metavariables
     *          (equal allquantified Variables replaced by equal fresh Metavariables);
     */
    public TRSSubstitution getWithFreshMetaVariables(final TRSSubstitution subst,
        final MyInteger toUseNext) {
        return this.getWithFreshMetaVariables(subst, null, toUseNext).x;
    }

    /**
     * replace all allquantified Variables of a Substitution and a Rule by
     *      fresh and pairwise disjunkt Metavariables
     *          (equal allquantified Variables replaced by equal fresh Metavariables);
     * allquantified Variables occuring in the Substitution AND in the Rule will
     *      be replaced the same way;
     * the Substitution and/or the Rule might be null;
     *      then the corresponding "renamed" result is also null;
     * if both are null, then the pair "(null, null)" is returned
     */
    public Pair<TRSSubstitution, Rule> getWithFreshMetaVariables(final TRSSubstitution subst,
        final Rule rule,
        final MyInteger toUseNext) {
        final Set<TRSVariable> allqVars = new LinkedHashSet<TRSVariable>();
        if (subst != null) {
            allqVars.addAll(this.getAllqVariables(subst.getVariables()));
        }
        if (rule != null) {
            allqVars.addAll(this.getAllqVariables(rule.getVariables()));
        }
        final Map<TRSVariable, TRSVariable> map =
            new LinkedHashMap<TRSVariable, TRSVariable>();
        for (final TRSVariable actAllqVar : allqVars) {
            map.put(actAllqVar, this.getFreshMetaVariable(toUseNext));
        }
        final TRSSubstitution varRenaming =
            TRSSubstitution.create(ImmutableCreator.create(map));
        TRSSubstitution substRenamed = null;
        Rule ruleRenamed = null;
        if (subst != null) {
            substRenamed = this.applyToDomainAndCodomain(subst, varRenaming);
        }
        if (rule != null) {
            ruleRenamed = rule.applySubstitution(varRenaming);
        }
        return new Pair<TRSSubstitution, Rule>(substRenamed, ruleRenamed);
    }

    public TRSTerm linearize(final TRSTerm t,
        Set<Position> positions,
        final MyInteger toUseNext) {
        positions = new LinkedHashSet<Position>(positions);
        positions.retainAll(this.getVariablePositions(t));
        TRSTerm result = t;
        for (final Position actPosition : positions) {
            result =
                result.replaceAt(actPosition,
                    this.getFreshMetaVariable(toUseNext));
        }
        return result;
    }

    public Node<NodeEntry> linearize(final Node<NodeEntry> node,
        final Set<Position> positions,
        final MyInteger toUseNext) {

        final NodeEntry nodeEntry = node.getObject();
        final TRSTerm t = nodeEntry.getT();
        final Set<TRSVariable> vars = nodeEntry.getVars();
        final Set<ExclusionSubstitution> substsExcl = nodeEntry.getSubsts();

        // some assertions
        if (aprove.Globals.useAssertions) {
            assert (this.getVariablePositions(t).containsAll(positions));
        }

        final TRSTerm tNew = this.linearize(t, positions, toUseNext);

        final Set<TRSVariable> varsNew = new LinkedHashSet<TRSVariable>(vars);
        varsNew.retainAll(tNew.getVariables());
        final Set<Position> intersection =
            new LinkedHashSet<Position>(positions);
        intersection.retainAll(nodeEntry.getTerminatingVariablePositions());
        for (final Position actPosition : intersection) {
            varsNew.add((TRSVariable) tNew.getSubterm(actPosition));
        }

        final Set<ExclusionSubstitution> substsNew =
            this.extract(tNew, substsExcl);

        return new Node<NodeEntry>(new NodeEntry(NodeType.Undefined,
            tNew, varsNew, substsNew, this));
    }

    /**************************************************************************/

    /**
     * @param pos must be a valid Position of "t"!
     */
    public boolean isPotentiallyReducible(final TRSTerm t, final Position pos) {
        for (final Position actPrefix : pos.getTruePrefixes()) {
            if (this.isRewritable(t, actPrefix)) {
                return false;
            }
        }
        return true;
    }

    /**************************************************************************/

    public boolean conflicts(final TRSTerm t,
        final TRSSubstitution substIns,
        final ExclusionSubstitution substExcl) {
        return t.applySubstitution(substExcl.getSubstitution()).getMatcher(
            t.applySubstitution(substIns)) != null;
    }

    public boolean isAdmissible(final TRSTerm t,
        final Set<ExclusionSubstitution> substsExcl,
        final TRSSubstitution substIns) {
        for (final ExclusionSubstitution actSubstExcl : substsExcl) {
            if (this.conflicts(t, substIns, actSubstExcl)) {
                return false;
            }
        }
        return true;
    }

    /**************************************************************************/

    public Set<ExclusionSubstitution> extract(final TRSTerm t,
        final Set<ExclusionSubstitution> substsExcl) {
        final Set<ExclusionSubstitution> result =
            new LinkedHashSet<ExclusionSubstitution>();
        final Set<TRSVariable> variablesT = t.getVariables();
        for (final ExclusionSubstitution actSubstExcl : substsExcl) {
            if (variablesT.containsAll(actSubstExcl.getFreeVariables())) {
                result.add(actSubstExcl);
            }
        }
        return result;
    }

    /**************************************************************************/

    public TRSTerm getCap(final TRSTerm t, final MyInteger toUseNext) {
        if (t instanceof TRSVariable) {
            return this.getFreshMetaVariable(toUseNext);
        }
        final TRSFunctionApplication tF = (TRSFunctionApplication) t;
        final ArrayList<TRSTerm> newArgs =
            new ArrayList<TRSTerm>(tF.getRootSymbol().getArity());
        for (final TRSTerm actArg : tF.getArguments()) {
            newArgs.add(this.getCap(actArg, toUseNext));
        }
        final TRSTerm tCap = TRSTerm.createFunctionApplication(tF.getRootSymbol(), ImmutableCreator.create(newArgs));
        for (final Rule actRule : this.rulesAllq) {
            if (new Unification(tCap, actRule.getLeft()).getMgu() != null) {
                return this.getFreshMetaVariable(toUseNext);
            }
        }
        return tCap;
    }

    public Set<TRSVariable> prop1(final TRSTerm t, final MyInteger toUseNext) {
        final Set<TRSVariable> result = new LinkedHashSet<TRSVariable>();
        final Set<Position> tCapVarPositions = this.getVariablePositions(this.getCap(t, toUseNext));
        for (final TRSVariable actVar : t.getVariables()) {
            final Set<Position> positions = this.getPositions(actVar, t);
            positions.retainAll(tCapVarPositions);
            if (!positions.isEmpty()) {
                result.add(actVar);
            }
        }
        return result;
    }

    public Set<TRSVariable> prop2(
        final TRSTerm t,
        final Set<ExclusionSubstitution> substsExcl,
        final MyInteger toUseNext
    ) {
        final Set<TRSVariable> result = new LinkedHashSet<TRSVariable>();
        final Set<TRSVariable> variablesT = t.getVariables();
        for (final TRSVariable actVar : variablesT) {
            if (!t.containsMoreThanOnce(actVar)) {
                loopPos: for (final Position actPos : this.getPositions(actVar, t)) {
                    for (final Position actPrefix : actPos.getTruePrefixes()) {
                        loopRule: for (Rule actRule : this.rulesAllq) {
                            actRule =
                                this.getWithFreshMetaVariables(actRule, toUseNext);
                            final TRSSubstitution unifier =
                                new Unification(t.getSubterm(actPrefix),
                                    actRule.getLeft()).getMgu();
                            if (unifier != null) {
                                for (final ExclusionSubstitution actSubstExcl : substsExcl) {
                                    if (!actSubstExcl.getFreeVariables().contains(
                                        actVar)
                                        && this.conflicts(t,
                                            unifier.restrictTo(variablesT),
                                            actSubstExcl)) {
                                        continue loopRule;
                                    }
                                }
                                continue loopPos;
                            }
                        }
                    }
                    result.add(actVar);
                    break;
                }
            }
        }
        return result;
    }

    public Set<TRSVariable> prop(final TRSTerm t,
        final Set<ExclusionSubstitution> substsExcl,
        final MyInteger toUseNext) {
        final Set<TRSVariable> result =
            new LinkedHashSet<TRSVariable>(this.prop1(t, toUseNext));
        result.addAll(this.prop2(t, substsExcl, toUseNext));
        return result;
    }

    public Set<TRSVariable> propagate(final Set<TRSVariable> vars,
        final TRSSubstitution substIns,
        final Set<ExclusionSubstitution> substsExcl,
        final MyInteger toUseNext) {
        final Set<TRSVariable> result = new LinkedHashSet<TRSVariable>();
        for (final TRSVariable actVar : vars) {
            final TRSTerm actVarSubstIns = substIns.substitute(actVar);
            result.addAll(this.prop(actVarSubstIns, this.extract(actVarSubstIns,
                substsExcl),
                toUseNext));
        }
        return result;
    }

    /**************************************************************************/

    public Set<ExclusionSubstitution> modify(final Set<ExclusionSubstitution> substsExcl,
        final TRSTerm t,
        final TRSSubstitution substIns) {
        final Set<ExclusionSubstitution> result =
            new LinkedHashSet<ExclusionSubstitution>();
        for (final ExclusionSubstitution actSubstExcl : substsExcl) {
            final ExclusionSubstitution actSubstExclModified =
                actSubstExcl.modify(t, substIns);
            if (actSubstExclModified != null) {
                result.add(actSubstExclModified);
            }
        }
        return result;
    }

    /**
     * @param pos must be a non-Variable-Position of the Pattern-Term of "node"
     * @param rule must be contained in rulesAllq! (renaming will be taken care of automatically)
     * @return a corresponding result-Node and Instantiation-Substitution and renamed Rule or
     *          null if Outermost-Narrowing fails
     */
    public Triple<Node<NodeEntry>, TRSSubstitution, Rule> outermostNarrow(final Node<NodeEntry> node,
        final Position pos,
        final Rule rule,
        final MyInteger toUseNext) {

        final NodeEntry nodeEntry = node.getObject();
        final NodeType lab = nodeEntry.getLab();
        final TRSTerm t = nodeEntry.getT();
        final Set<TRSVariable> vars = nodeEntry.getVars();
        final Set<ExclusionSubstitution> substsExcl = nodeEntry.getSubsts();

        // optimizations
        final Pair<TRSSubstitution, Boolean> unifierUnrenamedAdmissible =
            nodeEntry.getUnifierUnrenamedAdmissible(pos, rule, toUseNext);
        final TRSSubstitution unifierUnrenamed = unifierUnrenamedAdmissible.x;
        final Boolean admissible = unifierUnrenamedAdmissible.y;

        if (unifierUnrenamed == null) {

            // optimizations
            nodeEntry.informOutermostNarrowing(pos, rule, false);

            return null;
        }
        if (!admissible) {

            // optimizations
            nodeEntry.informOutermostNarrowing(pos, rule, false);

            return null;
        }

        // optimizations
        final Pair<TRSSubstitution, Rule> unifierRuleRenamed =
            this.getWithFreshMetaVariables(unifierUnrenamed, rule, toUseNext);
        final TRSSubstitution unifierRenamed = unifierRuleRenamed.x;
        final Rule ruleRenamed = unifierRuleRenamed.y;

        final TRSSubstitution substIns =
            unifierRenamed.restrictTo(t.getVariables());
        final TRSTerm tIns = t.applySubstitution(substIns);
        final TRSTerm tChild =
            tIns.replaceAt(pos, ruleRenamed.getRight().applySubstitution(
                unifierRenamed));
        final Set<ExclusionSubstitution> substsExclIns =
            this.modify(substsExcl, t, substIns);
        final Set<TRSVariable> varsChild =
            this.propagate(vars, substIns, substsExclIns, toUseNext);
        varsChild.retainAll(tChild.getVariables());
        if (!this.isPotentiallyReducible(tIns, pos)) {

            // optimizations
            nodeEntry.informOutermostNarrowing(pos, rule, false);

            return null;
        }
        final Set<ExclusionSubstitution> substsExclPrefix =
            new LinkedHashSet<ExclusionSubstitution>();
        for (final Rule actRule : this.rulesAllq) {
            final int actMaxIndex = TRSTerm.STANDARD_NUMBER + actRule.getVariables().size() - 1;
            for (final Position actPrefix : pos.getTruePrefixes()) {
                final TRSSubstitution unifier =
                    new Unification(tIns.getSubterm(actPrefix),
                        actRule.getLeft()).getMgu();
                if (unifier != null) {
                    substsExclPrefix.add(new ExclusionSubstitution(
                        this.restrictToVmeta(unifier), actMaxIndex, this).minimize(tIns));
                }
            }
        }
        Set<ExclusionSubstitution> substsChild =
            new LinkedHashSet<ExclusionSubstitution>(substsExclIns);
        substsChild.addAll(substsExclPrefix);
        substsChild = this.extract(tChild, substsChild);

        // optimizations
        nodeEntry.informOutermostNarrowing(pos, rule, true);

        return new Triple<Node<NodeEntry>, TRSSubstitution, Rule>(
            new Node<NodeEntry>(new NodeEntry(lab, tChild, varsChild,
                substsChild, this)), substIns, ruleRenamed);
    }

    /**
     * @param varRenaming must be a Variable-Renaming on Metavariables!
     */
    public Set<ExclusionSubstitution> transform(final Set<ExclusionSubstitution> substsExcl,
        final TRSSubstitution varRenaming) {
        final Set<ExclusionSubstitution> result =
            new LinkedHashSet<ExclusionSubstitution>();
        for (final ExclusionSubstitution actSubstExcl : substsExcl) {
            result.add(actSubstExcl.transform(varRenaming));
        }
        return result;
    }

    /**************************************************************************/

    /**
     * method for printing a Debug-File with given Name and Content to location this.pathForDebugOutputs
     */
    public void printDebugFile(final String fileName, final String fileContent) {
        final long nanos = System.nanoTime();
        FileWriter fw;
        try {
            final String base = "OTRSTerminationGraph";
            fw =
                new FileWriter(this.pathForDebugOutputs + "/" + base + nanos
                    + "_" + fileName + "_" + ".txt");
            fw.write(fileContent);
            fw.close();
        } catch (final IOException e) {
            e.printStackTrace();
        }
    }
}