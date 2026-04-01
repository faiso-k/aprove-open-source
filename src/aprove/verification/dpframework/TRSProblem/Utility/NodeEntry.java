package aprove.verification.dpframework.TRSProblem.Utility;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * this class represents the information labelled to a Node of the "OutermostTerminationGraph"
 *
 * @author Sebastian Weise
 */

public class NodeEntry {

    public enum NodeType {
        Narrow, ParSplit, Linearize, Termin, Ins, Undefined
    }

    private NodeType lab;
    private final TRSTerm t;
    private final Set<TRSVariable> vars;
    private final Set<ExclusionSubstitution> substs;
    private final OTRSTermGraphUtils util;

    // additional information
    // for Linearize-Nodes
    private Set<Position> positionsLinearize;
    // for Ins-Nodes
    private boolean isReUseNode;
    // for any Node; will only be set if we have extracted QDP-Problems from the Graph
    private boolean belongsToSCC;

    /*
     * to avoid multiple computations;
     * will only be set after asking for the corresponding values or
     *      be computed step by step and as far as needed while processing the current Node
     */
    // the Variables of the Pattern-Term
    private ImmutableSet<TRSVariable> variables;
    // the Positions of the Pattern-Term
    private ImmutableSet<Position> positions;
    // the Variable-Positions of the Pattern-Term
    private ImmutableSet<Position> variablePositions;
    // the Positions of outermost-terminating Variables
    private ImmutableSet<Position> terminatingVariablePositions;
    private ImmutableSet<Position> nonVariablePositions;
    // maps each Variable to it's Set of Positions
    private ImmutableMap<TRSVariable, List<Position>> varsToPos;
    private ImmutableSet<Position> potentiallyReduciblePositions;
    // maps each Variable to it's Set of potentially reducible Positions
    private final Map<TRSVariable, Set<Position>> varsToPotentiallyReduciblePositions;
    // the Set of all Metavariables occuring in ExclusionSubstitutions
    private ImmutableSet<TRSVariable> variablesInExclusionSubstitutions;
    private Boolean hasPotentiallyReducibleVariablePositions;
    private ImmutableSet<TRSVariable> criticalVariables;
    // the Positions of critical Variables
    private ImmutableSet<Position> criticalVariablePositions;
    /*
     * corresponding MGUs for Narrowing if existing and whether they would be admissible if
     *      being renamed accordingly and restricted to the Variables of t;
     * contains only Rules from util.getRulesAllq(),
     *      so Substitutions DON'T contain any fresh Metavariables, but ALLQUANTIFIED Variables instead!
     * valuePair == null => not computed yet;
     * valuePair.x == null => no Unification possible;
     * valuePair.y != null && valuePair.y == null => Admissibility not checked yet
     */
    private final Map<Pair<Position, Rule>, Pair<TRSSubstitution, Boolean>> posRuleToUnifAdm;
    // does Outermost-Narrowing fail at all Non-Variable-Positions of t (and with any Rule)?
    private Boolean outermostNarrowingFails;
    // for computing "outermostNarrowingFails"; contains only Rules from util.getRulesAllq()!
    private final Set<Pair<Position, Rule>> alreadyChecked;
    // the Complexity of the Pattern-Term
    private final int complexity;

    public NodeEntry(final NodeType lab, final TRSTerm t,
            final Set<TRSVariable> vars, final Set<ExclusionSubstitution> substs,
            final OTRSTermGraphUtils util) {
        this.lab = lab;
        this.t = t;
        if (vars == null) {
            this.vars = new LinkedHashSet<TRSVariable>();
        } else {
            this.vars = vars;
        }
        if (substs == null || !util.getUseExclusionSubstitutions()) {
            this.substs = new LinkedHashSet<ExclusionSubstitution>();
        } else {
            this.substs = substs;
        }
        this.util = util;

        this.varsToPotentiallyReduciblePositions =
            new LinkedHashMap<TRSVariable, Set<Position>>();
        this.posRuleToUnifAdm =
            new LinkedHashMap<Pair<Position, Rule>, Pair<TRSSubstitution, Boolean>>();
        this.alreadyChecked = new LinkedHashSet<Pair<Position, Rule>>();
        this.complexity = util.complexity(t);
    }

    public NodeType getLab() {
        return this.lab;
    }

    public void setLab(final NodeType newLab) {
        this.lab = newLab;
    }

    public TRSTerm getT() {
        return this.t;
    }

    public Set<TRSVariable> getVars() {
        return new LinkedHashSet<TRSVariable>(this.vars);
    }

    public Set<ExclusionSubstitution> getSubsts() {
        return new LinkedHashSet<ExclusionSubstitution>(this.substs);
    }

    /**************************************************************************/

    public void setPositionsLinearize(final Set<Position> positionsLinearize) {
        this.positionsLinearize = positionsLinearize;
    }

    public boolean getIsReUseNode() {
        return this.isReUseNode;
    }

    public void setIsReUseNode(final boolean isReUseNode) {
        this.isReUseNode = isReUseNode;
    }

    public boolean getBelongsToSCC() {
        return this.belongsToSCC;
    }

    public void setBelongsToSCC(final boolean belongsToSCC) {
        this.belongsToSCC = belongsToSCC;
    }

    /**************************************************************************/

    @Override
    public String toString() {
        final StringBuilder result =
            new StringBuilder(this.lab + "\\nterm: " + this.t
                + "\\nvars: " + this.vars + "\\nsubsts: " + this.substs);
        if (this.positionsLinearize != null) {
            result.append("\\npositions: " + this.positionsLinearize);
        }
        return result.toString();
    }

    /**************************************************************************/
    /**************************************************************************/

    private ImmutableSet<TRSVariable> getVariables() {
        if (this.variables == null) {
            this.variables =
                ImmutableCreator.create(this.getVarsToPos().keySet());
        }
        return this.variables;
    }

    private ImmutableSet<Position> getPositions() {
        if (this.positions == null) {
            this.positions = ImmutableCreator.create(this.t.getPositions());
        }
        return this.positions;
    }

    private ImmutableSet<Position> getVariablePositions() {
        if (this.variablePositions == null) {
            this.buildTerminatingAndAllVariablePositions();
        }
        return this.variablePositions;
    }

    public ImmutableSet<Position> getTerminatingVariablePositions() {
        if (this.terminatingVariablePositions == null) {
            this.buildTerminatingAndAllVariablePositions();
        }
        return this.terminatingVariablePositions;
    }

    private void buildTerminatingAndAllVariablePositions() {
        final Set<Position> variablePositionsTemp =
            new LinkedHashSet<Position>();
        final Set<Position> terminatingVariablePositionsTemp =
            new LinkedHashSet<Position>();
        for (final Map.Entry<TRSVariable, List<Position>> actVarPositions : this.getVarsToPos().entrySet()) {
            variablePositionsTemp.addAll(actVarPositions.getValue());
            if (this.vars.contains(actVarPositions.getKey())) {
                terminatingVariablePositionsTemp.addAll(actVarPositions.getValue());
            }
        }
        this.variablePositions = ImmutableCreator.create(variablePositionsTemp);
        this.terminatingVariablePositions =
            ImmutableCreator.create(terminatingVariablePositionsTemp);
    }

    private ImmutableSet<Position> getNonVariablePositions() {
        if (this.nonVariablePositions == null) {
            final Set<Position> nonVariablePositionsTemp =
                new LinkedHashSet<Position>(this.getPositions());
            nonVariablePositionsTemp.removeAll(this.getVariablePositions());
            this.nonVariablePositions =
                ImmutableCreator.create(nonVariablePositionsTemp);
        }
        return this.nonVariablePositions;
    }

    private ImmutableMap<TRSVariable, List<Position>> getVarsToPos() {
        if (this.varsToPos == null) {
            this.varsToPos =
                ImmutableCreator.create(this.t.getVariablePositions());
        }
        return this.varsToPos;
    }

    /**************************************************************************/

    /**
     * @param pos must be a valid Position of t
     * @param rule must be contained in util.getRulesAllq()!
     * @return see this.posRuleToSubstAdm!
     */
    public TRSSubstitution getUnifierUnrenamed(final Position pos,
        final Rule rule,
        final MyInteger toUseNext) {
        return this.getUnifierUnrenamedAdmissible(pos, rule, false, toUseNext).x;
    }

    /**
     * @param pos must be a valid Position of t
     * @param rule must be contained in util.getRulesAllq()!
     * @return see this.posRuleToSubstAdm!
     */
    public Pair<TRSSubstitution, Boolean> getUnifierUnrenamedAdmissible(final Position pos,
        final Rule rule,
        final MyInteger toUseNext) {
        return this.getUnifierUnrenamedAdmissible(pos, rule, true, toUseNext);
    }

    /**
     * @param pos must be a valid Position of t
     * @param rule must be contained in util.getRulesAllq()!
     * @return see this.posRuleToSubstAdm!
     */
    private Pair<TRSSubstitution, Boolean> getUnifierUnrenamedAdmissible(final Position pos,
        final Rule rule,
        final boolean computeAdmissibility,
        final MyInteger toUseNext) {
        final Pair<Position, Rule> pair = new Pair<Position, Rule>(pos, rule);
        Pair<TRSSubstitution, Boolean> substAdm = this.posRuleToUnifAdm.get(pair);
        if (substAdm == null) {
            substAdm =
                new Pair<TRSSubstitution, Boolean>(new Unification(
                    this.t.getSubterm(pos), rule.getLeft()).getMgu(), null);
            this.posRuleToUnifAdm.put(pair, substAdm);
        }
        if (computeAdmissibility && substAdm.y == null && substAdm.x != null) {
            substAdm.setValue(this.isAdmissible(this.util.getWithFreshMetaVariables(
                substAdm.x.restrictTo(this.getVariables()), toUseNext)));
        }
        return substAdm.shallowCopy();
    }

    /**
     * @param pos must be a valid Position of t
     * @param rule must be contained in util.getRulesAllq()!
     */
    private void setUnifierUnrenamedAdmissible(final Position pos,
        final Rule rule,
        final TRSSubstitution unifierUnrenamed,
        final Boolean admissible) {
        final Pair<Position, Rule> pair = new Pair<Position, Rule>(pos, rule);
        final Pair<TRSSubstitution, Boolean> substAdm =
            this.posRuleToUnifAdm.get(pair);
        if (substAdm == null || (substAdm.x != null && substAdm.y == null)) {
            this.posRuleToUnifAdm.put(pair, new Pair<TRSSubstitution, Boolean>(
                unifierUnrenamed, admissible));
        }
    }

    /**************************************************************************/

    public ImmutableSet<Position> getPotentiallyReduciblePositions() {
        if (this.potentiallyReduciblePositions == null) {
            final Set<Position> potentiallyReduciblePositionsTemp =
                new LinkedHashSet<Position>();
            final Set<Position> reduciblePositions =
                new LinkedHashSet<Position>();
            for (final Position actPosition : this.getPositions()) {
                for (final Rule actRule : this.util.getRulesAllq()) {
                    final TRSSubstitution matcher =
                        actRule.getLeft().getMatcher(
                            this.t.getSubterm(actPosition));
                    if (matcher != null) {
                        this.setUnifierUnrenamedAdmissible(actPosition,
                            actRule, matcher, null);
                        reduciblePositions.add(actPosition);
                        break;
                    }
                }
            }
            final Set<Position> positionsTemp =
                new LinkedHashSet<Position>(this.getPositions());
            loop: while (!positionsTemp.isEmpty()) {
                final Position actPosition = positionsTemp.iterator().next();
                final Set<Position> actPrefixes = actPosition.getTruePrefixes();
                for (final Position actPrefix : actPrefixes) {
                    if (reduciblePositions.contains(actPrefix)) {
                        positionsTemp.remove(actPosition);
                        continue loop;
                    }
                }
                final Set<Position> newPotentiallyReduciblePositions =
                    new LinkedHashSet<Position>(actPrefixes);
                newPotentiallyReduciblePositions.add(actPosition);
                potentiallyReduciblePositionsTemp.addAll(newPotentiallyReduciblePositions);
                positionsTemp.removeAll(newPotentiallyReduciblePositions);
            }
            this.potentiallyReduciblePositions =
                ImmutableCreator.create(potentiallyReduciblePositionsTemp);
        }
        return this.potentiallyReduciblePositions;
    }

    /**
     * @param var has to be contained in t!
     */
    public ImmutableSet<Position> getPotentiallyReduciblePositions(final TRSVariable var) {
        Set<Position> result =
            this.varsToPotentiallyReduciblePositions.get(var);
        if (result == null) {
            result = new LinkedHashSet<Position>(this.getVarsToPos().get(var));
            result.retainAll(this.getPotentiallyReduciblePositions());
            this.varsToPotentiallyReduciblePositions.put(var, result);
        }
        return ImmutableCreator.create(result);
    }

    /**
     * @param var has to be contained in t!
     */
    private Boolean hasPotentiallyReduciblePositions(final TRSVariable var) {
        return !this.getPotentiallyReduciblePositions(var).isEmpty();
    }

    public boolean hasPotentiallyReducibleVariablePositions() {
        if (this.hasPotentiallyReducibleVariablePositions == null) {
            this.hasPotentiallyReducibleVariablePositions = false;
            for (final TRSVariable actVar : this.getVariables()) {
                if (this.hasPotentiallyReduciblePositions(actVar)) {
                    this.hasPotentiallyReducibleVariablePositions =
                        true;
                    break;
                }
            }
        }
        return this.hasPotentiallyReducibleVariablePositions;
    }

    /**
     * @param var has to be contained in t!
     */
    private boolean isCritical(final TRSVariable var) {
        if (this.hasPotentiallyReduciblePositions(var)) {
            if (this.containsMoreThanOnce(var)) {
                return true;
            }
            if (this.variablesInExclusionSubstitutions == null) {
                this.buildVariablesInExclusionSubstitutions();
            }
            return this.variablesInExclusionSubstitutions.contains(var);
        }
        return false;
    }

    private boolean containsMoreThanOnce(final TRSVariable var) {
        final List<Position> positions = this.getVarsToPos().get(var);
        if (positions == null) {
            return false;
        }
        return positions.size() >= 2;
    }

    private void buildVariablesInExclusionSubstitutions() {
        final Set<TRSVariable> variablesInExcludeSubstitutionsTemp =
            new LinkedHashSet<TRSVariable>();
        for (final ExclusionSubstitution actSubstExcl : this.substs) {
            variablesInExcludeSubstitutionsTemp.addAll(actSubstExcl.getFreeVariables());
        }
        variablesInExcludeSubstitutionsTemp.retainAll(this.getVariables());
        this.variablesInExclusionSubstitutions =
            ImmutableCreator.create(variablesInExcludeSubstitutionsTemp);
    }

    public ImmutableSet<TRSVariable> getCriticalVariables() {
        if (this.criticalVariables == null) {
            final Set<TRSVariable> criticalVariablesTemp =
                new LinkedHashSet<TRSVariable>();
            for (final TRSVariable actVar : this.getVariables()) {
                if (this.isCritical(actVar)) {
                    criticalVariablesTemp.add(actVar);
                }
            }
            this.criticalVariables =
                ImmutableCreator.create(criticalVariablesTemp);
        }
        return this.criticalVariables;
    }

    public boolean hasCriticalVariables() {
        return !this.getCriticalVariables().isEmpty();
    }

    public ImmutableSet<Position> getCriticalVariablePositions() {
        if (this.criticalVariablePositions == null) {
            final Set<Position> criticalVariablePositionsTemp =
                new LinkedHashSet<Position>();
            for (final TRSVariable actVar : this.getCriticalVariables()) {
                criticalVariablePositionsTemp.addAll(this.getVarsToPos().get(
                    actVar));
            }
            this.criticalVariablePositions =
                ImmutableCreator.create(criticalVariablePositionsTemp);
        }
        return this.criticalVariablePositions;
    }

    /**************************************************************************/

    public boolean isExpandable() {
        final Set<TRSVariable> potentiallyNonTerminatingVariables =
            new LinkedHashSet<TRSVariable>(this.getVariables());
        potentiallyNonTerminatingVariables.removeAll(this.vars);
        for (final TRSVariable actVar : potentiallyNonTerminatingVariables) {
            if (this.hasPotentiallyReduciblePositions(actVar)) {
                return false;
            }
        }
        return true;
    }

    /**
     * @param pos must be a non-Variable-Position of t!
     * @param rule must be contained in util.getRulesAllq()!
     * @param succeeded true iff the Outermost-Narrowing succeeded
     *                      at Position "pos" with Rule "rule"
     */
    public void informOutermostNarrowing(final Position pos, final Rule rule, final boolean succeeded) {
        if (succeeded) {
            this.outermostNarrowingFails = false;
        } else {
            this.alreadyChecked.add(new Pair<Position, Rule>(pos, rule));
        }
    }

    /**
     * does Outermost-Narrowing fail at all Non-Variable-Positions of t (and with any Rule)?
     */
    public boolean outermostNarrowingFails(final MyInteger toUseNext) {
        if (this.outermostNarrowingFails == null) {
            final Node<NodeEntry> node = new Node<NodeEntry>(this);
            for (final Position actPos : this.getNonVariablePositions()) {
                for (final Rule actRule : this.util.getRulesAllq()) {
                    final Pair<Position, Rule> pair =
                        new Pair<Position, Rule>(actPos, actRule);
                    if (this.alreadyChecked.contains(pair)) {
                        continue;
                    }
                    this.util.outermostNarrow(node, actPos, actRule, toUseNext);
                    if (this.outermostNarrowingFails != null) {
                        return this.outermostNarrowingFails;
                    }
                }
            }
            this.outermostNarrowingFails = true;
        }
        return this.outermostNarrowingFails;
    }

    /**************************************************************************/

    public boolean isAdmissible(final TRSSubstitution substIns) {
        return this.util.isAdmissible(this.t, this.substs, substIns);
    }

    public boolean isEquivalent(final NodeEntry nodeEntry) {

        final TRSTerm tOther = nodeEntry.getT();
        final Set<TRSVariable> varsOther = nodeEntry.getVars();
        final Set<ExclusionSubstitution> substsOther =
            nodeEntry.getSubsts();

        final TRSSubstitution matcher = this.t.getMatcher(tOther);
        if (matcher == null) {
            return false;
        }
        if (!this.util.isVariableRenaming(matcher, this.getVariables(),
            tOther.getVariables())) {
            return false;
        }
        return varsOther.equals(this.util.applyVariableRenaming(this.vars,
            matcher))
            && substsOther.equals(this.util.transform(this.substs, matcher));
    }

    public int getComplexity() {
        return this.complexity;
    }
}