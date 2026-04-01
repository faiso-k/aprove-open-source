package aprove.input.Utility;

import java.util.*;

import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.IQTermSet.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.*;
import aprove.verification.idpframework.Core.PredefinedFunctions.Domains.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author Martin Pluecker
 */
public class RawIDP {

    private final Set<IVariable<?>> variables = new LinkedHashSet<IVariable<?>>();
    private final Set<String> variableNames = new LinkedHashSet<String>();
    private final Set<IRule> rules = new LinkedHashSet<IRule>();

    private final Map<INode, ITerm<?>> nodes = new LinkedHashMap<INode, ITerm<?>>();
    private final Set<INode> initialNodes = new LinkedHashSet<INode>();

    private final Map<INode, Itpf> nodeConditions =
        new LinkedHashMap<INode, Itpf>();
    private final List<INode> nodeList = new ArrayList<INode>();
    private final Map<INode, VarRenaming> loopRenamings =
        new LinkedHashMap<INode, VarRenaming>();
    private Map<IEdge, Itpf> edges;

    private IDPPredefinedMap predefinedMap = IDPPredefinedMap.DEFAULT_MAP;

    private final PolyFactory polyFactory = new SharingPolyFactory();
    private final ItpfFactory itpfFactory = new SharingItpfFactory(this.polyFactory);

    private IQTermSet q = null;
    private int lastNodeId = -1;
    private boolean minimal = true;

    public Set<IVariable<?>> getVariables() {
        return this.variables;
    }

    public boolean isVariable(final String sym) {
        return this.variableNames.contains(sym);
    }

    public void addVariable(final IVariable<?> x) {
        this.variables.add(x);
        this.variableNames.add(x.getName());
    }

    public IDPPredefinedMap getPredefinedMap() {
        return this.predefinedMap;
    }

    public void setPredefinedMap(final IDPPredefinedMap predefinedMap) {
        this.predefinedMap = predefinedMap;
    }

    public void addRule(final IRule r) {
        this.rules.add(r);
    }

    public void addNode(final ITerm<?> t, final Itpf condition) {
        final INode node = INode.create(++this.lastNodeId);
        this.nodes.put(node, t);
        this.nodeConditions.put(node, condition);
        this.nodeList.add(node);
    }

    public void addAllRules(final Collection<IRule> rules) {
        for (final IRule rule : rules) {
            this.addRule(rule);
        }
    }

    public Set<IRule> getRules() {
        return this.rules;
    }

    public Map<INode, ITerm<?>> getNodes() {
        return this.nodes;
    }

    public Map<INode, Itpf> getNodeConditions() {
        return this.nodeConditions;
    }

    public IQTermSet getQ() {
        if (this.q == null) {
            this.createConstructorQ();
        }
        return this.q;
    }

    public void setQ(final IQTermSet q) {
        this.q = q;
    }

    public void createInnermostQ() {
        final Set<IFunctionApplication<?>> qTerms = new LinkedHashSet<IFunctionApplication<?>>();
        for (final IRule rule : this.rules) {
            qTerms.add(rule.getLeft());
        }
        this.q = new IQTermSet(qTerms, PredefinedQMode.PredefinedRule, this.predefinedMap);
    }

    public void createConstructorQ() {
        final Set<IFunctionApplication<?>> qTerms = new LinkedHashSet<IFunctionApplication<?>>();
        for (final IRule rule : this.rules) {
            qTerms.add(this.createVariableFunctionApplication(rule.getLeft().getRootSymbol()));
        }
        this.q = new IQTermSet(qTerms, PredefinedQMode.ConstructorRewriting, this.predefinedMap);
    }

    private IFunctionApplication<?> createVariableFunctionApplication(final IFunctionSymbol<?> fs) {
        final ArrayList<ITerm<?>> arguments = new ArrayList<ITerm<?>>(fs.getArity());

        for(int i = 0; i < fs.getArity(); i++) {
            arguments.add(ITerm.createVariable("x_" + i, DomainFactory.UNKNOWN));
        }

        return ITerm.createFunctionApplication(fs, arguments);
    }

    public void initEdges() {
        if (this.edges == null) {
            this.edges = new LinkedHashMap<IEdge, Itpf>();;
        }
    }

    public void addEdge(final int from,
        final IPosition fromPos,
        final int to,
        final EdgeType type,
        final VarRenaming loopRenaming,
        final Itpf condition) throws IllegalEdgeException {
        final INode fromNode = this.nodeList.get(from);
        final INode toNode = this.nodeList.get(to);
        if (fromNode.equals(toNode)) {
            if (loopRenaming == null) {
                throw new IllegalEdgeException("Loop renaming must be set iff and only iff edge is first loop.");
            }
            final VarRenaming out =
                this.loopRenamings.put(fromNode, loopRenaming);
            if (out != null && !out.equals(loopRenaming)) {
                throw new IllegalEdgeException("Different loop renaming than before.");
            }
        } else {
            final Set<IVariable<?>> vars =
                new HashSet<IVariable<?>>(this.nodes.get(fromNode).getVariables());
            vars.retainAll(this.nodes.get(toNode).getVariables());
            if (!vars.isEmpty()) {
                throw new IllegalEdgeException("Adjacent rules must be variable disjoint.");
            }
            if (loopRenaming != null) {
                throw new IllegalEdgeException("Loop renaming must be set iff and only iff edge is first loop.");
            }
        }

        final IEdge edge = IEdge.create(fromNode, fromPos, toNode, type);
        this.edges.put(edge, condition);
    }

    public void addInitialNode(final int nodeId) {
        this.initialNodes.add(this.nodeList.get(nodeId));
    }

    public Map<IEdge, Itpf> getEdges() {
        return this.edges;
    }

    public Set<INode> getInitialNodes() {
        return this.initialNodes;
    }

    public void setMinimal(final boolean minimal) {
        this.minimal = minimal;
    }

    public boolean isMinimal() {
        return this.minimal;
    }

    public Map<INode, VarRenaming> getLoopRenamings() {
        return this.loopRenamings;
    }

    public Map<INode, VarRenaming> completeLoopRenamings() {
        final Map<INode, VarRenaming> renamed =
            new LinkedHashMap<INode, VarRenaming>(
                this.loopRenamings);
        final FreshNameGenerator freshNames = new FreshNameGenerator(FreshNameGenerator.VARIABLES);
        for (final ITerm<?> term : this.nodes.values()) {
            freshNames.lockHasNames(term.getFunctionSymbols());
            freshNames.lockHasNames(term.getVariables());
        }
        for (final Map.Entry<INode, ITerm<?>> nodeTerm : this.nodes.entrySet()) {
            if (!renamed.containsKey(nodeTerm.getKey())) {
                final Map<IVariable<?>, IVariable<?>> renaming = new LinkedHashMap<IVariable<?>, IVariable<?>>();
                for (final IVariable<?> var : nodeTerm.getValue().getVariables()) {
                    renaming.put(var, ITerm.createVariable(
                        freshNames.getFreshName(var.getName(), false),
                        var.getDomain()));
                }
                renamed.put(nodeTerm.getKey(),
                    VarRenaming.create(ImmutableCreator.create(renaming), false, this.polyFactory));
            }
        }
        return renamed;
    }



    public ItpfFactory getItpfFactory() {
        return this.itpfFactory;
    }



    public static class IllegalEdgeException extends Exception {

        private static final long serialVersionUID = 1L;

        public IllegalEdgeException(final String message) {
            super(message);
        }

    }

}
