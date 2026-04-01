package aprove.verification.idpframework.Processors.ItpfRules.Execution;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * @author Martin Pluecker
 */
public class ItpfSchedulerProof<FormulaType extends ProcessableFormula, RuleType extends ExecutableRule<FormulaType, ?>> extends DefaultProof implements IDPExportable {

    private static final int EQUATION_NUMBER_DIGITS = 3;
    private static final int IMPLICATION_STRING_LENGH = 3;

    protected final SimpleGraph<FormulaType, ImmutablePair<RuleType, ImplicationType>> steps;
    protected final Map<FormulaType, Node<FormulaType>> formulaToNode;
    protected final Set<Node<FormulaType>> leaves;
    protected final IDPProblem idp;
    protected final Node<FormulaType> startNode;
    protected final Node<FormulaType> trueNode;
    protected volatile ImplicationType totalImplication = ImplicationType.EQUIVALENT;

    public ItpfSchedulerProof(final IDPProblem idp, final FormulaType startFormula, final FormulaType TRUE) {
        this.idp = idp;
        this.steps = new SimpleGraph<FormulaType , ImmutablePair<RuleType, ImplicationType>>();
        this.formulaToNode = new LinkedHashMap<FormulaType , Node<FormulaType>>();
        this.leaves = new LinkedHashSet<Node<FormulaType>>();

        this.startNode = this.createNode(startFormula);
        if (startFormula.equals(TRUE)) {
            this.trueNode = this.startNode;
        } else {
            this.trueNode = this.createNode(TRUE);
        }
        this.leaves.remove(this.trueNode);
    }

    public synchronized boolean addStep(final FormulaType input, final RuleType rule, final ImplicationType implication, final Conjunction<FormulaType> result) {
        final Node<FormulaType> inputNode = this.formulaToNode.get(input);
        if (inputNode == null) {
            throw new IllegalStateException("illegal step");
        }

        // check for cycles
        for (final FormulaType formula : result) {
            final Node<FormulaType> resultNode = this.formulaToNode.get(formula);
            if (resultNode != null && this.steps.getPath(resultNode, inputNode) != null) {
                return false;
            }
        }

        if (!this.leaves.remove(inputNode)) {
            throw new IllegalStateException("illegal step");
        }

        if (result.isEmpty()) {
            this.steps.addEdge(inputNode, this.trueNode, new ImmutablePair<RuleType, ImplicationType>(rule, implication));
        } else {
            for (final FormulaType formula : result) {
                Node<FormulaType> resultNode = this.formulaToNode.get(formula);
                if (resultNode == null) {
                    resultNode = this.createNode(formula);
                }

                this.steps.addEdge(inputNode, resultNode, new ImmutablePair<RuleType, ImplicationType>(rule, implication));
            }
        }

        this.totalImplication = this.totalImplication.mult(implication);

        return true;
    }

    public IDPProblem getIDP() {
        return this.idp;
    }

    public FormulaType getStartFormula() {
        return this.startNode.getObject();
    }

    public boolean isEmptyProof() {
        return this.steps.getEdges().isEmpty();
    }

    public boolean isFailedProof() {
        return this.leaves.contains(this.startNode);
    }

    public synchronized ImplicationType getTotalImplication() {
        return this.totalImplication;
    }

    public synchronized Set<FormulaType> getLastFormulaStates() {
        final Set<FormulaType> result = new LinkedHashSet<FormulaType>();

        for (final Node<FormulaType> leaf : this.leaves) {
            result.add(leaf.getObject());
        }

        return result;
    }

    @Override
    public final String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public final String export(final Export_Util o) {
        return this.export(o, IDPExportable.DEFAULT_LEVEL);
    }

    @Override
    public final String export(final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        final StringBuilder sb = new StringBuilder();
        this.export(sb, o, verbosityLevel);
        return sb.toString();
    }

    @Override
    public final void export(final StringBuilder sb, final Export_Util o, final VerbosityLevel verbosityLevel) {
        final ExecutionStepColorization colorization = this.createColorization();
        this.export(sb, o, verbosityLevel, colorization, 0);
    }

    public synchronized Pair<Integer, Map<FormulaType, Integer>> export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel,
        final int nextExportId) {

        final ExecutionStepColorization colorization = this.createColorization();
        return this.export(sb, o, verbosityLevel, colorization, nextExportId);
    }

    public synchronized Pair<Integer, Map<FormulaType, Integer>> export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel,
        final ExecutionStepColorization colors,
        int nextExportId) {
        final SimpleGraph<FormulaType, ImmutableTriple<ImmutableList<RuleType>, ImplicationType, ImmutableList<FormulaType>>> exportCompressedSteps =
            this.exportCompressStepsGraph(verbosityLevel);

        this.exportStartFormula(exportCompressedSteps, nextExportId, this.startNode, sb, o, verbosityLevel, colors);

        final Map<FormulaType, Integer> equationIds = new LinkedHashMap<FormulaType, Integer>();

        if (!this.leaves.contains(this.startNode)) {
            nextExportId = this.exportSteps(sb, o, verbosityLevel, exportCompressedSteps, nextExportId, equationIds, colors);
        } else {
            equationIds.put(this.startNode.getObject(), nextExportId);
        }
//         sb.append(o.linebreak());

        return new Pair<Integer, Map<FormulaType, Integer>>(nextExportId, equationIds);
    }

    protected synchronized int exportSteps(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel,
        final SimpleGraph<FormulaType, ImmutableTriple<ImmutableList<RuleType>, ImplicationType, ImmutableList<FormulaType>>> exportCompressedSteps,
        final int startNodeExportId,
        final Map<FormulaType, Integer> equationIds,
        final ExecutionStepColorization colors) {

        return this.exportSteps(exportCompressedSteps,
            this.startNode,
            startNodeExportId,
            startNodeExportId + 1,
            equationIds, colors,
            sb, o, verbosityLevel);
    }

    private ExecutionStepColorization createColorization() {
        final List<Pair<FormulaType, FormulaType>> stepList = new ArrayList<Pair<FormulaType, FormulaType>>();
        for (final Edge<ImmutablePair<RuleType, ImplicationType>,FormulaType> edge : this.steps.getEdges()) {
            stepList.add(new Pair<FormulaType, FormulaType>(
                    edge.getStartNode().getObject(),
                    edge.getEndNode().getObject()));
        }

        return ExecutionStepColorization.create(stepList);
    }

    protected int exportSteps(final SimpleGraph<FormulaType, ImmutableTriple<ImmutableList<RuleType>, ImplicationType, ImmutableList<FormulaType>>> exportCompressedSteps,
        final Node<FormulaType> currentNode,
        final int parentExportId,
        int nextExportId,
        final Map<FormulaType, Integer> equationIds,
        final ExecutionStepColorization colors,
        final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        final Set<Edge<ImmutableTriple<ImmutableList<RuleType>, ImplicationType, ImmutableList<FormulaType>>, FormulaType>> outEdges = exportCompressedSteps.getOutEdges(currentNode);
        if (!outEdges.isEmpty()) {
            final ImmutableList<RuleType> appliedRules = outEdges.iterator().next().getObject().x;
            final Iterator<RuleType> appliedRulesIter = appliedRules.iterator();
            while (appliedRulesIter.hasNext()) {
                final RuleType rule = appliedRulesIter.next();
                rule.export(sb, o, verbosityLevel);
                if (appliedRulesIter.hasNext()) {
                    sb.append(", ");
                }
            }

            sb.append(" applied to (");
            sb.append(parentExportId);
            sb.append("):");
            sb.append(o.linebreak());

            final ImplicationType totalStepImplication = outEdges.iterator().next().getObject().y;
            final LinkedHashMap<Node<FormulaType>, Integer> parentEquationIDs =
                new LinkedHashMap<Node<FormulaType>, Integer>();

            for (final Edge<ImmutableTriple<ImmutableList<RuleType>, ImplicationType, ImmutableList<FormulaType>>, FormulaType> outEdge : outEdges) {
                final Collection<List<? extends ExecutionMarkable>> sequences = new ArrayList<List<? extends ExecutionMarkable>>();
                final ImmutableList<FormulaType> baseList = outEdge.getObject().z;
                sequences.add(baseList);

                final Set<Edge<ImmutableTriple<ImmutableList<RuleType>, ImplicationType, ImmutableList<FormulaType>>, FormulaType>> outSuccEdges =
                    exportCompressedSteps.getOutEdges(outEdge.getEndNode());

                for (final Edge<ImmutableTriple<ImmutableList<RuleType>, ImplicationType, ImmutableList<FormulaType>>, FormulaType> outSuccEdge : outSuccEdges) {
                    final List<ExecutionMarkable> succSeq = new ArrayList<ExecutionMarkable>();
                    succSeq.add(baseList.get(baseList.size() - 1));
                    succSeq.addAll(outSuccEdge.getObject().z);
                    sequences.add(succSeq);
                }

                final ExecutionStepColorization restrictedColors = colors.restrictTo(sequences);

                final Node<FormulaType> succNode = outEdge.getEndNode();
                final Integer equationId = equationIds.get(succNode.getObject());
                if (equationId != null) {
                    this.exportFormula(totalStepImplication, succNode.getObject(), equationId, restrictedColors, true, sb, o, verbosityLevel);
                } else {
                    parentEquationIDs.put(succNode, nextExportId);
                    equationIds.put(succNode.getObject(), nextExportId);
                    this.exportFormula(totalStepImplication, succNode.getObject(), nextExportId, restrictedColors, outSuccEdges.isEmpty(), sb, o, verbosityLevel);
                    nextExportId++;
                }
            }

            if (outEdges.size() > 1) {
                sb.append(o.linebreak());
            }

            for (final Edge<ImmutableTriple<ImmutableList<RuleType>, ImplicationType, ImmutableList<FormulaType>>, FormulaType> outEdge : outEdges) {
                final Node<FormulaType> succNode = outEdge.getEndNode();
                final Integer parentEqId = parentEquationIDs.get(succNode);

                if (parentEqId != null) {
                    nextExportId = this.exportSteps(
                        exportCompressedSteps,
                        outEdge.getEndNode(),
                        parentEqId,
                        nextExportId,
                        equationIds,
                        colors,
                        sb,
                        o,
                        verbosityLevel);
                }
                if (outEdges.size() > 1) {
                    sb.append(o.linebreak());
                }
            }
        }

        return nextExportId;
    }

    protected void exportStartFormula(final SimpleGraph<FormulaType, ImmutableTriple<ImmutableList<RuleType>, ImplicationType, ImmutableList<FormulaType>>> exportCompressedSteps,
        final int currentExportId,
        final Node<FormulaType> startNode,
        final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel,
        final ExecutionStepColorization colors) {
        for (int i = ItpfSchedulerProof.IMPLICATION_STRING_LENGH - 1; i >= 0; i--) {
            sb.append(o.escape(" "));
        }

        for (int i = ItpfSchedulerProof.EQUATION_NUMBER_DIGITS - (int) Math.floor(Math.log10(currentExportId)); i >= 0; i--) {
            sb.append(o.escape(" "));
        }

        sb.append("(");
        sb.append(currentExportId);
        sb.append("): ");

        final Collection<List<? extends ExecutionMarkable>> sequences = new ArrayList<List<? extends ExecutionMarkable>>();
        for (final Edge<ImmutableTriple<ImmutableList<RuleType>, ImplicationType, ImmutableList<FormulaType>>, FormulaType> outEdge : exportCompressedSteps.getOutEdges(startNode)) {
            sequences.add(outEdge.getObject().z);
        }

        final ExecutionStepColorization restrictedColors = colors.restrictTo(sequences);

        startNode.getObject().export(sb, o, verbosityLevel, restrictedColors);
        sb.append(o.cond_linebreak());
    }

    private void exportFormula(final ImplicationType implication,
        final ExecutionExportable formula,
        final int currentExportId,
        final ExecutionStepColorization colors,
        final boolean leaf,
        final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        final StringBuilder formulaSb = new StringBuilder();

        final String implicationString = implication.export(o, verbosityLevel);
        formulaSb.append(implicationString);

        for (int i = ItpfSchedulerProof.IMPLICATION_STRING_LENGH - implicationString.length() - 1; i >= 0; i--) {
            formulaSb.append(o.escape(" "));
        }

        for (int i = ItpfSchedulerProof.EQUATION_NUMBER_DIGITS - (int) Math.floor(Math.log10(currentExportId)); i >= 0; i--) {
            formulaSb.append(o.escape(" "));
        }

        formulaSb.append("(");
        formulaSb.append(currentExportId);
        formulaSb.append("): ");
        formula.export(formulaSb, o, verbosityLevel, colors);
        if (leaf) {
            sb.append(o.indent(o.bold(formulaSb.toString())));
        } else {
            sb.append(o.indent(formulaSb.toString()));
        }
        sb.append(o.linebreak());
    }

    private Node<FormulaType> createNode(final FormulaType formula) {
        final Node<FormulaType> node = new Node<FormulaType>(formula);
        this.formulaToNode.put(formula, node);
        this.leaves.add(node);
        this.steps.addNode(node);
        return node;
    }

    private SimpleGraph<FormulaType, ImmutableTriple<ImmutableList<RuleType>, ImplicationType, ImmutableList<FormulaType>>> exportCompressStepsGraph(final VerbosityLevel verbosityLevel) {
        final SimpleGraph<FormulaType, ImmutableTriple<ImmutableList<RuleType>, ImplicationType, ImmutableList<FormulaType>>> compressedSteps =
            new SimpleGraph<FormulaType, ImmutableTriple<ImmutableList<RuleType>, ImplicationType, ImmutableList<FormulaType>>>();

        compressedSteps.addNode(this.startNode);

        final List<RuleType> stepRules = new ArrayList<RuleType>();

        this.addCompressedEdges(
            this.startNode,
            this.startNode,
            stepRules,
            Collections.singletonList(this.startNode.getObject()),
            ImplicationType.EQUIVALENT,
            compressedSteps,
            verbosityLevel);

        return compressedSteps;
    }

    private void addCompressedEdges(final Node<FormulaType> stepStartNode,
        final Node<FormulaType> currentNode,
        final List<RuleType> stepRules,
        final List<FormulaType> stepFormulas,
        final ImplicationType stepImplication,
        final SimpleGraph<FormulaType, ImmutableTriple<ImmutableList<RuleType>, ImplicationType, ImmutableList<FormulaType>>> compressedSteps,
        final VerbosityLevel verbosityLevel) {
        final Set<Edge<ImmutablePair<RuleType, ImplicationType>, FormulaType>> outEdges = this.steps.getOutEdges(currentNode);

        boolean mustExportStep = outEdges.size() > 1;
        // determine if step must be exported
        {
            final ArrayList<RuleType> totalStepRules = new ArrayList<RuleType>(stepRules);
            if (!outEdges.isEmpty()) {
                {
                    final ImmutablePair<RuleType, ImplicationType> step = outEdges.iterator().next().getObject();
                    totalStepRules.add(step.x);
                }

                if (!mustExportStep) {
                    for (final Edge<ImmutablePair<RuleType, ImplicationType>, FormulaType> step : outEdges) {
                        if (compressedSteps.contains(step.getEndNode())) {
                            mustExportStep = true;
                        }
                    }
                }
            }

            if (!mustExportStep) {
                searchIncompatibleRule : for (final Edge<ImmutablePair<RuleType, ImplicationType>, FormulaType> step : outEdges) {
                    if (this.leaves.contains(step.getEndNode()) || step.getEndNode().equals(this.trueNode)) {
                        mustExportStep = true;
                        break searchIncompatibleRule;
                    } else if (verbosityLevel.compareTo(VerbosityLevel.MIDDLE) >= 0) {
                        final Set<Edge<ImmutablePair<RuleType, ImplicationType>, FormulaType>> stepSteps = this.steps.getOutEdges(step.getEndNode());
                        for (final Edge<ImmutablePair<RuleType, ImplicationType>, FormulaType> stepStep : stepSteps) {
                            final ImmutablePair<RuleType, ImplicationType> nextRule = stepStep.getObject();
                            for (final RuleType rule : totalStepRules) {
                                if (!rule.isCompatible(nextRule.x) || !nextRule.x.isCompatible(rule)) {
                                    mustExportStep = true;
                                    break searchIncompatibleRule;
                                }
                            }
                        }
                    }
                }
            }
        }

        if (mustExportStep) {
            for (final Edge<ImmutablePair<RuleType, ImplicationType>, FormulaType> outEdge : outEdges) {
                final ArrayList<RuleType> totalStepRules = new ArrayList<RuleType>(stepRules);
                totalStepRules.add(outEdge.getObject().x);
                ImplicationType totalStepImplication = stepImplication;
                totalStepImplication = totalStepImplication.mult(outEdge.getObject().y);

                final ArrayList<FormulaType> totalStepFormulas = new ArrayList<FormulaType>(stepFormulas);
                totalStepFormulas.add(outEdge.getEndNode().getObject());

                final boolean isNewNode = compressedSteps.addNode(outEdge.getEndNode());

                compressedSteps.addEdge(
                    stepStartNode,
                    outEdge.getEndNode(),
                    new ImmutableTriple<ImmutableList<RuleType>, ImplicationType, ImmutableList<FormulaType>>(
                        ImmutableCreator.create(totalStepRules),
                        totalStepImplication,
                        ImmutableCreator.create(totalStepFormulas))
                );

                if (isNewNode) {
                    this.addCompressedEdges(
                        outEdge.getEndNode(),
                        outEdge.getEndNode(),
                        new ArrayList<RuleType>(),
                        Collections.singletonList(outEdge.getEndNode().getObject()),
                        ImplicationType.EQUIVALENT,
                        compressedSteps,
                        verbosityLevel);
                }
            }
        } else {
            for (final Edge<ImmutablePair<RuleType, ImplicationType>, FormulaType> outEdge : outEdges) {
                final ArrayList<RuleType> totalStepRules = new ArrayList<RuleType>(stepRules);
                totalStepRules.add(outEdge.getObject().x);
                ImplicationType totalStepImplication = stepImplication;
                totalStepImplication = totalStepImplication.mult(outEdge.getObject().y);

                final ArrayList<FormulaType> totalStepFormulas = new ArrayList<FormulaType>(stepFormulas);
                totalStepFormulas.add(outEdge.getEndNode().getObject());

                this.addCompressedEdges(
                    stepStartNode,
                    outEdge.getEndNode(),
                    totalStepRules,
                    totalStepFormulas,
                    totalStepImplication,
                    compressedSteps,
                    verbosityLevel);
            }
        }
    }
}
