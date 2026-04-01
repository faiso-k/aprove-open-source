package aprove.verification.idpframework.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.SemiRings.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Polynomials.Interpretation.ShapeHeuristics.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * Drops all existing ItpfPolyAtoms and changes the PolyInterpretation.
 * @author MP
 */
public class IDPPolyIntInterpretationSwitch extends IDPProcessor<Result, IDPProblem> implements
        Mark<Result> {

    public static enum ShapeHeuristicType {
        LINEAR, CONSTRUCTOR_SUM, QUADRATIC, COMPLEXITY_CONSTRUCTORS, ABS_LINEAR;
    }

    public static enum ShapeHeuristicSequence {
        LINEAR_SHAPE {
            @Override
            protected List<ShapeHeuristicType> getShapeChain() {
                final ArrayList<ShapeHeuristicType> shapes = new ArrayList<ShapeHeuristicType>();
                shapes.add(ShapeHeuristicType.LINEAR);
                return shapes;
            }
        }, CONSTRUCTOR_SUM_LINEAR_SHAPE {
            @Override
            protected List<ShapeHeuristicType> getShapeChain() {
                final ArrayList<ShapeHeuristicType> shapes = new ArrayList<ShapeHeuristicType>();
                shapes.add(ShapeHeuristicType.CONSTRUCTOR_SUM);
                shapes.add(ShapeHeuristicType.LINEAR);
                return shapes;
            }
        }, CONSTRUCTOR_SUM_QUADRATIC_SHAPE {
            @Override
            protected List<ShapeHeuristicType> getShapeChain() {
                final ArrayList<ShapeHeuristicType> shapes = new ArrayList<ShapeHeuristicType>();
                shapes.add(ShapeHeuristicType.CONSTRUCTOR_SUM);
                shapes.add(ShapeHeuristicType.QUADRATIC);
                return shapes;
            }
        }, COMPLEXITY_CONSTRUCTORS_LINEAR_SHAPE {
            @Override
            protected List<ShapeHeuristicType> getShapeChain() {
                final ArrayList<ShapeHeuristicType> shapes = new ArrayList<ShapeHeuristicType>();
                shapes.add(ShapeHeuristicType.COMPLEXITY_CONSTRUCTORS);
                shapes.add(ShapeHeuristicType.LINEAR);
                return shapes;
            }
        }, COMPLEXITY_CONSTRUCTORS_QUADRATIC_SHAPE {
            @Override
            protected List<ShapeHeuristicType> getShapeChain() {
                final ArrayList<ShapeHeuristicType> shapes = new ArrayList<ShapeHeuristicType>();
                shapes.add(ShapeHeuristicType.COMPLEXITY_CONSTRUCTORS);
                shapes.add(ShapeHeuristicType.QUADRATIC);
                return shapes;
            }

        }, COMPLEXITY_CONSTRUCTORS_ABS_LINEAR_SHAPE {
            @Override
            protected List<ShapeHeuristicType> getShapeChain() {
                final ArrayList<ShapeHeuristicType> shapes = new ArrayList<ShapeHeuristicType>();
                shapes.add(ShapeHeuristicType.CONSTRUCTOR_SUM);
                shapes.add(ShapeHeuristicType.ABS_LINEAR);
                return shapes;
            }

        };

        protected abstract List<ShapeHeuristicType> getShapeChain();
    }

    public static class Arguments {

        public ShapeHeuristicSequence shapes = ShapeHeuristicSequence.LINEAR_SHAPE;

        public boolean replaceExisting = false;

    }

    private final ImmutableList<ShapeHeuristicType> shapeHeuristics;
    private final boolean replaceExisting;

    @ParamsViaArgumentObject
    public IDPPolyIntInterpretationSwitch(final Arguments arguments) {
        super("IDPPolyInterpretationSwitch");
        this.shapeHeuristics = ImmutableCreator.create(arguments.shapes.getShapeChain());
        this.replaceExisting = arguments.replaceExisting;
    }

    @Override
    public boolean isIDPApplicable(final IDPProblem idp) {
        return this.replaceExisting
            || idp.getIdpGraph().getPolyInterpretation() == null;
    }

    @Override
    protected Result processIDPProblem(final IDPProblem idp,
        final Abortion aborter) throws AbortionException {

        final boolean mustSwitch =
            idp.getIdpGraph().getPolyInterpretation() != null;

        Map<INode, Itpf> newNodeConditions = null;
        Map<IEdge, Itpf> newEdgeConditions = null;

        if (mustSwitch) {
            newNodeConditions =
                this.changeToPolyLess(idp.getItpfFactory(),
                    idp.getIdpGraph().getNodeConditions());

            newEdgeConditions =
                this.changeToPolyLess(idp.getItpfFactory(),
                    idp.getIdpGraph().getEdgeConditions());
        }

        final PolyShapeHeuristic<BigInt> shapeHeuristic = this.createShapeHeuristics(idp, this.shapeHeuristics);

        final PolyInterpretation<?> newPolyInterpretation =
            PolyIntInterpretation.create(
                shapeHeuristic,
                idp.getItpfFactory(),
                idp.getIdpGraph().getFreshVarGenerator());

        final IDependencyGraph newGraph =
            idp.getIdpGraph().change(
                newNodeConditions,
                newEdgeConditions,
                null,
                newPolyInterpretation,
                null,
                this.mark);

        final IDPPolyIntInterpretationSwitchProof proof =
            new IDPPolyIntInterpretationSwitchProof(
                shapeHeuristic,
                mustSwitch);

        final IDPProblem newIdp = idp.change(newGraph);

        return ResultFactory.proved(newIdp, YNMImplication.EQUIVALENT, proof);
    }

    private PolyShapeHeuristic<BigInt> createShapeHeuristics(final IDPProblem idp, final List<ShapeHeuristicType> shapes) {
        if (shapes.size() == 1) {
            return this.createShapeHeuristic(idp, shapes.get(0));
        } else {
            final ArrayList<PolyShapeHeuristic<BigInt>> heuristics = new ArrayList<PolyShapeHeuristic<BigInt>>();
            for (final ShapeHeuristicType shapeType : shapes) {
                heuristics.add(this.createShapeHeuristic(idp, shapeType));
            }

            return new PolyShapeChain<BigInt>(ImmutableCreator.create(heuristics));
        }
    }

    private PolyShapeHeuristic<BigInt> createShapeHeuristic(final IDPProblem idp, final ShapeHeuristicType shapeType) {
        final IDependencyGraph graph = idp.getIdpGraph();
        switch (shapeType) {
        case LINEAR:
            return new PolyShapeLinear<BigInt>();
        case CONSTRUCTOR_SUM: {
            final LinkedHashSet<IFunctionSymbol<?>> constructorSymbols =
                new LinkedHashSet<IFunctionSymbol<?>>(graph.getFunctionSymbols());
            constructorSymbols.removeAll(graph.getDefinedSymbols());

            return new PolyShapeConstructorSum<BigInt>(ImmutableCreator.create(constructorSymbols));
        }
        case QUADRATIC:
            return new PolyShapeQuadratic<BigInt>();
        case COMPLEXITY_CONSTRUCTORS: {
            final LinkedHashSet<IFunctionSymbol<?>> constructorSymbols =
                new LinkedHashSet<IFunctionSymbol<?>>(graph.getFunctionSymbols());
            constructorSymbols.removeAll(graph.getDefinedSymbols());
            return new PolyShapeComplexityConstructors<BigInt>(ImmutableCreator.create(constructorSymbols), BigInt.MINUS_ONE, BigInt.ONE);
        }
        case ABS_LINEAR: {
            return new PolyShapeAbsLinear<BigInt>(idp);
        }
        }
        return null;
    }


    private <K extends Object> Map<K, Itpf> changeToPolyLess(final ItpfFactory itpfFactory,
        final ImmutableMap<K, Itpf> formulas) {
        final LinkedHashMap<K, Itpf> change = new LinkedHashMap<K, Itpf>();
        for (final Map.Entry<K, Itpf> entry : formulas.entrySet()) {
            boolean changed = false;
            final Set<ItpfConjClause> newClasues =
                new LinkedHashSet<ItpfConjClause>();
            for (final ItpfConjClause clause : entry.getValue().getClauses()) {
                final LiteralMap newLiterals = new LiteralMap();
                boolean changedClause = false;
                for (final Map.Entry<? extends ItpfAtom, Boolean> literal : clause.getLiterals().entrySet()) {
                    if (literal.getKey().isPoly()) {
                        changedClause = true;
                    } else {
                        newLiterals.put(literal.getKey(), literal.getValue());
                    }
                }
                if (changedClause) {
                    newClasues.add(itpfFactory.createClause(
                        ImmutableCreator.create(newLiterals), clause.getS()));
                    changed = true;
                } else {
                    newClasues.add(clause);
                }
            }
            if (changed) {
                change.put(entry.getKey(), itpfFactory.create(
                    entry.getValue().getQuantification(),
                    ImmutableCreator.create(newClasues)));
            }
        }
        return change;
    }

    public static class IDPPolyIntInterpretationSwitchProof extends
            DefaultProof {

        private final boolean switchedInterpretation;
        private final PolyShapeHeuristic<BigInt> defaultMode;

        public IDPPolyIntInterpretationSwitchProof(
                final PolyShapeHeuristic<BigInt> defaultMode,
                final boolean switchedInterpretation) {
            this.defaultMode = defaultMode;
            this.switchedInterpretation = switchedInterpretation;
        }

        @Override
        public final String export(final Export_Util o,
            final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            if (this.switchedInterpretation) {
                sb.append("Switched polynomial integer interpretation");
            } else {
                sb.append("Added polynomial integer interpretation");
            }
            sb.append(o.newline());
            if (level.compareTo(VerbosityLevel.LOW) > 0) {
                sb.append("Parameters: ");
                sb.append(o.cond_linebreak());
                sb.append(o.cond_linebreak());
                sb.append("ShapeHeuristic: ");
                this.defaultMode.export(sb, o, level);
                sb.append(o.cond_linebreak());
            }
            return sb.toString();
        }
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        return false;
    }

}