package aprove.verification.idpframework.Processors.NonInf;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Algorithms.UsableRules.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Itpf.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author MP
 */
public class NonInfImplicationGraph implements IDPExportable {

    private final IDependencyGraph idpGraph;
    private final CollectionMap<Itpf, IEdge> implicationToEdges;
    private final IDPSubGraph subGraph;

    public NonInfImplicationGraph(final IDPProblem idp,
            final IDPSubGraph subGraph) {
        this.implicationToEdges = new CollectionMap<Itpf, IEdge>();
        this.idpGraph = idp.getIdpGraph();
        this.subGraph = subGraph;

        final ItpfFactory itpfFactory = this.idpGraph.getItpfFactory();

        for (final IEdge edge : subGraph.getEdges()) {
            final Itpf edgeCondition = this.idpGraph.getCondition(edge);

            Itpf precondition =
                itpfFactory.createAnd(this.idpGraph.getCondition(edge.from),
                    edgeCondition);

            final ImmutableTermSubstitution toSubstitution;
            if (edge.from.equals(edge.to)) {
                final VarRenaming loopSubstitution =
                    this.idpGraph.getLoopRenaming(edge.to);
                toSubstitution = ISubstitution.create(loopSubstitution.getMap());
                precondition =
                    itpfFactory.createAnd(
                        precondition,
                        this.idpGraph.getCondition(edge.to).applySubstitution(
                            loopSubstitution));
            } else {
                toSubstitution = ISubstitution.emptySubstitution();
                precondition =
                    itpfFactory.createAnd(precondition,
                        this.idpGraph.getCondition(edge.to));
            }

            final ImmutableList<ItpfQuantor> quantifications =
                ImmutableCreator.create(ItpfUtil.invertQuantors(itpfFactory, precondition.getQuantification()));

            for (final ItpfConjClause preconditionClause : precondition.getClauses()) {
                final LiteralMap conclusionLiterals = new LiteralMap();
                conclusionLiterals.put(itpfFactory.createEdgeOrientation(edge,
                    preconditionClause,
                    RelDependency.Increasing, IActiveCondition.EMPTY_CONDITION,
                    ISubstitution.emptySubstitution(), toSubstitution,
                    EdgeOrientationRelation.ABSTRACT_WEAK_GT), true);

                conclusionLiterals.put(itpfFactory.createEdgeOrientation(edge,
                    preconditionClause,
                    RelDependency.Increasing, IActiveCondition.EMPTY_CONDITION,
                    ISubstitution.emptySubstitution(), toSubstitution,
                    EdgeOrientationRelation.ABSTRACT_WEAK_BOUND), true);

                final Itpf conclusion =
                    itpfFactory.create(itpfFactory.createClause(
                        ImmutableCreator.create(conclusionLiterals),
                        ITerm.EMPTY_SET));

                this.implicationToEdges.add(
                    itpfFactory.create(quantifications, itpfFactory.createClause(
                        itpfFactory.createImplication(itpfFactory.create(preconditionClause),
                            conclusion), true, ITerm.EMPTY_SET)), edge);
            }
        }
    }

    public CollectionMap<Itpf, IEdge> getImplications() {
        return this.implicationToEdges;
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
    public void export(final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel) {
        for (final Entry<Itpf, Collection<IEdge>> implication : this.implicationToEdges.entrySet()) {
            implication.getKey().export(sb, o, verbosityLevel);
            sb.append(o.linebreak());

            if (!implication.getValue().isEmpty()) {
                final StringBuilder indent = new StringBuilder();
                final Iterator<IEdge> implicationsIterator =
                    implication.getValue().iterator();
                while (implicationsIterator.hasNext()) {
                    final IEdge edge = implicationsIterator.next();

                    sb.append(edge.type.export(o));
                    sb.append(": (");
                    sb.append(edge.from.id);
                    sb.append(")");
                    if (!edge.fromPos.isEmptyPosition()) {
                        sb.append("@");
                        sb.append(edge.fromPos.export(o));
                    }
                    sb.append(" -> (");
                    sb.append(edge.to.id);
                    sb.append(")");

                    if (edge.from.equals(edge.to)) {
                        sb.append(this.idpGraph.getLoopRenaming(edge.from).export(o));
                    }

                    if (implicationsIterator.hasNext()) {
                        sb.append(o.linebreak());
                    }
                }
                sb.append(o.indent(indent.toString()));
                sb.append(o.linebreak());
            }
        }

        sb.append(o.cond_linebreak());
    }

    /**
     * @return the edges
     */
    public IDPSubGraph getSubGraph() {
        return this.subGraph;
    }

}
