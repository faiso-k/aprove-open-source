/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Core.IDPGraph;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.FreshVarGenerator;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class VariableRenamedPath implements Exportable, IDPExportable,
        VerbosityExportable {

    public static final VariableRenamedPath EMPTY_PATH = new VariableRenamedPath(
        ImmutableCreator.create(Collections.<ImmutablePair<IEdge, VarRenaming>> emptyList()));

    public static VariableRenamedPath create(final IDependencyGraph graph,
        final ImmutableList<ImmutablePair<IEdge, VarRenaming>> path) {
        if (Globals.useAssertions) {
            if (!path.isEmpty()) {
                final Set<IVariable<?>> used =
                    new LinkedHashSet<IVariable<?>>(graph.getTerm(
                        path.get(0).x.from).getVariables());
                INode lastNode = null;
                for (final ImmutablePair<IEdge, VarRenaming> p : path) {
                    if (lastNode != null) {
                        if (Globals.useAssertions) {
                            assert lastNode.equals(p.x.from) : "invalid path";
                        }
                    }
                    lastNode = p.x.to;

                    if (Globals.useAssertions) {
                        final Set<IVariable<?>> ruleVars =
                            graph.getTerm(p.x.to).getVariables();

                        final HashSet<IVariable<?>> renamedRuleVars = new HashSet<IVariable<?>>();
                        for (final IVariable<?> x : ruleVars) {
                            renamedRuleVars.add(x.applyVarSubstitution(p.y));
                        }

                        for (final IVariable<?> x : renamedRuleVars) {
                            assert (used.add(x)) : "duplicate use of variable";
                        }
                    }
                }
            }
        }
        return new VariableRenamedPath(path);
    }

    public static VariableRenamedPath create(final IDependencyGraph graph,
        final List<IEdge> path) {
        if (path.isEmpty()) {
            return VariableRenamedPath.EMPTY_PATH;
        }

        // first node as is
        final FreshVarGenerator freshNames =
            new FreshVarGenerator(
                graph.getTerm(path.get(0).from).getVariables());

        return VariableRenamedPath.create(graph, freshNames, path);
    }

    public static VariableRenamedPath create(final IDependencyGraph graph,
        final FreshVarGenerator freshNames,
        final List<IEdge> path) {

        if (path.isEmpty()) {
            return VariableRenamedPath.EMPTY_PATH;
        }
        final List<ImmutablePair<IEdge, VarRenaming>> res =
            new ArrayList<ImmutablePair<IEdge, VarRenaming>>(
                path.size());

        INode lastNode = null;
        for (final IEdge edge : path) {
            if (Globals.useAssertions) {
                assert lastNode == null || lastNode.equals(edge.from) : "invalid path";
            }
            lastNode = edge.to;
            final VarRenaming substitution = ItpfUtil.getVariableRenaming(graph.getPolyFactory(), graph.getTerm(edge.to).getVariables(), freshNames);

            res.add(new ImmutablePair<IEdge, VarRenaming>(edge,
                    substitution));
        }
        return VariableRenamedPath.create(graph, ImmutableCreator.create(res));
    }

    private final ImmutableList<ImmutablePair<IEdge, VarRenaming>> path;

    private VariableRenamedPath(
            final ImmutableList<ImmutablePair<IEdge, VarRenaming>> path) {
        this.path = path;
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
        final Export_Util o, final VerbosityLevel verbosityLevel) {
        final Iterator<ImmutablePair<IEdge, VarRenaming>> iter =
            this.path.iterator();
        while (iter.hasNext()) {
            final ImmutablePair<IEdge, VarRenaming> nodeSubst =
                iter.next();
            nodeSubst.x.export(sb, o, verbosityLevel);
            if (!nodeSubst.y.isEmpty()) {
                sb.append("[");
                for (final Map.Entry<IVariable<?>, ? extends IVariable<?>> entry : nodeSubst.y.getMap().entrySet()) {
                    sb.append(entry.getKey().export(o));
                    sb.append(" / ");
                    sb.append(entry.getValue().export(o));
                    sb.append(", ");
                }
                sb.setLength(sb.length() - 2);
                sb.append("]");
            }
            if (iter.hasNext()) {
                sb.append(" ");
                sb.append(o.rightarrow());
                sb.append(" ");
            }
        }
        sb.setLength(sb.length() - 3);
    }

    public ImmutableList<ImmutablePair<IEdge, VarRenaming>> getPath() {
        return this.path;
    }

}
