/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.idpGraph;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class VariableRenamedPath implements Exportable, IDPExportable, VerbosityExportable {

    public static VariableRenamedPath create (List<Node> nodes) {
        if (nodes.isEmpty()) {
            return new VariableRenamedPath(ImmutableCreator.create(Collections.<ImmutablePair<Node, ImmutableMap<TRSVariable, TRSVariable>>>emptyList()));
        }
        List<ImmutablePair<Node, ImmutableMap<TRSVariable, TRSVariable>>> res = new ArrayList<ImmutablePair<Node, ImmutableMap<TRSVariable, TRSVariable>>>(nodes.size());
        // first node as is
        Iterator<Node> iter = nodes.iterator();
        Node first = iter.next();
        res.add(new ImmutablePair<Node, ImmutableMap<TRSVariable, TRSVariable>> (first, ImmutableCreator.create(Collections.<TRSVariable, TRSVariable>emptyMap())));
        FreshNameGenerator freshNames = new FreshNameGenerator(first.rule.getVariables(), FreshNameGenerator.PROLOG_VARS);
        while (iter.hasNext()) {
            Node node = iter.next();
            Set<TRSVariable> ruleVars = node.rule.getVariables();
            Map<TRSVariable, TRSVariable> subst = new LinkedHashMap<TRSVariable, TRSVariable>();
            for (TRSVariable v : ruleVars) {
                String newName = freshNames.getFreshName(v.getName(), false);
                if (!newName.equals(v.getName())) {
                    subst.put(v, TRSTerm.createVariable(newName));
                }
            }
            res.add(new ImmutablePair<Node, ImmutableMap<TRSVariable, TRSVariable>> (node, ImmutableCreator.create(subst)));
        }
        return VariableRenamedPath.create(ImmutableCreator.create(res));
    }

    public static VariableRenamedPath create(ImmutableList<ImmutablePair<Node, ImmutableMap<TRSVariable, TRSVariable>>> path) {
        if (Globals.useAssertions) {
            Set<TRSVariable> used = new LinkedHashSet<TRSVariable>();
            for (ImmutablePair<Node, ImmutableMap<TRSVariable, TRSVariable>> p : path) {
                Set<TRSVariable> ruleVars = p.x.rule.getVariables();
                for (TRSVariable x : ruleVars) {
                    TRSVariable y = p.y.get(x);
                    if (y == null) {
                        y = x;
                    }
                    assert(used.add((TRSVariable)y)) : "suplicate use of variable";
                }
            }
        }
        return new VariableRenamedPath(path);
    }

    private final ImmutableList<ImmutablePair<Node, ImmutableMap<TRSVariable, TRSVariable>>> path;

    private VariableRenamedPath(ImmutableList<ImmutablePair<Node, ImmutableMap<TRSVariable, TRSVariable>>> path) {
        this.path = path;
    }

    public ImmutableList<ImmutablePair<Node, ImmutableMap<TRSVariable, TRSVariable>>> getPath() {
        return this.path;
    }

    @Override
    public String export(Export_Util o) {
        return this.export(o, VerbosityLevel.MIDDLE);
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {
        return this.export(o, null, level);
    }

    @Override
    public String export(Export_Util o, IDPPredefinedMap predefinedMap,
            VerbosityLevel verbosityLevel) {
        StringBuilder sb = new StringBuilder();
        Iterator<ImmutablePair<Node, ImmutableMap<TRSVariable, TRSVariable>>> iter = this.path.iterator();
        while (iter.hasNext()) {
            ImmutablePair<Node, ImmutableMap<TRSVariable, TRSVariable>> nodeSubst = iter.next();
            sb.append(nodeSubst.x.export(o, predefinedMap, verbosityLevel));
            if (!nodeSubst.y.isEmpty()) {
                sb.append("[");
                for (Map.Entry<TRSVariable, TRSVariable> entry : nodeSubst.y.entrySet()) {
                    sb.append(IDPExport.exportTerm(entry.getKey(), o, predefinedMap));
                    sb.append(" / ");
                    sb.append(IDPExport.exportTerm(entry.getValue(), o, predefinedMap));
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
        return sb.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }
}
