/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Core.Itpf;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Algorithms.UsableRules.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Polynomials.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class ItpfEdgeUra extends ItpfAbstractUra {

    public static ItpfEdgeUra create(final IUsableRulesEstimation eu,
        final RelDependency k,
        final IActiveCondition activeCondition,
        final IEdge edge,
        final ImmutableTermSubstitution substitution,
        final ItpRelation rel,
        final ItpfFactory factory) {
        return new ItpfEdgeUra(eu, k, activeCondition, edge, substitution, rel,
            factory);
    }

    private final IActiveCondition activeCondition;
    private final IEdge edge;
    protected final ImmutableTermSubstitution substitution;
    private final int hash;

    protected ItpfEdgeUra(final IUsableRulesEstimation eu,
            final RelDependency relDependency, final IActiveCondition activeCondition,
            final IEdge edge, final ImmutableTermSubstitution substitution,
            final ItpRelation rel, final ItpfFactory factory) {
        super(eu, relDependency, rel, factory);
        this.activeCondition = activeCondition;
        this.edge = edge;
        this.substitution = substitution;

        final int prime = 37;
        int result = 1;
        result = prime * result + ((eu == null) ? 0 : eu.hashCode());
        result = prime * result + relDependency.hashCode();
        result = prime * result + activeCondition.hashCode();
        result = prime * result + rel.hashCode();
        result = prime * result + edge.hashCode();
        result = prime * result + substitution.hashCode();
        this.hash = result;
    }

    @Override
    public ItpfAtom applySubstitution(final PolyTermSubstitution sigma) {
        final ImmutableTermSubstitution newSubstitution =
            this.substitution.immutableTermCompose(sigma);

        if (newSubstitution != this.substitution) {
            return this.factory.createEdgeUra(this.usableRulesEstimation, this.relDependency, this.activeCondition,
                this.edge, newSubstitution, this.relation);
        } else {
            return this;
        }
    }

    @Override
    public ItpfAtom replaceAllFunctionSymbols(final FunctionSymbolReplacement replaceMap) {
        final ImmutableTermSubstitution newSubstitution =
            this.substitution.replaceAllFunctionSymbols(replaceMap);

        if (newSubstitution != this.substitution) {
            return this.factory.createEdgeUra(this.usableRulesEstimation, this.relDependency, this.activeCondition,
                this.edge, newSubstitution, this.relation);
        } else {
            return this;
        }
    }

    @Override
    public void collectExecutionMarks(final Map<ExecutionUid, ExecutionMarkable> executionMarks) {
        this.executionMarksHandler.collectExecutionMarks(executionMarks);
    }

    @Override
    public void collectFunctionSymbols(final Set<IFunctionSymbol<?>> fss) {
    }

    @Override
    public void collectVariables(final Set<IVariable<?>> vars) {
        vars.addAll(this.substitution.getTermDomain());
        vars.addAll(this.substitution.getTermVariablesInCodomain());
    }

    @Override
    public void collectNodes(final Set<ImmutablePair<INode, ImmutableTermSubstitution>> nds) {
        nds.add(new ImmutablePair<INode, ImmutableTermSubstitution>(this.edge.from,
            this.substitution));
        nds.add(new ImmutablePair<INode, ImmutableTermSubstitution>(this.edge.to,
                this.substitution));
    }

    @Override
    public void collectTerms(final Set<ITerm<?>> terms, final boolean dropVars) {
    }

    @Override
    public boolean isEdgeUra() {
        return true;
    }

    @Override
    public YNM isTrivial() {
        return YNM.MAYBE;
    }

    public IEdge getEdge() {
        return this.edge;
    }

    public ImmutableTermSubstitution getSubstitution() {
        return this.substitution;
    }

    public IActiveCondition getActiveCondition() {
        return this.activeCondition;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final ItpfEdgeUra other = (ItpfEdgeUra) obj;
        return this.relDependency == other.relDependency
            && this.relation == other.relation
            && this.edge.equals(other.edge)
            && this.substitution.equals(other.getSubstitution())
            && this.activeCondition.equals(other.activeCondition)
            && (this.usableRulesEstimation == other.usableRulesEstimation || (this.usableRulesEstimation != null && this.usableRulesEstimation.equals(other.usableRulesEstimation)));
    }

    @Override
    public int hashCode() {
        return this.hash;
    }

    @Override
    public void export(final boolean negated,
        final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel, final ExecutionStepColorization colors) {
        if (negated) {
            sb.append(o.notSign());
        }
        sb.append("(U");
        if (this.relDependency != RelDependency.Increasing) {
            sb.append(o.sup(this.relDependency.export(o)));
        }
        sb.append(", ");
        sb.append(this.edge.export(o));
        if (!this.getSubstitution().isEmpty()) {
            sb.append(" ");
            sb.append(this.getSubstitution().export(o));
        }
        sb.append(", ");
        sb.append(this.getRelation().export(o));
        sb.append(")");
    }

    @Override
    public Map<String, String> getXmlAttribs(XmlExporter eu) {
        return null;
    }

    @Override
    public XmlContentsMap getXmlContents(XmlExporter xe) {
        return null;
    }
}
