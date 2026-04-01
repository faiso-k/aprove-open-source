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

public class ItpfNodeUra extends ItpfAbstractUra {

    public static ItpfNodeUra create(final IUsableRulesEstimation eu,
        final RelDependency k,
        final INode node,
        final ImmutableTermSubstitution substitution,
        final ItpRelation rel,
        final ItpfFactory factory) {
        return new ItpfNodeUra(eu, k, node, substitution, rel, factory);
    }

    private final INode node;
    protected final ImmutableTermSubstitution substitution;
    private final int hash;

    protected ItpfNodeUra(final IUsableRulesEstimation eu, final RelDependency k,
            final INode node, final ImmutableTermSubstitution substitution,
            final ItpRelation rel, final ItpfFactory factory) {
        super(eu, k, rel, factory);
        this.node = node;
        this.substitution = substitution;

        final int prime = 31;
        int result = 1;
        result = prime * result + ((eu == null) ? 0 : eu.hashCode());
        result = prime * result + k.hashCode();
        result = prime * result + rel.hashCode();
        result = prime * result + node.hashCode();
        result = prime * result + substitution.hashCode();
        this.hash = result;
    }

    @Override
    public ItpfAtom applySubstitution(final PolyTermSubstitution sigma) {
        final ImmutableTermSubstitution newSubstitution = this.substitution.immutableTermCompose(sigma);

        if (newSubstitution != this.substitution) {
            return this.factory.createNodeUra(this.usableRulesEstimation, this.relDependency, this.node, newSubstitution, this.relation);
        } else {
            return this;
        }
    }

    @Override
    public ItpfAtom replaceAllFunctionSymbols(final FunctionSymbolReplacement replaceMap) {
        final ImmutableTermSubstitution newSubstitution = this.substitution.replaceAllFunctionSymbols(replaceMap);

        if (newSubstitution != this.substitution) {
            return this.factory.createNodeUra(this.usableRulesEstimation, this.relDependency, this.node, newSubstitution, this.relation);
        } else {
            return this;
        }
    }

    @Override
    public void collectFunctionSymbols(final Set<IFunctionSymbol<?>> fss) {
    }

    @Override
    public void collectExecutionMarks(final Map<ExecutionUid, ExecutionMarkable> executionMarks) {
        this.executionMarksHandler.collectExecutionMarks(executionMarks);
    }

    @Override
    public void collectVariables(final Set<IVariable<?>> vars) {
        vars.addAll(this.substitution.getTermDomain());
        vars.addAll(this.substitution.getTermVariablesInCodomain());
    }

    @Override
    public void collectNodes(final Set<ImmutablePair<INode, ImmutableTermSubstitution>> nds) {
        nds.add(new ImmutablePair<INode, ImmutableTermSubstitution>(this.node, this.substitution));
    }

    @Override
    public void collectTerms(final Set<ITerm<?>> terms, final boolean dropVars) {
    }

    @Override
    public boolean isNodeUra() {
        return true;
    }

    @Override
    public YNM isTrivial() {
        return YNM.MAYBE;
    }

    public INode getNode() {
        return this.node;
    }

    public ImmutableTermSubstitution getSubstitution() {
        return this.substitution;
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
        final ItpfNodeUra other = (ItpfNodeUra) obj;
        return this.relDependency == other.relDependency && this.relation == other.relation && this.node.equals(other.node) && this.substitution.equals(other.getSubstitution())
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
        sb.append(this.node.export(o));
        if (!this.getSubstitution().isEmpty()) {
            sb.append(" ");
            sb.append(this.getSubstitution().export(o));
        }
        sb.append(", ");
        sb.append(this.getRelation().export(o));
        sb.append(")");
    }

    @Override
    public XmlContentsMap getXmlContents(XmlExporter xe) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Map<String, String> getXmlAttribs(XmlExporter xe) {
        // TODO Auto-generated method stub
        return null;
    }
}
