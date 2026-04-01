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

/**
 * s -- e@(rel, active) --> t => s^(rel, active) >=^(rel, active) t^(rel,
 * active)
 * @author MP
 */

public class ItpfEdgeOrientation extends ItpfAtom.ItpfAtomSkeleton {

    public static ItpfEdgeOrientation create(final IEdge edge,
        final Immutable metaData,
        final RelDependency relDependency,
        final IActiveCondition activeCondition,
        final ImmutableTermSubstitution substitutionFrom,
        final ImmutableTermSubstitution substitutionTo,
        final EdgeOrientationRelation relation,
        final ItpfFactory factory) {
        return new ItpfEdgeOrientation(edge, metaData, relDependency, activeCondition, substitutionFrom,
            substitutionTo, relation, factory);
    }

    private final IActiveCondition activeCondition;
    private final RelDependency relDependency;

    private final ImmutableTermSubstitution substitutionFrom;
    private final ImmutableTermSubstitution substitutionTo;

    private final Immutable metaData;

    private final IEdge edge;
    private final EdgeOrientationRelation relation;

    private final ItpfFactory factory;
    private final int hash;

    protected ItpfEdgeOrientation(final IEdge edge, final Immutable metaData, final RelDependency relDependency,
            final IActiveCondition activeCondition, final ImmutableTermSubstitution substitutionFrom,
            final ImmutableTermSubstitution substitutionTo, final EdgeOrientationRelation rel, final ItpfFactory factory) {
        super();
        this.edge = edge;
        this.metaData = metaData;

        this.relDependency = relDependency;
        this.activeCondition = activeCondition;

        this.substitutionFrom = substitutionFrom;
        this.substitutionTo = substitutionTo;

        this.relation = rel;
        this.factory = factory;
        final int prime = 31;
        int result = 1;
        result = prime * result + rel.hashCode();
        result = prime * result + edge.hashCode();
        result = prime * result + substitutionFrom.hashCode();
        result = prime * result + relDependency.hashCode();
        result = prime * result + activeCondition.hashCode();
        result = prime * result + substitutionTo.hashCode();
        if (metaData != null) {
            result = prime * result + metaData.hashCode();
        }
        this.hash = result;
    }

    public IEdge getEdge() {
        return this.edge;
    }

    public Immutable getMetaData() {
        return this.metaData;
    }

    public ImmutableTermSubstitution getSubstitutionFrom() {
        return this.substitutionFrom;
    }

    public IActiveCondition getActiveCondition() {
        return this.activeCondition;
    }

    public RelDependency getRelDependency() {
        return this.relDependency;
    }

    /**
     * @return the substitutionTo
     */
    public ImmutableTermSubstitution getSubstitutionTo() {
        return this.substitutionTo;
    }

    /**
     * @return the relation
     */
    public EdgeOrientationRelation getRelation() {
        return this.relation;
    }

    @Override
    public ItpfAtom applySubstitution(final PolyTermSubstitution sigma) {
        final ImmutableTermSubstitution newSubstitutionFrom = this.substitutionFrom.immutableTermCompose(sigma);

        final ImmutableTermSubstitution newSubstitutionTo = this.substitutionTo.immutableTermCompose(sigma);

        if (newSubstitutionFrom != this.substitutionFrom || newSubstitutionTo != this.substitutionTo) {
            return this.factory.createEdgeOrientation(this.edge, this.metaData, this.relDependency,
                this.activeCondition, newSubstitutionFrom, newSubstitutionTo, this.relation);
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
    }

    @Override
    public void collectNodes(final Set<ImmutablePair<INode, ImmutableTermSubstitution>> nds) {
        nds.add(new ImmutablePair<INode, ImmutableTermSubstitution>(this.edge.from, this.substitutionFrom));
        nds.add(new ImmutablePair<INode, ImmutableTermSubstitution>(this.edge.to, this.substitutionTo));
    }

    @Override
    public void collectTerms(final Set<ITerm<?>> terms, final boolean collectVariables) {
    }

    @Override
    public boolean isEdgeOrientation() {
        return true;
    }

    @Override
    public YNM isTrivial() {
        return YNM.MAYBE;
    }

    @Override
    public ItpfAtom replaceAllFunctionSymbols(final FunctionSymbolReplacement replaceMap) {
        return this;
    }

    /**
     * {@inheritDoc}
     */
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
        final ItpfEdgeOrientation other = (ItpfEdgeOrientation) obj;
        if (this.activeCondition == null) {
            if (other.activeCondition != null) {
                return false;
            }
        } else if (!this.activeCondition.equals(other.activeCondition)) {
            return false;
        }
        if (this.edge == null) {
            if (other.edge != null) {
                return false;
            }
        } else if (!this.edge.equals(other.edge)) {
            return false;
        }
        if (this.metaData == null) {
            if (other.metaData != null) {
                return false;
            }
        } else if (!this.metaData.equals(other.metaData)) {
            return false;
        }
        if (this.relDependency != other.relDependency) {
            return false;
        }
        if (this.relation != other.relation) {
            return false;
        }
        if (this.substitutionFrom == null) {
            if (other.substitutionFrom != null) {
                return false;
            }
        } else if (!this.substitutionFrom.equals(other.substitutionFrom)) {
            return false;
        }
        if (this.substitutionTo == null) {
            if (other.substitutionTo != null) {
                return false;
            }
        } else if (!this.substitutionTo.equals(other.substitutionTo)) {
            return false;
        }
        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        return this.hash;
    }

    @Override
    public void export(final boolean negated,
        final StringBuilder sb,
        final Export_Util o,
        final VerbosityLevel verbosityLevel,
        final ExecutionStepColorization colors) {
        if (negated) {
            sb.append(o.notSign());
        }
        sb.append("(O ");
        this.edge.from.export(sb, o, verbosityLevel);
        if (!this.edge.fromPos.isEmptyPosition()) {
            sb.append("@");
            sb.append(this.edge.fromPos.export(o));
        }

        if (!this.substitutionFrom.isEmpty()) {
            sb.append(this.substitutionFrom.export(o));
        }
        sb.append(" ");
        sb.append(this.relation.export(o));
        sb.append(" ");
        this.edge.to.export(sb, o, verbosityLevel);
        if (!this.substitutionTo.isEmpty()) {
            sb.append(this.substitutionTo.export(o));
        }

        if (this.relDependency != RelDependency.Increasing || !this.activeCondition.isEmpty()) {
            sb.append(", @(");
            sb.append(this.relDependency.export(o));
            sb.append(", ");
            this.activeCondition.export(sb, o, verbosityLevel);
            sb.append(")");
        }

        sb.append(")");
    }

    @Override
    public Map<String, String> getXmlAttribs(final XmlExporter xe) {
        return null;
    }

    @Override
    public XmlContentsMap getXmlContents(final XmlExporter xe) {
        final XmlContentsMap contents = new XmlContentsMap();
        contents.add("edge.from", this.edge.from);
        contents.add("edge.fromPos", this.edge.fromPos);
        contents.add("substitutionFrom", this.substitutionFrom);
        contents.add("relation", this.relation);
        contents.add("edge.to", this.edge.to);
        contents.add("substitutionTo", this.substitutionTo);
        contents.add("relDependency", this.relDependency);
        contents.add("activeCondition", this.activeCondition);
        return contents;
    }
}
