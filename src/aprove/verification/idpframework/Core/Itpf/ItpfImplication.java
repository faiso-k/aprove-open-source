package aprove.verification.idpframework.Core.Itpf;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * @author MP
 */
public class ItpfImplication extends ItpfAtom.ItpfAtomSkeleton implements ProcessableFormula {

    static ItpfImplication create(final Itpf precondition,
        final Itpf conclusion,
        final ItpfFactory factory) {
        return new ItpfImplication(precondition, conclusion, factory);
    }

    private final Itpf precondition;
    private final Itpf conclusion;
    private final ItpfFactory factory;

    private volatile ImmutableSet<IVariable<?>> freeVariables;
    private volatile ImmutableSet<ImmutablePair<INode, ImmutableTermSubstitution>> nodes;
    private final int hashCode;

    public ItpfImplication(final Itpf precondition, final Itpf conclusion, final ItpfFactory factory) {
        if (Globals.useAssertions) {
            assert precondition.getQuantification().isEmpty() && conclusion.getQuantification().isEmpty() : "do not add quantifications inside implications";
        }
        this.precondition = precondition;
        this.conclusion = conclusion;
        this.factory = factory;

        final int prime = 31;
        this.hashCode = (prime + conclusion.hashCode()) * prime + precondition.hashCode();
    }

    public Itpf getConclusion() {
        return this.conclusion;
    }

    public Itpf getPrecondition() {
        return this.precondition;
    }

    @Override
    public boolean isImplication() {
        return true;
    }

    @Override
    public YNM isTrivial() {
        if (this.precondition.isFalse() || this.conclusion.isTrue()) {
            return YNM.YES;
        } else if (this.precondition.isTrue() && this.conclusion.isFalse()) {
            return YNM.NO;
        } else {
            return YNM.MAYBE;
        }
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof ItpfImplication)) {
            return false;
        }
        final ItpfImplication other = (ItpfImplication) obj;

        return this.precondition.equals(other.precondition) && this.conclusion.equals(other.conclusion);
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
        sb.append("(");
        this.precondition.export(sb, o, verbosityLevel, colors);
        sb.append(" ");
        sb.append(o.implication());
        sb.append(" ");
        this.conclusion.export(sb, o, verbosityLevel, colors);
        sb.append(")");
    }

    @Override
    public Map<String, String> getXmlAttribs(XmlExporter xe) {
        return null;
    }

    @Override
    public XmlContentsMap getXmlContents(XmlExporter xe) {
        XmlContentsMap contents = new XmlContentsMap();
        contents.add("precondition", this.precondition);
        contents.add("conclusion", this.conclusion);
        return contents;
    }

    @Override
    public Set<IVariable<?>> getFreeVariables() {
        if (this.freeVariables == null) {
            synchronized (this) {
                if (this.freeVariables == null) {
                    final Set<IVariable<?>> vars = new LinkedHashSet<IVariable<?>>();
                    vars.addAll(this.precondition.getFreeVariables());
                    vars.addAll(this.conclusion.getFreeVariables());
                    return this.freeVariables = ImmutableCreator.create(vars);
                }
            }
        }
        return this.freeVariables;
    }

    @Override
    public ImmutableSet<ImmutablePair<INode, ImmutableTermSubstitution>> getNodes() {
        if (this.nodes == null) {
            synchronized (this) {
                if (this.nodes == null) {
                    final Set<ImmutablePair<INode, ImmutableTermSubstitution>> nds = new LinkedHashSet<ImmutablePair<INode, ImmutableTermSubstitution>>();
                    this.collectNodes(nds);
                    return this.nodes = ImmutableCreator.create(nds);
                }
            }
        }
        return this.nodes;
    }

    @Override
    public ItpfImplication applySubstitution(final PolyTermSubstitution sigma) {
        final Itpf newPrecondition = this.precondition.applySubstitution(sigma);
        final Itpf newConclusion = this.conclusion.applySubstitution(sigma);

        if (this.precondition != newPrecondition || this.conclusion != newConclusion) {
            return this.factory.createImplication(newPrecondition, newConclusion);
        } else {
            return this;
        }
    }

    @Override
    public void collectExecutionMarks(final Map<ExecutionUid, ExecutionMarkable> executionMarks) {
        this.executionMarksHandler.collectExecutionMarks(executionMarks);
        this.precondition.collectExecutionMarks(executionMarks);
        this.conclusion.collectExecutionMarks(executionMarks);
    }

    @Override
    public void collectFunctionSymbols(final Set<IFunctionSymbol<?>> fss) {
        fss.addAll(this.precondition.getFunctionSymbols());
        fss.addAll(this.conclusion.getFunctionSymbols());
    }

    @Override
    public void collectVariables(final Set<IVariable<?>> vars) {
        vars.addAll(this.precondition.getVariables());
        vars.addAll(this.conclusion.getVariables());
    }

    @Override
    public void collectNodes(final Set<ImmutablePair<INode, ImmutableTermSubstitution>> nds) {
        nds.addAll(this.precondition.getNodes());
        nds.addAll(this.conclusion.getNodes());
    }

    @Override
    public void collectTerms(final Set<ITerm<?>> terms, final boolean dropVars) {
        terms.addAll(this.precondition.getTerms(dropVars));
        terms.addAll(this.conclusion.getTerms(dropVars));
    }

    @Override
    public ItpfAtom replaceAllFunctionSymbols(final FunctionSymbolReplacement replaceMap) {
        final Itpf newPrecondition = this.precondition.replaceAllFunctionSymbols(replaceMap);
        final Itpf newConclusion = this.conclusion.replaceAllFunctionSymbols(replaceMap);

        if (this.precondition != newPrecondition || this.conclusion != newConclusion) {
            return this.factory.createImplication(newPrecondition, newConclusion);
        } else {
            return this;
        }
    }

}
