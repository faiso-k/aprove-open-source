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
 *
 * @author MP
 */
public class ItpfTermUra extends ItpfAbstractUra {

    public static ItpfTermUra create(final IUsableRulesEstimation eu,
        final RelDependency k,
        final IActiveCondition activeCondition,
        final ITerm<?> term,
        final ItpRelation rel,
        final ItpfFactory factory) {
        return new ItpfTermUra(eu, k, activeCondition, term, rel, factory);
    }

    private final ITerm<?> term;
    private final IActiveCondition activeContext;
    private final int hash;

    private ItpfTermUra(final IUsableRulesEstimation eu, final RelDependency k, final IActiveCondition activeCondition,
            final ITerm<?> term, final ItpRelation rel, final ItpfFactory factory) {
        super(eu, k, rel, factory);
        this.term = term;
        this.activeContext = activeCondition;

        final int prime = 17;
        int result = 1;
        result = prime * result + ((eu == null) ? 0 : eu.hashCode());
        result = prime * result + k.hashCode();
        result = prime * result + activeCondition.hashCode();
        result = prime * result + rel.hashCode();
        result = prime * result + term.hashCode();
        this.hash = result;
    }

    @Override
    public boolean isTermUra() {
        return true;
    }

    public IActiveCondition getActiveContext() {
        return this.activeContext;
    }

    public ITerm<?> getTerm() {
        return this.term;
    }

    @Override
    public ItpfTermUra applySubstitution(final PolyTermSubstitution sigma) {
        final ITerm<?> newTerm = this.term.applySubstitution(sigma);
        if (!newTerm.equals(this.term)) {
            return this.factory.createTermUra(this.usableRulesEstimation, this.relDependency, this.activeContext, newTerm, this.relation);
        } else {
            return this;
        }
    }

    @Override
    public void collectFunctionSymbols(final Set<IFunctionSymbol<?>> fss) {
        this.term.collectFunctionSymbols(fss);
    }

    @Override
    public ItpfAtom replaceAllFunctionSymbols(final FunctionSymbolReplacement replaceMap) {
        final ITerm<?> newTerm = this.term.replaceAllFunctionSymbols(replaceMap);
        final IActiveCondition newContext = this.activeContext.replaceFunctionSymbols(replaceMap);
        if (!newTerm.equals(this.term) || !newContext.equals(this.activeContext)) {
            return this.factory.createTermUra(this.usableRulesEstimation, this.relDependency, newContext, newTerm, this.relation);
        } else {
            return this;
        }
    }

    @Override
    public void collectExecutionMarks(final Map<ExecutionUid, ExecutionMarkable> executionMarks) {
        this.executionMarksHandler.collectExecutionMarks(executionMarks);
    }

    @Override
    public void collectVariables(final Set<IVariable<?>> vars) {
        this.term.collectVariables(vars);
    }

    @Override
    public void collectNodes(final Set<ImmutablePair<INode, ImmutableTermSubstitution>> nds) {
        // nothing to do here
    }

    @Override
    public void collectTerms(final Set<ITerm<?>> terms, final boolean dropVars) {
        if (!this.term.isVariable() || !dropVars) {
            terms.add(this.term);
        }
    }

    @Override
    public YNM isTrivial() {
        return YNM.MAYBE;
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
        final ItpfTermUra other = (ItpfTermUra) obj;
        return this.relDependency == other.relDependency && this.activeContext.equals(other.activeContext) && this.relation == other.relation && this.term.equals(other.term)
            && (this.usableRulesEstimation == other.usableRulesEstimation || (this.usableRulesEstimation != null && this.usableRulesEstimation.equals(other.usableRulesEstimation)));
    }


    @Override
    public int hashCode() {
        return this.hash;
    }

    @Override
    public void export(final boolean negated,
        final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel, final ExecutionStepColorization colors) {
        if (negated) {
            sb.append(eu.notSign());
        }
        sb.append("(U");
        if (this.relDependency != RelDependency.Increasing) {
            sb.append(eu.sup(this.relDependency.export(eu)));
        }
        sb.append(", ");
        this.term.export(sb, eu, verbosityLevel);
        sb.append(", ");
        sb.append(this.getRelation().export(eu));
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
