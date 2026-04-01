/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.idpframework.Core.Itpf;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.BasicStructures.*;
import aprove.verification.idpframework.Core.BasicStructures.Substitutions.*;
import aprove.verification.idpframework.Core.IDPGraph.*;
import aprove.verification.idpframework.Core.Utility.*;
import aprove.verification.idpframework.Core.Utility.Marking.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * An Itpf formula has always pr�nex normal DNF.
 * @author Martin Pluecker
 */
public abstract class Itpf extends QuantifiedDisjunction<ItpfConjClause> implements
        Exportable, XmlExportable, ProcessableFormula, Immutable,
        SelfMarkable<ExecutionResult<Conjunction<Itpf>, Itpf>, Itpf>, HasVariables<IVariable<?>>,
        ExecutionMarkable {

    private final MarksHandler<ExecutionResult<Conjunction<Itpf>, Itpf>, Itpf, Itpf> marks;
    protected final int hashCode;
    protected final ExecutionMarksHandler executionMarksHandler;

    public Itpf(final ImmutableList<ItpfQuantor> quantors, final ImmutableSet<ItpfConjClause> clauses) {
        super(quantors, clauses);
        this.marks =
            new MarksHandler<ExecutionResult<Conjunction<Itpf>, Itpf>, Itpf, Itpf>(
                this);
        this.executionMarksHandler = new ExecutionMarksHandler(this);
        final int prime = 37;
        this.hashCode = prime * (prime + quantors.hashCode()) + clauses.hashCode();
    }

    @Override
    public ImmutableSet<ItpfConjClause> asCollection() {
        return (ImmutableSet<ItpfConjClause>) this.items;
    }

    public final Itpf applySubstitution(final PolyTermSubstitution sigma) {
        return this.applySubstitution(sigma, false);
    }

    public final <T extends ITerm<?>> Itpf applySubstitution(final PolyTermSubstitution sigma,
        final boolean substituteBoundVariables) {
        PolyTermSubstitution usedSigma;
        if (substituteBoundVariables) {
            usedSigma = sigma;
        } else {
            usedSigma =
                NonBoundPolyTermSubstitution.create(sigma, this.getBoundVariables());
        }

        if (usedSigma.isEmpty()) {
            return this;
        } else {
            return this.applySubstitutionNoCheck(usedSigma, substituteBoundVariables);
        }
    }

    @Override
    public MarksHandler<ExecutionResult<Conjunction<Itpf>, Itpf>, Itpf, Itpf> getMarks() {
        return this.marks;
    }

    @Override
    public void addExecutionMark(final ExecutionUid mark) {
        this.executionMarksHandler.addExecutionMark(mark);
    }

    @Override
    public boolean isExecutionMarked(final ExecutionUid mark) {
        return this.executionMarksHandler.isExecutionMarked(mark);
    }

    @Override
    public Set<ExecutionUid> getExecutionMarks() {
        return this.executionMarksHandler.getExecutionMarks();
    }

    /**
     * @param usedSigma already removed all bound variables from substitution
     * @param substituteBoundVariables
     * @return
     */
    protected abstract <T extends ITerm<?>> Itpf applySubstitutionNoCheck(final PolyTermSubstitution sigma,
        final boolean substituteBoundVariables);

    public abstract ImmutableSet<IVariable<?>> getBoundVariables();

    public abstract ImmutableSet<ItpfConjClause> getClauses();

    @Override
    public abstract ImmutableSet<IVariable<?>> getVariables();

    @Override
    public abstract ImmutableSet<ImmutablePair<INode, ImmutableTermSubstitution>> getNodes();

    public abstract ImmutableSet<ITerm<?>> getTerms(boolean dropVars);

    @Override
    public abstract ImmutableSet<IVariable<?>> getFreeVariables();

    public abstract ImmutableSet<IFunctionSymbol<?>> getFunctionSymbols();

    public abstract Itpf replaceAllFunctionSymbols(FunctionSymbolReplacement replaceMap);

    public abstract Itpf getQuantorfree();

    public abstract boolean isFalse();

    public abstract boolean isTrue();

    @Override
    public final void export(final StringBuilder sb, final Export_Util o, final VerbosityLevel verbosityLevel) {
        this.export(sb, o, verbosityLevel, ExecutionStepColorization.EMPTY);
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (obj instanceof Itpf) {
            final Itpf other = (Itpf) obj;
            if (other.hashCode != this.hashCode) {
                return false;
            }
            if (!this.getQuantification().equals(other.getQuantification())) {
                return false;
            }
            if (!this.getClauses().equals(other.getClauses())) {
                return false;
            }
            return true;
        } else {
            return false;
        }
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }


}
