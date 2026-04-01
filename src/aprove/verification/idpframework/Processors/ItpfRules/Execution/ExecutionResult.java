package aprove.verification.idpframework.Processors.ItpfRules.Execution;

import java.util.*;

import aprove.verification.idpframework.Core.Utility.Marking.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class ExecutionResult<C extends MarkContent<C, FormulaType>, FormulaType>
    implements
        MarkContent<ExecutionResult<C, FormulaType>, FormulaType>,
        Immutable
{

    public final C result;
    public final ImplicationType implication;
    public final ApplicationMode usedApplications;
    public final boolean fixpointReached;

    public ExecutionResult(
        final C result,
        final ImplicationType implication,
        final ApplicationMode usedApplications,
        final boolean fixpointReached)
    {
        this.result = result;
        this.implication = implication;
        this.usedApplications = usedApplications;
        this.fixpointReached = fixpointReached;
    }

    public ExecutionResult<C, FormulaType> increaseUsedApplications(
        final ApplicationMode usedApplications,
        final boolean fixpointReached)
    {
        return new ExecutionResult<C, FormulaType>(
            this.result,
            this.implication,
            this.usedApplications.increaseBy(usedApplications),
            this.fixpointReached && fixpointReached);
    }

    public ExecutionResult<C, FormulaType> setUsedApplications(
        final ApplicationMode usedApplications,
        final boolean fixpointReached)
    {
        return new ExecutionResult<C, FormulaType>(
            this.result,
            this.implication,
            usedApplications,
            this.fixpointReached && fixpointReached);
    }

    public ExecutionResult<C, FormulaType> multImplication(final ImplicationType implication) {
        return new ExecutionResult<C, FormulaType>(
            this.result,
            this.implication.mult(implication),
            this.usedApplications,
            this.fixpointReached);
    }

    @Override
    public Iterator<FormulaType> iterator() {
        return this.result.iterator();
    }

    @Override
    public boolean isEmpty() {
        return this.result.isEmpty();
    }

    @Override
    public int size() {
        return this.result.size();
    }

    @Override
    public ImmutableCollection<FormulaType> asCollection() {
        return this.result.asCollection();
    }

    @Override
    public boolean isSingleton(final FormulaType content) {
        return this.result.isSingleton(content);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.implication == null) ? 0 : this.implication.hashCode());
        result = prime * result + ((this.result == null) ? 0 : this.result.hashCode());
        result = prime * result + ((this.usedApplications == null) ? 0 : this.usedApplications.hashCode());
        result = prime * result + (this.fixpointReached ? 1 : 0);
        return result;
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
        final ExecutionResult<?, ?> other = (ExecutionResult<?, ?>) obj;
        if (this.implication != other.implication) {
            return false;
        }
        if (this.result == null) {
            if (other.result != null) {
                return false;
            }
        } else if (!this.result.equals(other.result)) {
            return false;
        }
        if (this.usedApplications != other.usedApplications) {
            return false;
        }

        if (this.fixpointReached != other.fixpointReached) {
            return false;
        }
        return true;
    }

}
