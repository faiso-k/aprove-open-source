package aprove.verification.idpframework.Core.Utility.Marking;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.idpframework.Core.*;
import aprove.verification.idpframework.Polynomials.Interpretation.*;
import aprove.verification.idpframework.Processors.ItpfRules.Execution.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 *
 * @author MP
 */
public class ExecutionMark<MetaDataType> extends IDPExportable.IDPExportableSkeleton implements Immutable, Mark<MetaDataType> {

    private final ExecutableRule<?, MetaDataType> mark;
    private final ImplicationType executionRequirements;
    private final ApplicationMode mode;
    private final int hashCode;
    private final PolyInterpretation<?> polyInterpretation;

    public ExecutionMark(final ExecutableRule<?, MetaDataType> mark, final PolyInterpretation<?> polyInterpretation, final ImplicationType executionRequirements, final ApplicationMode mode) {
        this.mark = mark;
        this.polyInterpretation = polyInterpretation;
        this.executionRequirements = executionRequirements;
        this.mode = mode;
        {
            final int prime = 31;
            int result = 1;
            result =
                prime
                    * result
                    + executionRequirements.hashCode();
            result = prime * result + mark.hashCode();
            result = prime * result + (polyInterpretation != null ? polyInterpretation.hashCode() : 0);
            result = prime * result + mode.hashCode();
            this.hashCode = result;
        }
    }

    @Override
    public boolean isCompatible(final Mark<?> mark) {
        if (this.mode != ApplicationMode.Multistep) {
            return false;
        }

        if (mark instanceof ExecutionMark) {
            final ExecutionMark<?> otherMark = (ExecutionMark<?>) mark;
            return otherMark.mode == ApplicationMode.Multistep && this.executionRequirements == otherMark.executionRequirements && this.mark.isCompatible(otherMark.mark);
        }

        return false;
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
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final ExecutionMark<?> other = (ExecutionMark<?>) obj;

        if (this.polyInterpretation == null) {
            if (other.polyInterpretation != null) {
                return false;
            }
        } else if (!this.polyInterpretation.equals(other.polyInterpretation)) {
            return false;
        }

        return this.executionRequirements == other.executionRequirements
            && this.mode == other.mode
            && this.mark.equals(other.mark);
    }

    @Override
    public void export(final StringBuilder sb,
        final Export_Util eu,
        final VerbosityLevel verbosityLevel) {
        this.executionRequirements.export(sb, eu, verbosityLevel);
        sb.append(" ");
        sb.append(this.mode);
        sb.append(" ");
        this.mark.export(sb, eu, verbosityLevel);
    }

}
