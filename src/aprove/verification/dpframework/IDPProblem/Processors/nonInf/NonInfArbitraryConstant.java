/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors.nonInf;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

public class NonInfArbitraryConstant extends GAtomicVar {

    private final TRSTerm term;

    public NonInfArbitraryConstant(final TRSTerm term) {
        super(term.toString());
        this.term = term;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + ((this.term == null) ? 0 : this.term.hashCode());
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (!super.equals(obj)) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final NonInfArbitraryConstant other = (NonInfArbitraryConstant) obj;
        if (this.term == null) {
            if (other.term != null) {
                return false;
            }
        } else if (!this.term.equals(other.term)) {
            return false;
        }
        return true;
    }

    @Override
    public String export(final Export_Util eu) {
        final StringBuilder buffer = new StringBuilder();
        buffer.append("NonInfArbitraryConstant(");
        buffer.append(this.term.export(eu));
        buffer.append(")");
        return buffer.toString();
    }

}
