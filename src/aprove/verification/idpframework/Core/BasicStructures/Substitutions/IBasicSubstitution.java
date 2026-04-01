package aprove.verification.idpframework.Core.BasicStructures.Substitutions;

import java.util.*;

import aprove.verification.idpframework.Core.*;
import immutables.*;

/**
 * Contract on hashCode() and equals():
 *      hashCode : hashCode of domain
 *      equals : if domains are equal and substitutions on that domain are equal
 * @author MP
 */
public interface IBasicSubstitution {

    public Set<?> getDomain();
    public Object substitute(final Object key);

    /**
     * Domain must be immutable!
     * @author MP
     *
     */
    public abstract class IBasicSubstitutionSkeleton extends IDPExportable.IDPExportableSkeleton implements IBasicSubstitution {

        private volatile Integer hashCode;

        @Override
        public int hashCode() {
            if (this instanceof Immutable) {
                if (this.hashCode == null) {
                    synchronized (this) {
                        if (this.hashCode == null) {
                            this.hashCode = this.getDomain().hashCode();
                        }
                    }
                }
                return this.hashCode;
            } else {
                return this.getDomain().hashCode();
            }
        }

        @Override
        public boolean equals(final Object obj) {
            if (this == obj) {
                return true;
            }
            if (obj == null) {
                return false;
            }
            if (!(obj instanceof IBasicSubstitution)) {
                return false;
            }
            final IBasicSubstitution other = (IBasicSubstitution) obj;

            final Set<?> myDomain = this.getDomain();
            final Set<?> otherDomain = other.getDomain();
            if (!myDomain.equals(otherDomain)) {
                return false;
            }

            for (final Object key : myDomain) {
                if (!this.substitute(key).equals(other.substitute(key))) {
                    return false;
                }
            }

            return true;
        }

    }

}
