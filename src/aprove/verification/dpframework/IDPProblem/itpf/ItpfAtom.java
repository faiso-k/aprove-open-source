/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.itpf;


public abstract class ItpfAtom extends Itpf {

    public ItpfAtom() {
        super(true, true);
    }

    @Override
    public final boolean isAtom () {
        return true;
    }

}
