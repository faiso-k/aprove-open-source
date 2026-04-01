/**
 *
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.itpf;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;

public class ItpfUtils {

    public static Itpf quantifyExist(Collection<TRSVariable> variables, Itpf child) {
        for (TRSVariable var : variables) {
            child = ItpfExists.create(var, child);
        }
        return child;
    }

    public static Itpf quantifyAll(Collection<TRSVariable> variables, Itpf child) {
        for (TRSVariable var : variables) {
            child = ItpfAll.create(var, child);
        }
        return child;
    }

}
