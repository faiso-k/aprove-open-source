package aprove.verification.oldframework.Unification.Problems;

import java.util.*;

public interface SystemOfElementaryProblems {

    /** Returns a List containing all quasi solved forms.
     */
    public List getQuasiSolvedForms();

    /** Returns an iterator that generates the quasi solved forms one-by-one.
     */
    public Iterator iterateQuasiSolvedForms();

}
