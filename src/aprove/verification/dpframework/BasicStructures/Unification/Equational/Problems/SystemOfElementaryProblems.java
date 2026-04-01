/*
 * Created on Feb 16, 2006
 */
package aprove.verification.dpframework.BasicStructures.Unification.Equational.Problems;

import java.util.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */

public interface SystemOfElementaryProblems {

    /** Returns a List containing all quasi solved forms.
     */
    public List getQuasiSolvedForms();

    /** Returns an iterator that generates the quasi solved forms one-by-one.
     */
    public Iterator iterateQuasiSolvedForms();

}
