package aprove.input.Programs.prolog.structure;

/**
 * TermWalker for performing whatever action one might want to perform
 * on PrologTerms.<br><br>
 *
 * Created: Sep 8, 2006<br>
 * Last modified: Dec 15, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
public interface TermWalker {

    /**
     * Returns whether or not this TermWalker should be given to the
     * specified PrologTerm.
     * @param term The PrologTerm to check.
     * @return True, if this TermWalker should be given to the specified
     *         PrologTerm. False otherwise.
     */
    boolean goDeeper(final PrologTerm term);

    /**
     * Returns whether or not this TermWalker is applicable for the
     * specified PrologTerm.
     * @param term The PrologTerm to check.
     * @return True, if this TermWalker is applicable for the specified
     *         PrologTerm. False otherwise.
     */
    boolean isApplicable(final PrologTerm term);

    /**
     * Method which is invoked on every PrologTerm for which the
     * isApplicable() method returns true.
     * @param term The PrologTerm on which this method is invoked.
     */
    void performAction(final PrologTerm term);

}
