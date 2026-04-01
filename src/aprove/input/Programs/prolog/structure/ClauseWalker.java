package aprove.input.Programs.prolog.structure;

/**
 * ClauseWalker for performing whatever action one might want to perform
 * on PrologClauses.<br><br>
 *
 * Created: Oct 21, 2006<br>
 * Last modified: Dec 15, 2006
 *
 * @author cryingshadow
 * @version $Id$
 */
public interface ClauseWalker {

    /**
     * Returns whether or not this ClauseWalker is applicable for the
     * specified PrologClause.
     * @param clause The PrologClause to check.
     * @return True, if this ClauseWalker is applicable for the specified
     *         PrologClause. False otherwise.
     */
    boolean isApplicable(PrologClause clause);

    /**
     * Method which is invoked on every PrologClause for which the
     * isApplicable() method results in true.
     * @param clause The PrologClause on which this method is invoked.
     */
    void performAction(PrologClause clause);

}
