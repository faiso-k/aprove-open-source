package aprove.input.Programs.prolog.structure;

/**
 * @author cryingshadow
 *
 */
public interface ReplacementWalker {

    /**
     * Returns whether or not this ReplacementWalker should be given to the
     * specified PrologTerm.
     * @param term The PrologTerm to check.
     * @return True, if this TermWalker should be given to the specified
     *         PrologTerm. False otherwise.
     */
    boolean goDeeper(final PrologTerm term);

    /**
     * Returns whether or not this ReplacementWalker is applicable for the
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
     * @return The PrologTerm to replace.
     */
    PrologTerm replace(final PrologTerm term);

}
