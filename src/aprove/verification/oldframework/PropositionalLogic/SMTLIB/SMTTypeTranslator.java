package aprove.verification.oldframework.PropositionalLogic.SMTLIB;

import java.util.*;

/**
 * Interface for classes that translate internal types to some output format.
 *
 * @author Andreas Kelle-Emden
 */
public interface SMTTypeTranslator {
    /**
     * @return the string describing the type of integer variables.
     */
    String integers();

    /**
     * @return the string describing the type of rational variables.
     */
    String rationals();

    /**
     * @return the string describing the type of boolean variables.
     */
    String bools();

    /**
     * @param len some length
     * @return the string describing the type of bit vector variables of
     *  length <code>n</code>.
     */
    String bitvectors(int len);

    /**
     * @param domains the domains of the functions arguments.
     * @param range the range of the function.
     * @return the string describing the type of functions mapping
     *  values from <code>domains</code> to <code>range</code>.
     */
    String functions(List<String> domains, String range);
}
