package aprove.verification.oldframework.PropositionalLogic.Formulae;


/**
 * SplitMode allows to select the mode to
 * split And or Or formulae.
 *
 * @author Patrick Kabasci
 * @version $Id$
 */
public enum SplitMode {
    // flatten nested occurrences of the same kind of formula
    // (-> try to achieve high junctor arity)
    FLATTEN,

    // build a left comb out of the args (-> junctors at most binary)
    LEFT_COMB,

    // build a right comb out of the args (-> junctors at most binary)
    RIGHT_COMB,

    // build a balanced binary tree out of the args
    // (-> junctors at most binary)
    BALANCED,

    // just take the args as they come (-> arity depends on the number
    // of (possibly unique) arguments)
    UNFILTERED
}