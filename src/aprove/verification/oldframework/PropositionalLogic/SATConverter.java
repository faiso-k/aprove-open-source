package aprove.verification.oldframework.PropositionalLogic;

import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Converts TheoryPropositions and Formulae over such propositions
 * to purely propositional formulae. Note that these conversions
 * need not be equivalence preserving! There are also
 * TheoryPropositions which satisfiability is undecidable for,
 * but purely propositional formulae are necessarily deciable.
 *
 * Recommendation to implementors:
 * The information that establishes the correspondence of the theory atoms
 * to propositional formulae can be stored in some attribute of the class
 * and then be obtained later. We have intentionally specified convert not
 * to return this info since its type is very domain-dependent.
 *
 * @author Carsten Fuhs
 * @version $Id$
 *
 * @param T - statement type to be converted to SAT
 */
public interface SATConverter<T extends TheoryProposition> {

    /**
     * Converts a Formula over a TheoryProposition
     * to a purely propositional Formula.
     *
     * Note to implementors:
     *  - visit f (propbably a good idea: each node only once!)
     *  - at TheoryAtoms, use convertProposition
     *  - maybe remember some stuff that happens there
     *  - postprocess using the stuff that happened while
     *    converting or using some other global info
     *
     *  - store
     * @param f - to be converted
     * @return
     *  - a corresponding purely propostional formula
     */
    public Formula<None> convert(Formula<T> f);

    /**
     * Converts a TheoryProposition to a corresponding
     * purely propositional formula.
     *
     * @param proposition - to be converted
     * @return a corresponding purely propositional formula
     */
    public Formula<None> convertProposition(T proposition);
}
