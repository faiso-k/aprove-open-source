package aprove.verification.oldframework.IRSwT.Engines.Formulae;

import java.util.*;

import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * Represents a negation.
 * @author Matthias Hoelzel
 * @param <A> type of atoms
 */
public class NotFormula<A extends CheckableAndSMTExportable> extends AbstractFormula<A> {
    /** Store the direct subformula of this. */
    AbstractFormula<A> formula;

    /**
     * Constructor!
     * @param subformula a negation always exactly one subformula
     */
    public NotFormula(final AbstractFormula<A> subformula) {
        this.formula = subformula;
    }

    @Override
    public boolean check(final Map<String, PreciseRational> as) {
        return !this.formula.check(as);
    }

    @Override
    public Formula<SMTLIBTheoryAtom> toSMTLIBInt(final FormulaFactory<SMTLIBTheoryAtom> factory) {
        return factory.buildNot(this.formula.toSMTLIBInt(factory));
    }

    @Override
    public Formula<SMTLIBTheoryAtom> toSMTLIBRat(final FormulaFactory<SMTLIBTheoryAtom> factory) {
        return factory.buildNot(this.formula.toSMTLIBRat(factory));
    }

    @Override
    public String toString() {
        return "! " + this.formula;
    }
}
