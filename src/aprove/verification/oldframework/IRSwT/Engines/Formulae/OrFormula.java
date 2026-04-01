package aprove.verification.oldframework.IRSwT.Engines.Formulae;

import java.util.*;

import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * Represents a disjunction!
 * @author Matthias Hoelzel
 * @param <A> type of atoms
 */
public class OrFormula<A extends CheckableAndSMTExportable> extends TwoAryFormula<A> {
    /**
     * Constructor!
     * @param leftForm the left formula
     * @param rightForm the right formula
     */
    public OrFormula(final AbstractFormula<A> leftForm, final AbstractFormula<A> rightForm) {
        super(leftForm, rightForm);
    }

    @Override
    public boolean check(final Map<String, PreciseRational> as) {
        final boolean result = this.left.check(as) || this.right.check(as);
        return result;
    }

    @Override
    public Formula<SMTLIBTheoryAtom> toSMTLIBInt(final FormulaFactory<SMTLIBTheoryAtom> factory) {
        return factory.buildOr(this.left.toSMTLIBInt(factory), this.right.toSMTLIBInt(factory));
    }

    @Override
    public Formula<SMTLIBTheoryAtom> toSMTLIBRat(final FormulaFactory<SMTLIBTheoryAtom> factory) {
        return factory.buildOr(this.left.toSMTLIBRat(factory), this.right.toSMTLIBRat(factory));
    }

    @Override
    public String toString() {
        return "(" + this.left.toString() + " \\/ " + this.right.toString() + ")";
    }
}
