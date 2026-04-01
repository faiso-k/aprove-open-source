package aprove.verification.oldframework.IRSwT.Engines.Formulae;

import java.util.*;

import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * Represent an atomic formula.
 * @author Matthias Hoelzel
 * @param <A> type of atoms
 */
public class AtomFormula<A extends CheckableAndSMTExportable> extends AbstractFormula<A> {
    /** Atom! Atom! */
    private final A atom;

    /**
     * Constructor!
     * @param a some atom to be stored
     */
    public AtomFormula(final A a) {
        this.atom = a;
    }

    @Override
    public Formula<SMTLIBTheoryAtom> toSMTLIBInt(final FormulaFactory<SMTLIBTheoryAtom> factory) {
        return this.atom.toSMTLIBInt(factory);
    }

    @Override
    public Formula<SMTLIBTheoryAtom> toSMTLIBRat(final FormulaFactory<SMTLIBTheoryAtom> factory) {
        return this.atom.toSMTLIBRat(factory);
    }

    @Override
    public boolean check(final Map<String, PreciseRational> as) {
        final boolean result = this.atom.check(as);
        return result;
    }

    @Override
    public String toString() {
        return this.atom.toString();
    }
}
