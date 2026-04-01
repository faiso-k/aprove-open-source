package aprove.verification.oldframework.IRSwT.Engines.Formulae;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatComparison.*;

/**
 * Represents a formula that is always true.
 * @author Matthias Hoelzel
 * @param <A> type of atoms
 */
public class TrueFormula<A extends CheckableAndSMTExportable> extends AbstractFormula<A> {
    @Override
    public boolean check(final Map<String, PreciseRational> as) {
        return true;
    }

    @Override
    public Formula<SMTLIBTheoryAtom> toSMTLIBInt(final FormulaFactory<SMTLIBTheoryAtom> factory) {
        final SMTLIBIntConstant smtLibZero = SMTLIBIntConstant.create(BigInteger.ZERO);
        return factory.buildTheoryAtom(SMTLIBIntEquals.create(smtLibZero, smtLibZero));
    }

    @Override
    public Formula<SMTLIBTheoryAtom> toSMTLIBRat(final FormulaFactory<SMTLIBTheoryAtom> factory) {
        final SMTLIBRatConstant smtLibZero = SMTLIBRatConstant.create(BigInteger.ZERO);
        return factory.buildTheoryAtom(SMTLIBRatEquals.create(smtLibZero, smtLibZero));
    }

    @Override
    public String toString() {
        return "TRUE";
    }
}
