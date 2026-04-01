package aprove.verification.oldframework.IRSwT.Engines.Formulae;

import java.util.*;

import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * Represent an object that can be "checked" by a rational assignment
 * and that can be exported to SMTLIBInt and SMTLIBRat.
 * (Thanks to java's generics syntax, this interface cannot be split into two
 * separate interfaces ..)
 * @author Matthias Hoelzel
 *
 */
public interface CheckableAndSMTExportable {
    /**
     * Checks whether or not as is a satisfying assignment.
     * @param as some variable assignment
     * @return boolean
     */
    public boolean check(Map<String, PreciseRational> as);

    /**
     * Rewrite this formula into a SMTLIBInt-formula
     * @param factory some formula factory
     * @return a SMTLLIBInt-formula
     */
    public abstract Formula<SMTLIBTheoryAtom> toSMTLIBInt(FormulaFactory<SMTLIBTheoryAtom> factory);

    /**
     * Rewrite this formula into a SMTLIBRat-formula
     * @param factory some formula factory
     * @return a SMTLLIBRat-formula
     */
    public abstract Formula<SMTLIBTheoryAtom> toSMTLIBRat(FormulaFactory<SMTLIBTheoryAtom> factory);
}
