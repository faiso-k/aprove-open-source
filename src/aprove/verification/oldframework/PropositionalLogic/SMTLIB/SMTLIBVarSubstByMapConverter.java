package aprove.verification.oldframework.PropositionalLogic.SMTLIB;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;

/**
 * Converter used to replace variables in SMTLIB theory atoms. Useful together
 * with {@link TheoryConverterVisitor}, which applies this to a complete
 * formula.
 *
 * @author Marc Brockschmidt
 */
public class SMTLIBVarSubstByMapConverter extends SMTLIBVarSubstConverter {
    /** The map describing the actual substitution. */
    private final Map<SMTLIBVariable<?>, ? extends SMTLIBValue> varSubstitution;

    /**
     * @param varSubst The map describing the actual substitution.
     * @param fact The factory used to create new formulae.
     */
    public SMTLIBVarSubstByMapConverter(
            final Map<SMTLIBVariable<?>, ? extends SMTLIBValue> varSubst,
            final FormulaFactory<SMTLIBTheoryAtom> fact) {
        super(fact);
        this.varSubstitution = varSubst;
    }

    @SuppressWarnings("unchecked")
    @Override
    public <T extends SMTLIBValue> T convertVariable(final SMTLIBVariable<T> var) {
        if (this.varSubstitution.containsKey(var)) {
            return (T) this.varSubstitution.get(var);
        } else {
            return (T) var;
        }
    }
}
