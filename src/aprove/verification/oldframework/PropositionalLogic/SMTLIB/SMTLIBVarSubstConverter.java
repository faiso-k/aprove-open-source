package aprove.verification.oldframework.PropositionalLogic.SMTLIB;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector.SMTLIBBVFunctions.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBool.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBFunctions.*;
/**
 * Converter used to replace variables in SMTLIB theory atoms. Useful together
 * with {@link TheoryConverterVisitor}, which applies this to a complete
 * formula.
 *
 * @author Marc Brockschmidt
 */
public abstract class SMTLIBVarSubstConverter implements TheoryConverter<SMTLIBTheoryAtom, SMTLIBTheoryAtom> {
    /** The factory used to create new formulae. */
    private final FormulaFactory<SMTLIBTheoryAtom> factory;

    /**
     * @param fact The factory used to create new formulae.
     */
    public SMTLIBVarSubstConverter(final FormulaFactory<SMTLIBTheoryAtom> fact) {
        this.factory = fact;
    }

    @Override
    public Formula<SMTLIBTheoryAtom> convert(final SMTLIBTheoryAtom theoryProposition) {
        return this.factory.buildTheoryAtom(this.convertAtom(theoryProposition));
    }

    public abstract <T extends SMTLIBValue> T convertVariable(SMTLIBVariable<T> var);

    public <T extends SMTLIBValue> SMTLIBTheoryAtom convertAtom(final SMTLIBTheoryAtom theoryProposition) {
        if (theoryProposition instanceof SMTLIBFuncApp<?>) {
            @SuppressWarnings("unchecked")
            final SMTLIBFuncApp<T> funcApp = (SMTLIBFuncApp<T>) theoryProposition;
            return funcApp.createFromInstance(
                    this.convertValues(funcApp.getDomVals()));
        } else if (theoryProposition instanceof SMTLIBBoolValue) {
            return this.convertValue((SMTLIBBoolValue) theoryProposition);
        } else {
            throw new UnsupportedOperationException("Unknown SMTLIB formula element.");
        }
    }

    /**
     * @param <T> the type of the value
     * @param value the actual value
     * @return the converted value.
     */
    @SuppressWarnings("unchecked")
    public <T extends SMTLIBValue> T convertValue(final T value) {
        if (value instanceof SMTLIBVariable<?>) {
            return (T) this.convertVariable((SMTLIBVariable<?>) value);
        } else if (value instanceof SMTLIBConstant) {
            return value;
        } else if (value instanceof SMTLIBCMP<?>) {
            final SMTLIBCMP<T> cmp = (SMTLIBCMP<T>) value;
            return (T) cmp.createFromExisting(
                    this.convertValue(cmp.getA()),
                    this.convertValue(cmp.getB()));
        } else if (value instanceof SMTLIBFuncApp) {
            final SMTLIBFuncApp<T> funcApp = (SMTLIBFuncApp<T>) value;
            return (T) funcApp.createFromInstance(
                    this.convertValues(funcApp.getDomVals()));
        } else if (value instanceof SMTLIBITE<?>) {
            final SMTLIBITE<T> ite = (SMTLIBITE<T>) value;
            return (T) ite.createFromExisting(
                    this.convertValue(ite.getCondition()),
                    this.convertValue(ite.getThenValue()),
                    this.convertValue(ite.getElseValue()));
        } else if (value instanceof SMTLIBNAryFunc) {
            final SMTLIBNAryFunc<T> func = (SMTLIBNAryFunc<T>) value;
            return (T) func.createFromExisting(
                    this.convertValues(func.getValues()));
        } else if (value instanceof SMTLIBBVExtract) {
            final SMTLIBBVExtract extract = (SMTLIBBVExtract) value;
            return (T) SMTLIBBVExtract.create(
                    this.convertValue(extract.getA()),
                    extract.getI(),
                    extract.getJ());
        }

        throw new UnsupportedOperationException("Unknown SMTLIB object " + value.getClass());
    }

    /**
     * @param <T> the type of the values
     * @param vals list of values
     * @return list of converted values.
     */
    private <T extends SMTLIBValue> List<T> convertValues(final List<T> vals) {
        final List<T> newVals = new ArrayList<T>(vals.size());
        for (final T val : vals) {
            newVals.add(this.convertValue(val));
        }
        return newVals;
    }
}
