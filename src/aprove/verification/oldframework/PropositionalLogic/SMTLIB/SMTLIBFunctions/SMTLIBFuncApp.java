package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBFunctions;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * Function application
 *
 * @author Andreas Kelle-Emden
 */
public abstract class SMTLIBFuncApp<T extends SMTLIBValue> implements SMTLIBTheoryAtom, SMTLIBValue {

    protected final List<SMTLIBValue> domVals;

    protected SMTLIBFuncApp(final List<SMTLIBValue> domVals) {
        this.domVals = domVals;
    }

    public abstract SMTLIBFunction<T> getFunc();

    /**
     * @param newVals new values
     * @return a new instance of this function application, using the new values
     *  as arguments instead of the existing ones (i.e., it keeps only the
     *  applied function, all other values may differ).
     */
    public abstract SMTLIBFuncApp<T> createFromInstance(List<SMTLIBValue> newVals);

    @Override
    public Object apply(final SMTLIBFormulaVisitor visitor) {
        return visitor.caseSMTLIBFuncApp(this);
    }

    public List<SMTLIBValue> getDomVals() {
        return this.domVals;
    }

    @Override
    public void apply(final SMTFormulaVisitor<?> visitor) {
        visitor.caseSMTFuncApp(this);
        for (final SMTLIBValue arg : this.domVals) {
            arg.apply(visitor);
        }
    }
}
