package aprove.verification.oldframework.PropositionalLogic.SMTLIB;

/**
 * Class implemented by constants in the SMTLIB framework.
 *
 * @author Marc Brockschmidt
 */
public abstract class SMTLIBConstant<T extends SMTLIBValue> implements SMTLIBValue {

    @Override
    public void apply(final SMTFormulaVisitor<?> visitor) {
        visitor.caseSMTConstant(this);
        return;
    }
}
