package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBBitVector;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * Variable of type bitvector
 *
 * @author Andreas Kelle-Emden
 */
public class SMTLIBBVVariable extends SMTLIBVariable<SMTLIBBVValue> implements SMTLIBBVValue {
    private final int len;
    // Bitvector in form 1010010100111
    private String result;

    private SMTLIBBVVariable(final String name, final int len) {
        super(name);
        this.len = len;
        this.result = null;
    }

    public static SMTLIBBVVariable create(final String name, final int len) {
        return new SMTLIBBVVariable(name, len);
    }

    @Override
    public int getLen() {
        return this.len;
    }

    /** {@inheritDoc} */
    @Override
    public String getTypeAsString(final SMTTypeTranslator types) {
        return types.bitvectors(this.len);
    }

    @Override
    public void setResult(final String entry) {
        if (entry.startsWith("0b")) {
            this.result = entry.substring(2);
        } else {
            this.result = entry;
        }
    }

    public Integer getResultAsUnsignedInteger() {
        if (this.result == null) {
            return null;
        }
        return Integer.parseInt(this.result,2);
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = super.hashCode();
        result = prime * result + this.len;
        return result;
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (!super.equals(obj)) {
            return false;
        }
        if (!(obj instanceof SMTLIBBVVariable)) {
            return false;
        }
        final SMTLIBBVVariable other = (SMTLIBBVVariable) obj;
        if (this.len != other.len) {
            return false;
        }
        return true;
    }

}
