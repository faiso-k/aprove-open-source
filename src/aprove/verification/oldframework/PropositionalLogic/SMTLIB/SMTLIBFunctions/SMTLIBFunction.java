package aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBFunctions;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;

/**
 * Interface for functions
 * [type1]...[typen] -> [range]
 *
 * @author Andreas Kelle-Emden
 */
public abstract class SMTLIBFunction<T extends SMTLIBValue> implements SMTLIBAssignableSemantics {

    protected final List<String> domains;
    protected final String name;

    protected SMTLIBFunction(final List<String> domains, final String name) {
        this.domains = domains;
        this.name = name;
    }

    public List<String> getDomains() {
        return this.domains;
    }

    public abstract void setResult(List<String> vals, String result);

    public abstract String getRange(SMTTypeTranslator types);

    @Override
    public String getName() {
        return this.name;
    }

    @Override
    public String getTypeAsString(final SMTTypeTranslator types) {
        return types.functions(this.domains, this.getRange(types));
    }

    @Override
    public int hashCode() {
        return this.name.hashCode(); // + ((result == null) ? 0 : result.hashCode());
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        return this.hashCode() == obj.hashCode();
    }

    public Object apply(final SMTLIBFormulaVisitor visitor) {
        // TODO Auto-generated method stub
        return null;
    }

}
