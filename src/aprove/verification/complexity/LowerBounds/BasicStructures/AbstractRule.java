package aprove.verification.complexity.LowerBounds.BasicStructures;

import java.util.LinkedHashSet;
import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

public abstract class AbstractRule extends Relation<TRSFunctionApplication, TRSTerm, AbstractRule> implements HasRuleForm {

    public AbstractRule(TRSFunctionApplication lhs, TRSTerm rhs) {
        super(lhs, rhs);
    }

    public FunctionSymbol getRootSymbol() {
        return this.lhs.getRootSymbol();
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.lhs == null) ? 0 : this.lhs.hashCode());
        result = prime * result + ((this.rhs == null) ? 0 : this.rhs.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        AbstractRule other = (AbstractRule) obj;
        if (this.lhs == null) {
            if (other.lhs != null) {
                return false;
            }
        } else if (!this.lhs.equals(other.lhs)) {
            return false;
        }
        if (this.rhs == null) {
            if (other.rhs != null) {
                return false;
            }
        } else if (!this.rhs.equals(other.rhs)) {
            return false;
        }
        return true;
    }

    public abstract Complexity getComplexity();

    @Override
    String getSymbol(Export_Util eu) {
        return eu.rightarrow();
    }

    public abstract String getIndex();
    
    /**
     * returns the set of functionSymbols occurring in this rule.
     * the resulting set may be modified
     */
    @Override
    public Set<FunctionSymbol> getFunctionSymbols() {
        final Set<FunctionSymbol> fs = new LinkedHashSet<FunctionSymbol>();
        this.lhs.collectFunctionSymbols(fs);
        this.rhs.collectFunctionSymbols(fs);
        return fs;
    }


}
