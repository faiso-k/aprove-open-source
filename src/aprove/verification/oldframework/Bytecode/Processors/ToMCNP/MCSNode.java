package aprove.verification.oldframework.Bytecode.Processors.ToMCNP;

import java.util.*;
import java.util.concurrent.atomic.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 *
 * @author Matthias Hoelzel
 *
 */
public class MCSNode {
    private static AtomicInteger counter = new AtomicInteger();

    public ArrayList<MCSVariable> variables;

    /**
     * Node's postfix-number.
     */
    private final Integer postfix;

    /**
     * Constructor: Create an empty node.
     */
    public MCSNode() {
        this.variables = new ArrayList<MCSVariable>();
        this.postfix = MCSNode.counter.incrementAndGet();
    }

    /**
     * Returns node's postfix-number.
     * @return Integer
     */
    public Integer getPostfix() {
        return this.postfix;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((this.postfix == null) ? 0 : this.postfix.hashCode());
        result = prime * result + ((this.variables == null) ? 0 : this.variables.hashCode());
        return result;
    }

    /**
     * {@inheritDoc}
     */
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
        final MCSNode other = (MCSNode) obj;
        if (this.postfix == null) {
            if (other.postfix != null) {
                return false;
            }
        } else if (!this.postfix.equals(other.postfix)) {
            return false;
        }
        if (this.variables == null) {
            if (other.variables != null) {
                return false;
            }
        } else if (!this.variables.equals(other.variables)) {
            return false;
        }
        return true;
    }

    @Override
    public String toString() {
        final StringBuilder result = new StringBuilder("MCSNode(");
        int num = this.variables.size();
        for (final MCSVariable v : this.variables) {
            result.append(v.toString());
            num--;
            if (num != 0) {
                result.append(", ");
            }
        }
        result.append(')');
        return result.toString();
    }

    /**
     * Returns the dot name.
     * @return string
     */
    public String getDotName() {
        return "n" + this.postfix;
    }

    /**
     * Returns this node in form of a function application.
     * @return A function application.
     */
    public TRSFunctionApplication toFunctionApplication() {
        final String symbolName = "f" + this.postfix.toString();
        final FunctionSymbol symbol = FunctionSymbol.create(symbolName, this.variables.size());
        final ArrayList<TRSVariable> arguments = new ArrayList<TRSVariable>(this.variables.size());
        for (final MCSVariable v : this.variables) {
            arguments.add(TRSTerm.createVariable(v.getName()));
        }

        return TRSTerm.createFunctionApplication(symbol, ImmutableCreator.create(arguments));
    }

    /**
     * Returns the dot representation.
     * @return string
     */
    public String getDotRepresentation() {
        final StringBuilder result = new StringBuilder(this.getDotName());
        result.append("[label=\"");
        int modCounter = 0;
        for (final MCSVariable v : this.variables) {
            result.append(v);
            modCounter++;
            if (modCounter != this.variables.size()) {
                result.append(',');
                if (modCounter % 4 == 0) {
                    result.append("\\n");
                } else {
                    result.append(' ');
                }
            }
        }
        result.append("\", shape=\"box\"];");
        return result.toString();
    }
}
