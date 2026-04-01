/**
 *
 * @author noschinski
 * @version $Id$
 */

package aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes;

import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Visitors.*;

public class SMTLIBConverterVarPartVisitor<V extends GPolyVar>
                                    extends VarPartNodeVisitor<V> {

    /**
     * Representation of the VarPart in SMTLIB format.
     */
    private StringBuffer source;

    /**
     * Maps variables to a textual representation in the generated source string.
     */
    private final SMTLIBVarMapper<V> varMapper;

    public SMTLIBConverterVarPartVisitor(SMTLIBVarMapper<V> varMapper) {
        this.source = new StringBuffer();
        this.varMapper = varMapper;
    }

    /**
     * Truncates the getSource() output.
     *
     * @see getSource
     */
    public void clearSource() {
        this.source = new StringBuffer();
    }

    /**
     * Returns the textual SMTLIB representation of the VarPart.
     *
     * The return value is only useful, after the visitor's applyTo method
     * was called.
     *
     * Note: The source string is not truncated between mulitple applyTo calls;
     * this must be done manually by calliwng clearSource().
     */
    public String getSource() {
        return this.source.toString();
    }

    @Override
    public void fcaseVarPartNode(VarPartNode<V> v) {
        V var = v.getVar();

        if (var == null) {
            // empty var = 1
            this.source.append(" 1");
            return;
        }

        this.source.append(" ");
        if (this.varMapper != null) {
            this.source.append(this.varMapper.getName(var));
        } else {
            this.source.append(var);
        }
    }


}
