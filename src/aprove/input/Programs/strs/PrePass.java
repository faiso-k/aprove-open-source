/**
 * Collects the defined function symbols.
 * They are on the root position of a lhs of a rule.
 *
 * @author dickmeis
 * @version $Id$
 */

package aprove.input.Programs.strs;

import java.util.*;
import java.util.logging.*;

import aprove.input.Generated.strs.analysis.*;
import aprove.input.Generated.strs.node.*;
import aprove.input.Utility.*;

public class PrePass extends DepthFirstAdapter {

    protected static Logger logger = Logger.getLogger("aprove.input.Programs.strs.PrePass");

    // function symbols occuring on the root position of a lhs
    private Stack<String> definedFunctSymb;

    private ParseErrors parseErrors;

    public PrePass() {
        this.definedFunctSymb = new Stack<String>();
        this.parseErrors = new ParseErrors();
    }

    @Override
    public void outASimple(ASimple node)
    {
        PTerm pTerm = node.getLeft();
        if (pTerm instanceof AVarTerm) {
            ParseError pe = new ParseError(ParseError.VARIABLE_CONDITION_VIOLATED);
            pe.setMessage("Left side must not be a variable.");
            this.parseErrors.add(pe);
            return;
        }

        if (pTerm instanceof AConst0Term) {
            ParseError pe = new ParseError();
            pe.setMessage("Left side must not be a constructor.");
            this.parseErrors.add(pe);
            return;
        }

        AConstFuncTerm aConstFuncTerm = (AConstFuncTerm) pTerm;
        TPrefixIdent prefixIdent = aConstFuncTerm.getPrefixIdent();
        String name = prefixIdent.getText();

        if (!this.definedFunctSymb.contains(name)){
            this.definedFunctSymb.push(name);
        }
    }

    public ParseErrors getErrors() {
        return this.parseErrors;
    }

    public Stack<String> getDefinedFunctSymb(){
        return this.definedFunctSymb;
    }

}