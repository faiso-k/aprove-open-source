package aprove.input.Programs.Predef.IntegerPredef;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

/** Represents an abstract item which represents an object of a pre-defined data structure.
 * @author Matthias Raffelsieper
 */

public class IntegerPredefItem extends AbstractIntegerPredefItem {

    public IntegerPredefItem() {
        this(null, null, null);
    }

    public IntegerPredefItem(String nodeContent, TypeContext typeContext, Program program) {
        super(nodeContent,typeContext, program, new Vector<AlgebraTerm>());
    }


    /** checks whether a given string can be parsed as integer number (with leading '+' or '-')
     * @param str String to check whether it represents an integer number
     * @return true iff the passed string can be parsed as integer number
     */
    public static boolean isIntegerString(String str) {
        if (str.startsWith("+")) {
            str = str.substring(1);
        }
        try {
            Integer.parseInt(str);
            return true;
        }
        catch (NumberFormatException e) {
            return false;
        }
    }


    /** creates a Term from an object of a pre-defined data structure
     * @return a pair consisting of the term corresponding to the object
     * and possibly a set of rules that are needed for this data structure.
     */
    @Override
    public AlgebraTerm toTerm() {
        AlgebraTerm term;

        String numberString = this.nodeContent;
        // strip off a "+"-sign
        if (this.nodeContent.charAt(0)=='+') {
            numberString = this.nodeContent.substring(1,this.nodeContent.length());
        }
        int number = Integer.parseInt(numberString);

        // if the number is bigger than 0, it will be built entirely from succ, otherwise entirely from pred
        SyntacticFunctionSymbol d = (number>0) ? this.getSucc() : this.getPred();

        term = AlgebraFunctionApplication.create(this.getZero());

        for(int i=0; i<Math.abs(number); ++i) {
            Vector<AlgebraTerm> args = new Vector<AlgebraTerm>();
            args.add(term);
            term = AlgebraFunctionApplication.create(d, args);
        }

        return term;
    }


}
