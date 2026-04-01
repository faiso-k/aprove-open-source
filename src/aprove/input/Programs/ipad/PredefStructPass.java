package aprove.input.Programs.ipad;

import aprove.input.Generated.ipad.node.*;
import aprove.input.Programs.Predef.*;
import aprove.input.Programs.Predef.IntegerPredef.*;
import aprove.verification.oldframework.Typing.*;

/** This pass creates the appropriate sorts and types for all predefined structures.
 *  <p>
 *  Also, for each predefined structure a corresponding equal_* function is defined
 *  And for every constructor a isa_*-function is added.
 * @author Matthias Raffelsieper
 */

class PredefStructPass extends Pass {

    private String intName;

    @Override
    public void inStart(Start node) {
        this.containsInts = false;
        this.intName = AbstractIntegerPredefItem.getIntTypeName();
        PredefDataStructureSymbols.clear();
        PredefFunctionSymbols.clear();
    }


    @Override
    public void outStart(Start node) {
        if (this.containsInts) {
            this.addIntStruct();
            this.addPredefIntFunctions();
        }
    }

    /** adds the predefined Data Structure for Integers
     *  with the name defined in intTypeName
     */
    private void addIntStruct() {
        String intTypeName = AbstractIntegerPredefItem.getIntTypeName();

        TypeDefinition intTD = (new IntegerDataStructureCreator(this.typeContext, this.prog)).createIntegerDataStructure();

        PredefDataStructureSymbols.addPredefinedSymbols(intTD);

        this.sorttoken.put(intTypeName, new TId(intTypeName));
    }


    private void addPredefIntFunctions() {
        PredefFunctionSymbols.addPredefinedFunctions(IntegerTools.getIntegerPredefFunctions());
    }



    /** checks whether the passed tokens content is equal to the name
     * integers are assumed to have and sets containsInts accordingly
     */
    private void testForInt(Node node) {
        String sortName = this.chop(node);
        if (this.intName.equals(sortName)) {
            this.containsInts = true;
        }
    }


    @Override
    public void inAIdlist(AIdlist node) {
        this.testForInt(node.getType());
    }

    @Override
    public void inAIdcomma(AIdcomma node) {
        this.testForInt(node.getType());
    }

    @Override
    public void inAType(AType node) {
        this.testForInt(node.getId());
    }

    @Override
    public void inAParam(AParam node) {
        this.testForInt(node.getType());
    }

    @Override
    public void inAIntNumberSterm(AIntNumberSterm node) {
        this.containsInts = true;
    }
}
