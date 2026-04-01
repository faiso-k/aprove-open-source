package aprove.input.Programs.Predef.IntegerPredef;

import java.util.*;

import aprove.input.Programs.Predef.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Typing.*;

/** class that is the base class for all integer related predefined items.
 *  it also defines the names that the data structure symbols are assumed to have.
 */
public abstract class AbstractIntegerPredefItem extends AbstractPredefItem {


    private static final String intTypeName = "int";
    private static final String zeroName = "0_int";
    private static final String succName = "s_int";
    private static final String predName = "p_int";
    private static final String succSelectorName = "sSel_int";
    private static final String predSelectorName = "pSel_int";


    protected Vector<AlgebraTerm> arguments;
    private AlgebraTerm intType;
    private Sort intSort;
    private ConstructorSymbol zero = null;
    private ConstructorSymbol succ = null;
    private ConstructorSymbol pred = null;

    public AbstractIntegerPredefItem() {
        this(null, null, null, new Vector<AlgebraTerm>());
    }

    public AbstractIntegerPredefItem(String nodeContent, TypeContext typeContext, Program program, List<AlgebraTerm> arguments) {
        super(nodeContent, typeContext, program);
        this.setArguments(arguments);
        this.getDataStructure();
    }


    /** Name Integers are assumed to have
     * @return the name expected for ints
     */
    public static String getIntTypeName() {
        return AbstractIntegerPredefItem.intTypeName;
    }

    /** Name the Constructor zero is assumed to have
     * @return the name expected for zero
     */
    public static String getZeroName() {
        return AbstractIntegerPredefItem.zeroName;
    }

    /** Name the Constructor succ is assumed to have
     * @return the name expected for succ
     */
    public static String getSuccName() {
        return AbstractIntegerPredefItem.succName;
    }

    /** Name the Constructor pred is assumed to have
     * @return the name expected for pred
     */
    public static String getPredName() {
        return AbstractIntegerPredefItem.predName;
    }

    /** name the selector for succ is assumed to have
     * @return the name expected for the selector of succ
     */
    public static String getSuccSelectorName() {
        return AbstractIntegerPredefItem.succSelectorName;
    }

    /** name the selector for pred is assumed to have
     * @return the name expected for the selector of pred
     */
    public static String getPredSelectorName() {
        return AbstractIntegerPredefItem.predSelectorName;
    }


    // Selectors

    public Vector<AlgebraTerm> getArguments() {
        return this.arguments;
    }

    public void setArguments(List<AlgebraTerm> arguments) {
        this.arguments = new Vector<AlgebraTerm>(arguments);
    }


    public AlgebraTerm getIntType() {
        if (this.intType == null) {
            this.intType = this.typeContext.getTypeDef(AbstractIntegerPredefItem.intTypeName).getDefTerm();
        }
        return this.intType;
    }

    public void setIntType(AlgebraTerm intType) {
        this.intType = intType;
    }

    /** @deprecated
     */
    @Deprecated
    protected Sort getIntSort() {
        if (this.intSort == null) {
            this.intSort = this.program.getSort(AbstractIntegerPredefItem.intTypeName);
        }
        return this.intSort;
    }

    /** @deprecated
     */
    @Deprecated
    protected void setIntSort(Sort intSort) {
        this.intSort = intSort;
    }

    public ConstructorSymbol getZero() {
        return this.zero;
    }

    public void setZero(ConstructorSymbol zero) {
        this.zero = zero;
    }


    public ConstructorSymbol getSucc() {
        return this.succ;
    }

    public void setSucc(ConstructorSymbol succ) {
        this.succ = succ;
    }


    public ConstructorSymbol getPred() {
        return this.pred;
    }

    public void setPred(ConstructorSymbol pred) {
        this.pred = pred;
    }




    /* @see aprove.input.Programs.ipad.AbstractPredefItem#toTerm()
     */
    @Override
    public abstract AlgebraTerm toTerm();


    /** checks whether a Term t is built only from symbols of the Integer Data Structure
     * and does not contain succ and pred inside one another
     * @param t Term to check
     * @return true iff t is built only from zero, succ, or pred
     */
    public boolean isIntegerTerm(AlgebraTerm t) {
        return IntegerTools.isIntegerTerm(t,this.typeContext);
    }



    /** returns a new DefFunctionSymbol with specified name and arity
     * the return type is assumed to be int
     * @param name name of the newly created DefFunctionSymbol
     * @param arity number of arguments of the new DefFunctionSymbol
     * @return the new DefFunctionSymbol
     */
    protected DefFunctionSymbol createAndAddDefFunSym(String name, int arity) {
        return this.createAndAddDefFunSym(name, arity, this.getIntType(), this.getIntSort());
    }

    /** returns a new DefFunctionSymbol with specified name and arity
     * and return type
     * @param name name of the newly created DefFunctionSymbol
     * @param arity number of arguments of the new DefFunctionSymbol
     * @param retType return type of the new DefFunctionSymbol
     * @param retSort sort of return value of the new DefFunctionSymbol
     * @return the new DefFunctionSymbol
     */
    protected DefFunctionSymbol createAndAddDefFunSym(String name, int arity, AlgebraTerm retType, Sort retSort) {

        List<Sort> sortArgs = new Vector<Sort>();
        List<AlgebraTerm> typeArgs = new Vector<AlgebraTerm>();
        for(int i=0; i<arity; ++i) {
            sortArgs.add(this.getIntSort());
            typeArgs.add(this.getIntType());
        }

        DefFunctionSymbol defSym = DefFunctionSymbol.create(name, sortArgs, retSort);

        this.typeContext.setSingleTypeOf(defSym, new Type(TypeTools.function(typeArgs, retType)));
        try {
            this.program.addDefFunctionSymbol(defSym);
//            this.program.setFunctionSignature(defSym, Symbol.DEFAULTSIG);
            // the following (setting signature to MAINSIG) results in keeping this symbol
            // even if it is not used anymore in the simplified program
            // and also its termination will be shown everytime when a SCC contains it
            // but it will be contained in its own MRB
            this.program.setFunctionSignature(defSym, Symbol.MAINSIG);
        } catch (ProgramException e) { throw new RuntimeException("A Function Symbol with name ''"+name+"'' already exists."); }

        defSym.setTermination(true);

        return defSym;
    }


    /* reads the constructor zero and the defined function symbols succ and pred
     * (which are used to build terms) from the program.
     * These are added if necessary
     */
    private void getDataStructure() {
        TypeDefinition intTypeDef = this.typeContext.getTypeDef(AbstractIntegerPredefItem.intTypeName);



        // the Integer TypeDef does not exist yet => ERROR, since it should have been created in the PredefStructPass
        if(intTypeDef == null) {
            throw new RuntimeException("Internal Error: The Integer Type Definition was not found.");
        }

        // read the Integer Symbols
        for(Symbol sym : intTypeDef.getDeclaredSymbols()) {
            if (sym.getName().equals(AbstractIntegerPredefItem.zeroName)) {
                this.zero = (ConstructorSymbol)sym;
            } else if (sym.getName().equals(AbstractIntegerPredefItem.succName)) {
                this.succ = (ConstructorSymbol)sym;
            } else if (sym.getName().equals(AbstractIntegerPredefItem.predName)) {
                this.pred = (ConstructorSymbol)sym;
            } else {
                throw new RuntimeException("Error: Symbol ''"+sym.getName()+"'' in Integer type definition is unknown.");
            }
        }

        if ( (this.zero == null) || (this.succ == null) || (this.pred == null) ) {
            if ( (this.zero == null) && (this.succ == null) && (this.pred == null) ) {
                throw new RuntimeException("Internal Error: Integer data structure symbols do not exist!");
            }
            else {
                throw new RuntimeException("Internal Error: Some Integer data structure symbols exist, while others do not.");
            }
        }
    }



}
