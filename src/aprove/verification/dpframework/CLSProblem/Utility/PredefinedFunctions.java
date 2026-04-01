/**
 *
 */
package aprove.verification.dpframework.CLSProblem.Utility;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * Enumeration of all predefined function symbol, except the integers.
 */
public enum PredefinedFunctions {
    And("And", 2),
    Or("Or", 2),
    Not("not", 1),
    Clt("Clt", 2),
    Cle("Cle", 2),
    Ceq("Eq", 2),
    Cge("Cge", 2),
    Cgt("Cgt", 2),
    Add("Add", 2),
    Sub("Sub", 2),

    Neg("Neg", 1),
    Div("Div", 2),
    Mul("Mul", 2),
    Rem("Rem", 2),
    Shl("Shl", 2),
    Shr("Shr", 2),
    Xor("Xor", 2),

    // FIXME: Check arity!
    Conv_i("Conv_i", 1),
    Conv_i1("Conv_i1", 1),
    Conv_i2("Conv_i2", 1),
    Conv_i4("Conv_i4", 1),
    Conv_i8("Conv_i8", 1),
    Conv_r4("Conv_r4", 1),
    Conv_r8("Conv_r8", 1),
    Conv_u("Conv_u", 1),
    Conv_u1("Conv_u1", 1),
    Conv_u2("Conv_u2", 1),
    Conv_u4("Conv_u4", 1),
    Conv_u8("Conv_u8", 1),
    Conv_r_un("Conv_r_un", 1),
    WritableBytes("WritableBytes", 2),
    Add_Ovf("Add_Ovf", 2),
    Add_Ovf_Un("Add_Ovf_Un", 2),
    Cne_Un("Cne_Un", 2),
    Cge_Un("Cge_Un", 2),
    Cgt_Un("Cgt_Un", 2),
    Cle_Un("Cle_Un", 2),
    Clt_Un("Clt_Un", 2),
    Div_Un("Div_Un", 2),
    Mul_Ovf("Mul_Ovf", 2),
    Mul_Ovf_Un("Mul_Ovf_Un", 2),
    Rem_Un("Rem_Un", 2),
    Shr_Un("Shr_Un", 2),
    Sub_Ovf("Sub_Ovf", 2),
    Sub_Ovf_Un("Sub_Ovf_Un", 2),
    ;

    final private String name;
    final private int arity;
    final private FunctionSymbol funcSym;

    /**
     * Mapping of enum constants to the associated function symbols
     */
    final static ImmutableMap<FunctionSymbol, PredefinedFunctions> SYM_MAP;
    static {
        LinkedHashMap<FunctionSymbol, PredefinedFunctions> sym_map =
            new LinkedHashMap<FunctionSymbol, PredefinedFunctions>();
        for (PredefinedFunctions f : PredefinedFunctions.values()) {
            sym_map.put(f.getSym(), f);
        }
        SYM_MAP = ImmutableCreator.create(sym_map);
    }

    private PredefinedFunctions(String name, int arity) {
        this.name = name;
        this.arity = arity;
        this.funcSym = FunctionSymbol.create(name, arity);
    }

    /**
     * Get arity of the associated function symbol.
     */
    public int getArity() {
        return this.arity;
    }

    /**
     * Get name of the associated function symbol.
     */
    public String getName() {
        return this.name;
    }

    /**
     * Get the associated function symbol.
     */
    public FunctionSymbol getSym() {
        return this.funcSym;
    }

    /**
     * Checks if <code>fs</code> is the function symbol associated to
     * <code>this</code> enum constant.
     */
    public boolean isSym(FunctionSymbol fs) {
        String name = fs.getName();
        return this.arity == fs.getArity()
                && this.name.equals(name);
    }

    boolean isSym(String name, int arity) {
        return this.arity == arity && this.name.equals(name);
    }

    /**
     * Returns the enum constant associated with <code>fs</code>.
     *
     * Returns null, iff no constant is associated with <code>fs</code>.
     */
    public static PredefinedFunctions getElem(FunctionSymbol fs) {
        return PredefinedFunctions.SYM_MAP.get(fs);
    }

}