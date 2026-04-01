package aprove.verification.oldframework.Rewriting.Transformers;

import java.util.*;

import aprove.verification.oldframework.Syntax.*;

/** An special defined symbol that is generated in the transformation of
 * conditional programs.
 * @author Stephan Falke
 * @version $Id$
 */

public class IfSymbol extends DefFunctionSymbol {

    public static final String PREFIX = "if_";
    public static final String INFIX = "_";

    private static Map sym_cache = new HashMap();

    private String shortName;
    private int number;
    private String fullName;

    private IfSymbol(String fullName, String shortName, int number, List<Sort> argsorts, Sort sort) {
    super(fullName, argsorts, sort);
    this.fullName = fullName;
    this.number = number;
    this.shortName = shortName;
    }


    /** Returns true iff
     *   - both symbols have the same name
     *   - their sorts are equal
     */
    @Override
    public boolean equals(Object o) {
        if (o instanceof IfSymbol) {
            boolean eq = super.equals(o);
            IfSymbol that = (IfSymbol)o;
            return eq && this.argSorts.equals(that.argSorts) && this.sort.equals(that.sort);
        } else {
            return false;
        }
    }


    /** Returns a new instance of IfSymbol.
     * The name will be <code>PREFIX+name+number</code>.
     */
    public static IfSymbol create(String name, int number, List<Sort> argsorts, Sort sort) {
    String fullName = IfSymbol.PREFIX + name + IfSymbol.INFIX + Integer.valueOf(number).toString();
        IfSymbol sym = new IfSymbol(fullName, name, number, argsorts, sort);
        if (IfSymbol.sym_cache.containsKey(sym)) {
            sym = (IfSymbol)IfSymbol.sym_cache.get(sym);
        } else {
            IfSymbol.sym_cache.put(sym, sym);
        }
        return sym;
    }

    /** Returns the name the IfSymbol would get.
     */
    public static String createName(String name, int number) {
    return IfSymbol.PREFIX + name + IfSymbol.INFIX + Integer.valueOf(number).toString();
    }

    /** Returns the name of the symbol that was used to create this IfSymbol.
     */
    public String getShortName() {
    return this.shortName;
    }

    /** Returns the number that was used to create this IfSymbol.
     */
    public int getNumber() {
    return this.number;
    }


    @Override
    public Symbol deepcopy() {
        IfSymbol copyIfSym = new IfSymbol(new String(this.fullName), new String(this.shortName), this.number, new Vector<Sort>(this.argSorts), this.sort);
        copyIfSym.setTermination(this.termination);
        return copyIfSym;
    }
}
