package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;
import java.util.logging.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;


/** For every DefFunctionApp this visitor meets, it simply looks into the
 * countermap, takes the integer stored for the symbol of the DefFunctionApp
 * increases it by 1 and sets the attribute "symbolCount" of the term to the new value.
 * The increased value is then stored back into the map.
 *
 * If the map does not contain any enries for the symbol, the counting starts with 1.
 *
 * This results in a unique int ID for every occurence of every DefFunctionSymbol
 * @author Christian Kaeunicke
 * @version $Id$
 */
public class AddSymbolCountVisitor extends CoarseGrainedDepthFirstTermVisitor {
    public static Logger logger = Logger.getLogger("aprove.verification.oldframework.Algebra.Terms.Visitors");

    Map<DefFunctionSymbol,Integer> counter;

    public AddSymbolCountVisitor(Map<DefFunctionSymbol,Integer> counter) {
    this.counter = counter;
    };

    @Override
    public void outFunctionApp(AlgebraFunctionApplication f) {
    if (f instanceof DefFunctionApp) {
        DefFunctionSymbol symbol = (DefFunctionSymbol) ((DefFunctionApp) f).getSymbol();
        Integer count = this.counter.get(symbol);
        if (count == null) {
            count = Integer.valueOf(1);
        }
        f.setAttribute("symbolCount", count);
        count = Integer.valueOf(count.intValue() + 1);
        this.counter.put(symbol, count);
    };
    };
}
