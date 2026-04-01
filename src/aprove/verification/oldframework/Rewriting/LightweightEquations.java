package aprove.verification.oldframework.Rewriting ;

import java.util.*;

import aprove.verification.oldframework.Syntax.*;

/**
 *  A hash set of lightweight equations with some additional functionality.
 *  @author Stephan Falke
 *  @version $Id$
 */

public class LightweightEquations extends LinkedHashSet<LightweightEquation> {

    public static LightweightEquations create() {
    return new LightweightEquations();
    }

    public static LightweightEquations create(Collection<TRSEquation> E) {
    LightweightEquations res = new LightweightEquations();
    Iterator i = E.iterator();
    while(i.hasNext()) {
        res.add(LightweightEquation.create((TRSEquation)i.next()));
    }
    return res;
    }

    /** Returns the function symbols occuring in the equations contained in this
     * set.
     */
    public List getSignature() {
    Set sig = new LinkedHashSet();
    Iterator i = this.iterator();
    while(i.hasNext()) {
        LightweightEquation eq = (LightweightEquation)i.next();
        sig.addAll(eq.getOneSide().getFunctionSymbols());
        sig.addAll(eq.getOtherSide().getFunctionSymbols());
    }
    List result = new Vector();
    i = sig.iterator();
    while(i.hasNext()) {
        result.add(((Symbol)i.next()).getName());
    }
    return result;
    }

    /** Returns some element of this set, <code>null</code> if the set is empty.
     */
    public LightweightEquation getArbitraryElement() {
    Iterator i = this.iterator();
    if(i.hasNext()) {
        return (LightweightEquation)i.next();
    }
    else {
        return null;
    }
    }

    /** Remove trivial equations from this set and return a new set.
     */
    public LightweightEquations removeTrivials() {
    LightweightEquations result = LightweightEquations.create();
    Iterator i = this.iterator();
    while(i.hasNext()) {
        LightweightEquation eq = (LightweightEquation)i.next();
        if(!eq.isTrivial()) {
            result.add(eq);
        }
    }
    return result;
    }


    public LightweightEquations deepcopy() {
    LightweightEquations result = LightweightEquations.create();
    Iterator i = this.iterator();
    while(i.hasNext()) {
        result.add(((LightweightEquation)i.next()).deepcopy());
    }
    return result;
    }

}
