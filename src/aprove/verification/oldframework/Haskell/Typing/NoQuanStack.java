package aprove.verification.oldframework.Haskell.Typing;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.Collectors.*;


/**
 * @author Stephan Swiderski
 * @version $Id$
 *
 * The NoQuanStack is a GroupStack over HaskellSyms
 *
 * For each function or mrb a new Group is created in the
 * noQuanStack to collect all HaskellSyms representing type-variables
 * for which it is forbidden to be allquantified
 *
 * If a substitution ? is applied to a variable x in the noQuanStack
 * the forbiddance of allquantification is tranfered to the variables in ?(x)
 * i.e. the variables of ?(x) are collected in the same level as x
 *
 */
public class NoQuanStack extends GroupStack<HaskellSym> {

    /**
     * applies a substitution subs to variables in the noQuanStack.
     * It adds the variables of subs(x) also to thes same level as x,
     * if x is in the NoQuanStack.
     */
    public void apply(HaskellSubstitution subs){
        for (Map.Entry<HaskellSym,HaskellObject>  e : subs.entrySet()){
            HaskellSym sym = e.getKey();

            // XXX DEBUG
            if (aprove.Globals.DEBUG_SWISTE || aprove.Globals.DEBUG_MATRAF) {
                //System.out.println("Search:"+sym+" :: "+group+" -> "+e.getValue());
            }

            int i = this.remove(sym);
            if (i > -1) {
                Set<HaskellSym> nsyms = new HashSet<HaskellSym>();
                e.getValue().visit((new FreeVarSymCollector(nsyms)));
                this.addToGroup(i,nsyms);
            }
        }
    }

    /**
     * adds all variables occuring in the HaskellObject ho
     * to this NoQuanStack in the current level.
     */
    public void addHoToPeekGroup(HaskellObject ho){
        Set<HaskellSym> syms = new HashSet<HaskellSym>();
        ho.visit((new FreeVarSymCollector(syms)));
        this.addToPeekGroup(syms);
    }


}
