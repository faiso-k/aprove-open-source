package aprove.verification.dpframework.BasicStructures.Unification;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Class which encapsulates some static functions which do some helpfull
 * stuff with phi-terms (used by the semiunification algorithm and its
 * solution extraction).
 *
 * @author Matthias Sondermann
 * @version $Id$
 */
public abstract class PhiTermFunctions {

    /**
     * Creates a new function symbol phi with a fresh name which does not occur in term1 and term2.
     */
    public static FunctionSymbol createPhiFunctionSymbol(Set<String> forbiddenNames){
        String name = "phi";
        while(forbiddenNames.contains(name)){
            name += "i";
        }
        // create a new function symbol with name phi{i}* and arity 1
        return FunctionSymbol.create(name,1);
    }


    /**
     * @return A term of the form phi^n(term) where n=numberOfPhis and all phis are pushed as far innermost as possible.
     */
    public static TRSTerm constructPhiTerm(TRSTerm term, int numberOfPhis, FunctionSymbol phi){
        TRSTerm retTerm = term;
        ArrayList<TRSTerm> phiArgs;
        for(int i=0; i<numberOfPhis; i++){
            phiArgs = new ArrayList<TRSTerm>();
            phiArgs.add(retTerm);
            retTerm = TRSTerm.createFunctionApplication(phi,ImmutableCreator.create(phiArgs));
        }
        return PhiTermFunctions.push(retTerm, phi);
    }

    /**
     * Counts the number of outermost phis of <code>term</code>, i.e. return n when <code>term</code>=phi^n(rest).
     */
    public static int countPhisInFront(TRSTerm term, FunctionSymbol phi){
        int ret = 0;
        if(term.isVariable()) {
            return 0;
        }
        TRSFunctionApplication f = (TRSFunctionApplication) term;

        while(f.getRootSymbol().equals(phi)){
            ret++;
            term = f.getArgument(0);
            if(term.isVariable()){
                return ret;
            }
            else{
                f = (TRSFunctionApplication)term;
            }
        }
        return ret;
    }

    /**
     * Pushes all phis as far innermost as possible.
     */
    public static TRSTerm push(TRSTerm term, FunctionSymbol phi){
        return PhiTermFunctions.push(term, phi, 0);
    }

    /**
     * Pushes all phis of the left and right term of the termpair.
     * @return A new pair of terms with all phis pushed innermost
     */
    public static Pair<TRSTerm,TRSTerm> push(Pair<TRSTerm,TRSTerm> termPair, FunctionSymbol phi){
        return new Pair<TRSTerm,TRSTerm>(PhiTermFunctions.push(termPair.x, phi, 0),PhiTermFunctions.push(termPair.y, phi, 0));
    }

    /**
     * Pushes all <code>phiCount</code> phis into the term.
     * @return a new term with all phis pushed innermost
     */
    public static TRSTerm push(TRSTerm term, FunctionSymbol phi, int phiCount){
        // to avert generating a new term in every position the appearances of phis are count
        // if <code>term</code> is a variable add counted phis
        Pair<TRSTerm,Integer> actPair = PhiTermFunctions.removeAndCountPhisInFront(term,phi);
        int numberOfPhis = actPair.y + phiCount;
        term = actPair.x;
        if(!term.isVariable()){
            TRSFunctionApplication func = (TRSFunctionApplication) term;
            ArrayList<TRSTerm> newChildren = new ArrayList<TRSTerm>();
            for(TRSTerm child : func.getArguments()){
                newChildren.add(PhiTermFunctions.push(child,phi,numberOfPhis));
            }
            return TRSTerm.createFunctionApplication(func.getRootSymbol(),ImmutableCreator.create(newChildren));
        }
        else{
            for(int i=1;i<=numberOfPhis;i++){
                ArrayList<TRSTerm> oneChild = new ArrayList<TRSTerm>(1);
                oneChild.add(term);
                term = TRSTerm.createFunctionApplication(phi,ImmutableCreator.create(oneChild));
            }
            return term;
        }
    }

    /**
     * Counts the number of phis in front of <code>term</code> and removes them.
     * @return pair.x = number of phis in front, pair.y = term without phis in front
     */
    public static Pair<TRSTerm,Integer> removeAndCountPhisInFront(TRSTerm term, FunctionSymbol phi){
        int count=0;
        while(true){
            if(term.isVariable()) {
                return new Pair<TRSTerm,Integer>(term,count);
            }
            TRSFunctionApplication func = (TRSFunctionApplication) term;
            if(func.getRootSymbol().equals(phi)){
                count++;
                term = func.getArgument(0);
            } else {
                return new Pair<TRSTerm,Integer>(term,count);
            }
        }
    }

    /**
     * Returns a new term without the phis in front.
     * @return return t if <code>term</code> is of the form phi^n(t), n>=0
     */
    public static TRSTerm removePhisInFront(TRSTerm term, FunctionSymbol phi){
        while(!term.isVariable()){
            TRSFunctionApplication func = (TRSFunctionApplication) term;
            if(!func.getRootSymbol().equals(phi)) {
                return term;
            }
            term = func.getArgument(0);
        }
        return term;
    }

    /**
     * Is <code>term</code> of the form phi^n(x), n>=0?
     * @return true if <code>term</code> is a phifunction, else false
     */
    public static boolean termIsPhiFunction(TRSTerm term, FunctionSymbol phi){
        while(!term.isVariable()){
            TRSFunctionApplication f = (TRSFunctionApplication) term;
            if(!f.getRootSymbol().equals(phi)){
                return false;
            }
            term = f.getArgument(0);
        }
        return true;
    }

    /**
     * The caller has to verify that <code>term</code> is a phi-function!
     * @return x iff <code>term</code> is of the form phi^n(x), n>=0
     */
    public static TRSVariable getVarOfPhiFunction(TRSTerm term){
        while(!term.isVariable()){
            TRSFunctionApplication f = (TRSFunctionApplication) term;
            term = f.getArgument(0);
        }
        return (TRSVariable) term;
    }
}
