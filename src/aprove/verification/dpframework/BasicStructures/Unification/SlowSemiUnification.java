package aprove.verification.dpframework.BasicStructures.Unification;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Class which contains an semiunification algorithm.
 * For more details on semiunification have a look at dag-based semiunification algorithm or
 * the solution extraction procedure
 *
 * @see SemiUnification.java, SemiUnificationSolutionExtraction.java
 *
 * @author Matthias Sondermann
 * @version $Id$
 */
public class SlowSemiUnification implements Exportable{

    /**
     * new function symbol "phi" which represents the matcher in the semiunification
     */
    private FunctionSymbol phi;
    /**
     * the terms of the semiunification problem (termPair.x sigma phi = termPair.y sigma)
     */
    private Pair<TRSTerm,TRSTerm> termPair;
    private TRSTerm term1;
    private TRSTerm term2;
    /**
     * lists of generated terms
     */
    private List<Pair<TRSTerm,TRSTerm>> finishList;
    private List<Pair<TRSTerm,TRSTerm>> workingList;
    /**
     * order of the variables of both terms - arbitrarily chosen
     */
    private List<TRSVariable> variableOrder;
    /**
     * this is a substitution of phi-functions: (phi^n(var)/t)
     */
    private Map<TRSTerm,TRSTerm> substitution;
    /**
     * flag which indicates if something is to be done or not
     */
    private boolean globalChange = true;
    /**
     * necessary for generating the semiunifier and the matcher
     */
    private FreshNameGenerator nameGen;

    /**
     * creates a new semiunification problem of the form:
     * is there a substitution sigma and a matcher rho so that rho(sigma(term1)) = sigma(term2)
     */
    public SlowSemiUnification(TRSTerm term1, TRSTerm term2){

        if(Globals.useAssertions){
            assert(term1!=null && term2!=null);
        }
        // initialize the needed information
        this.termPair = new Pair<TRSTerm,TRSTerm>(term1,term2);
        this.term1 = term1;
        this.term2 = term2;
        this.workingList = new ArrayList<Pair<TRSTerm,TRSTerm>>();
        this.finishList = new ArrayList<Pair<TRSTerm,TRSTerm>>();
        this.substitution = new LinkedHashMap<TRSTerm,TRSTerm>();

        // generate sets of variable and function symbol names used for creating phi and fresh variable names
        Set<String> varNames = new LinkedHashSet<String>();
        for(TRSVariable actVar : term1.getVariables()){
            varNames.add(actVar.getName());
        }
        for(TRSVariable actVar : term2.getVariables()){
            varNames.add(actVar.getName());
        }
        Set<String> funcNames = new LinkedHashSet<String>();
        for(FunctionSymbol actFunc : term1.getFunctionSymbols()){
            funcNames.add(actFunc.getName());
        }
        for(FunctionSymbol actFunc : term2.getFunctionSymbols()){
            funcNames.add(actFunc.getName());
        }
        Set<String> forbiddenNames = new LinkedHashSet<String>(varNames);
        forbiddenNames.addAll(funcNames);

        // now the phi function symbol is needed to construct the substitutions
        this.phi = PhiTermFunctions.createPhiFunctionSymbol(forbiddenNames);

        // initialise the name generator which is used for generating fresh variable names
        this.nameGen = new FreshNameGenerator(forbiddenNames, FreshNameGenerator.VARIABLES);

        // term1 gets a phi around it, so term1 = phi(term1)
        ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(1);
        args.add(term1);
        term1 = TRSTerm.createFunctionApplication(this.phi,ImmutableCreator.create(args));

        // add the two terms to the working list
        this.workingList.add(new Pair<TRSTerm,TRSTerm>(term1,term2));

        // create variable order
        this.variableOrder = new ArrayList<TRSVariable>();
        for(TRSVariable x : term1.getVariables()){
            if(!this.variableOrder.contains(x)) {
                this.variableOrder.add(x);
            }
        }
        for(TRSVariable x : term2.getVariables()){
            if(!this.variableOrder.contains(x)) {
                this.variableOrder.add(x);
            }
        }
    }

    /**
     * Generates the semiunifier and the matcher of the given semiunification problem
     * @return pair.x = matcher, pair.y = semiunifier; null if the given terms don??t semiunify
     */
    public Pair<TRSSubstitution,TRSSubstitution> getSubstitutions(){

        if(!this.semiUnify()){
            return null;
        }

        // the tow given terms semiunify, so compute the matcher and the semiunifier

        // initialize the name generator with the set of variable names that occur in the given termpair
        Set<TRSVariable> variables = new LinkedHashSet<TRSVariable>();
        Set<String> varNames = new LinkedHashSet<String>();
        for(TRSVariable var : this.termPair.x.getVariables()){
            variables.add(var);
            varNames.add(var.getName());
        }
        for(TRSVariable var : this.termPair.y.getVariables()){
            variables.add(var);
            varNames.add(var.getName());
        }
        this.nameGen = new FreshNameGenerator(varNames, FreshNameGenerator.VARIABLES);

        Set<Pair<TRSTerm,TRSTerm>> algoConstraints = new LinkedHashSet<Pair<TRSTerm,TRSTerm>>(this.workingList);
        SemiUnificationSolutionExtraction solex = new SemiUnificationSolutionExtraction(this.termPair,algoConstraints,this.phi,this.nameGen);
        return solex.getSubstitutions();
    }

    /**
     * algorithm which checks if term1 and term2 are semiunifiable
     * @return true if the two terms semiunify, else false
     */
    public boolean semiUnify(){
        // globalChange = true means that something changed in the last run
        while(this.globalChange){

            this.globalChange = false;

            // check every pair of terms
            while(!this.workingList.isEmpty()){
                // check next pair and remove it from actual list
                Pair<TRSTerm,TRSTerm> actPair = this.workingList.remove(0);
                // remove equations of the form t = t
                if(actPair.x.equals(actPair.y)){
                    continue;
                }
                // failure?
                // 1. failure: term1 = f(...), term2 = g(...)
                if(this.checkSymbolClash(actPair)){
                    // System.out.println("!!! clash failure !!!");
                    return false;
                }
                // 2. failure: term1 = phi^n(x), term2 = f(...,phi^m(x),...), m>=n
                if(this.checkBadLoop(actPair)){
                    // System.out.println("!!! bad loop failure !!!");
                    return false;
                }

                // try to push
                // phi(f(t_1,...,t_n) = f(phi(t_1),...,phi(t_n))
                Pair<TRSTerm,TRSTerm> pushPair = PhiTermFunctions.push(actPair, this.phi);
                if(!actPair.equals(pushPair)){
                    this.globalChange = true;
                }
                actPair = pushPair;

                // transitivity check
                // s = t and t = u => s = u
                List<Pair<TRSTerm,TRSTerm>> list = this.transitivity(actPair);

                for(Pair<TRSTerm,TRSTerm> pair : list){
                    this.addNewPair(pair);
                }

                // try to orient
                // term1 = term2 if term1 > term (see orient-function for order of terms)
                Pair<TRSTerm,TRSTerm> orientPair = this.orient(actPair);

                if(!actPair.equals(orientPair)){
                    this.globalChange = true;
                }
                actPair = orientPair;

                // try to substitute
                // phi^n(x) = term => substitute every phi^n(x) in the list
                if(PhiTermFunctions.termIsPhiFunction(actPair.x, this.phi)){
                    if(!this.substitution.containsKey(actPair.x)){
                        this.globalChange = true;
                        this.substitution.put(actPair.x,actPair.y);
                        for(Pair<TRSTerm,TRSTerm> termPair : this.workingList){
                            termPair = this.substitutePair(termPair);
                        }
                        for(Pair<TRSTerm,TRSTerm> termPair : this.finishList){
                            termPair = this.substitutePair(termPair);
                        }
                    }
                }

                // try to decompose
                // f(s_1,...s_n) = f(t_1,...,t_n) => s_1 = t_1, ..., s_n = t_n
                List<Pair<TRSTerm,TRSTerm>> dummyList = this.decompose(actPair);
                if(!dummyList.isEmpty()){
                    this.globalChange = true;
                    for(Pair<TRSTerm,TRSTerm> termPair : dummyList){
                        // check new pair for substitution and transitivity
                        this.addNewPair(termPair);
                    }
                }
                // if term can not be decomposed return it to the list
                else{
                    this.finishList.add(actPair);
                }
            }
            // copy finishlist to workinglist and repeat the whole procedure if something changed
            for(Pair<TRSTerm,TRSTerm> pair : this.finishList){
                this.workingList.add(pair);
            }
            this.finishList.clear();
        }
        // no more modifications possible => terms are semiunifiable
        return true;
    }

    /**
     * checks if left term of termpair = f(...) and right term = g(...) with f!=g
     * @return true if the symbols clash, else false
     */
    private boolean checkSymbolClash(Pair<TRSTerm,TRSTerm> termPair){
        // phis are not interesting for symbol clash so remove them
        TRSTerm term1 = PhiTermFunctions.removePhisInFront(termPair.x, this.phi);
        TRSTerm term2 = PhiTermFunctions.removePhisInFront(termPair.y, this.phi);

        if(!term1.isVariable() && !term2.isVariable()){
            TRSFunctionApplication func1 = (TRSFunctionApplication)term1;
            TRSFunctionApplication func2 = (TRSFunctionApplication)term2;
            if(!func1.getRootSymbol().equals(func2.getRootSymbol())){
                return true;
            }
        }
        return false;
    }

    /**
     * checks if left term of termpair = phi^n(x) and right term = f(...,phi^m(x),...) with m>=n
     * @return true if a bad loop exists, else false
     */
    private boolean checkBadLoop(Pair<TRSTerm,TRSTerm> termPair){
        TRSTerm term1 = termPair.x;
        TRSTerm term2 = termPair.y;

        if(PhiTermFunctions.termIsPhiFunction(term1, this.phi) && !term2.isVariable()){
            if(term2.hasSubterm(term1)){
                return true;
            }
        }
        return false;
    }

    /**
     * decomposes the termpair s=f(s_1,...,s_n) and t=f(t_1,...,t_n)
     * @return the list of the pairs s_1=t_1,...,s_n=t_n if s and t are function applications with the same functionsymbol, else the empty list is returned
     */
    private List<Pair<TRSTerm,TRSTerm>> decompose(Pair<TRSTerm,TRSTerm> termPair){
        TRSTerm leftTerm = termPair.x;
        TRSTerm rightTerm = termPair.y;
        List<Pair<TRSTerm,TRSTerm>> returnList = new ArrayList<Pair<TRSTerm,TRSTerm>>();

        // decompose only if left and right term are functions
        if(!leftTerm.isVariable() && !rightTerm.isVariable())
        {
            TRSFunctionApplication funcLeft = (TRSFunctionApplication) leftTerm;
            TRSFunctionApplication funcRight = (TRSFunctionApplication) rightTerm;

            if(funcLeft.getRootSymbol().equals(this.phi) || funcRight.getRootSymbol().equals(this.phi)){
                return returnList;
            }
            if(funcLeft.getRootSymbol().getArity()==0){
                return returnList;
            }

            for(int i=0; i<funcLeft.getArguments().size(); i++){
                TRSTerm leftChild = funcLeft.getArgument(i);
                TRSTerm rightChild = funcRight.getArgument(i);
                // add new child only if it was not generated earlier
                Pair<TRSTerm,TRSTerm> newPair = new Pair<TRSTerm,TRSTerm>(leftChild,rightChild);
                if(!this.isAlreadyInList(newPair) && !returnList.contains(newPair)){
                    returnList.add(newPair);
                }
            }
            return returnList;
        }
        return returnList;
    }

    /**
     * orients the termpair so that s = t iff s>t
     * @return a new term with orientated terms
     */
    private Pair<TRSTerm,TRSTerm> orient(Pair<TRSTerm,TRSTerm> termPair){
        TRSTerm leftTerm = termPair.x;
        TRSTerm rightTerm = termPair.y;

        Pair<TRSTerm,Integer> pair = PhiTermFunctions.removeAndCountPhisInFront(leftTerm, this.phi);
        int leftPhis = pair.y;
        TRSTerm leftWithoutPhis = pair.x;

        pair = PhiTermFunctions.removeAndCountPhisInFront(rightTerm, this.phi);
        int rightPhis = pair.y;
        TRSTerm rightWithoutPhis = pair.x;

        if(leftWithoutPhis.isVariable() && rightWithoutPhis.isVariable()){
            TRSVariable leftVar = (TRSVariable) leftWithoutPhis;
            TRSVariable rightVar = (TRSVariable) rightWithoutPhis;

            if(this.varIsGreaterThanVar(leftVar,rightVar)){
                return new Pair<TRSTerm,TRSTerm>(leftTerm,rightTerm);
            }
            if(leftVar.equals(rightVar) && leftPhis > rightPhis){
                return new Pair<TRSTerm,TRSTerm>(leftTerm,rightTerm);
            }
        }
        if(leftWithoutPhis.isVariable() && !rightWithoutPhis.isVariable()){
            return new Pair<TRSTerm,TRSTerm>(leftTerm,rightTerm);
        }
        if(!leftWithoutPhis.isVariable() && !rightWithoutPhis.isVariable()){
            return new Pair<TRSTerm,TRSTerm>(leftTerm,rightTerm);
        }

        return new Pair<TRSTerm,TRSTerm>(rightTerm,leftTerm);
    }

    /**
     * Checks every pair in list with <code>termpair</code> if a new term can be created (s=t and t=u => s=u).
     * @return A list of all pairs which could be created by the transitivity rule.
     */
    private List<Pair<TRSTerm,TRSTerm>> transitivity(Pair<TRSTerm,TRSTerm> termPair){
        // internal work with sets so that dublicates are removed efficiently
        Set<Pair<TRSTerm,TRSTerm>> dummySet = new LinkedHashSet<Pair<TRSTerm,TRSTerm>>();

        dummySet.addAll(this.transitivity(termPair,this.workingList));
        dummySet.addAll(this.transitivity(termPair,this.finishList));

        List<Pair<TRSTerm,TRSTerm>> retList = new LinkedList<Pair<TRSTerm,TRSTerm>>();
        for(Pair<TRSTerm,TRSTerm> pair : dummySet){
            if(!this.isAlreadyInList(pair)){
                retList.add(pair);
            }
        }
        return retList;
    }

    /**
     * This is only a helper function of transitivity(Pair<Term,Term> termPair).
     */
    private Set<Pair<TRSTerm,TRSTerm>> transitivity(Pair<TRSTerm,TRSTerm> termPair, List<Pair<TRSTerm,TRSTerm>> list){
        // this set has to be reduced at the end of this method to avoid a loop
        Set<Pair<TRSTerm,TRSTerm>> setOfNewPairs = new LinkedHashSet<Pair<TRSTerm,TRSTerm>>();

        TRSTerm leftTerm = termPair.x;
        TRSTerm rightTerm = termPair.y;

        for(Pair<TRSTerm,TRSTerm> working : list){
            // case:
            TRSTerm leftWorking = working.x;
            TRSTerm rightWorking = working.y;

            if(rightWorking.equals(leftTerm)){
                setOfNewPairs.add(new Pair<TRSTerm,TRSTerm>(leftWorking,rightTerm));
            }
            if(leftWorking.equals(rightTerm)){
                setOfNewPairs.add(new Pair<TRSTerm,TRSTerm>(leftTerm,rightWorking));
            }
        }
        Set<Pair<TRSTerm,TRSTerm>> retSet = new LinkedHashSet<Pair<TRSTerm,TRSTerm>>();
        for(Pair<TRSTerm,TRSTerm> pair : setOfNewPairs){
            if(!this.isAlreadyInList(pair)){
                retSet.add(pair);
            }
        }
        return retSet;
    }

    /**
     * Substitutes every possible subterm of both terms.
     * @return A new pair with the substituted terms.
     */
    private Pair<TRSTerm,TRSTerm> substitutePair(Pair<TRSTerm,TRSTerm> termPair){
        // get all actual substitutions
        for(TRSTerm substTerm : this.substitution.keySet()){
            // substitute only if the substitution is not equal to the equation
            Pair<TRSTerm,TRSTerm> substPair = new Pair<TRSTerm,TRSTerm>(substTerm,this.substitution.get(substTerm));
            if(termPair.equals(substPair)){
                return termPair;
            }
            termPair.x = termPair.x.replaceAll(substTerm,this.substitution.get(substTerm));
            termPair.y = termPair.y.replaceAll(substTerm,this.substitution.get(substTerm));
        }
        return termPair;
    }

    /**
     * Tries to substitute the new pair and tries to find new terms because of transitivity. after that the new pair is added to the actual list.
     * @param termPair
     */
    private void addNewPair(Pair<TRSTerm,TRSTerm> termPair){
        this.finishList.add(termPair);
        if(!this.isAlreadyInList(termPair)){
            // try to substitute
            termPair = this.substitutePair(termPair);
            // transitivity? => add all terms
            List<Pair<TRSTerm,TRSTerm>> list = this.transitivity(termPair);
            for(Pair<TRSTerm,TRSTerm> pair : list){
                this.addNewPair(pair);
            }
        }
    }

    /**
     * @return True iff <code>x</code>><code>y</code>, otherwise false (see variable order).
     */
    private boolean varIsGreaterThanVar(TRSVariable x, TRSVariable y){
        for(TRSVariable var: this.variableOrder){
            if(var.equals(x) && !var.equals(y)) {
                return true;
            }
            if(var.equals(y)) {
                return false;
            }
        }
        return false;
    }

    /**
     * Checks if <code>termPair</code> is already in list of generated pairs.
     */
    private boolean isAlreadyInList(Pair<TRSTerm,TRSTerm> termPair){
        if(this.workingList.contains(termPair)){
            return true;
        }
        if(this.finishList.contains(termPair)){
            return true;
        }
        return false;
    }

    /**
     * Be aware of the side effect this method can make! The algorithm should only run once but is called here. So be sure
     * that the algorithm was never started before.
     */
    @Override
    public String export(Export_Util eo){
        return this.export(eo,false);
    }

    public String export(Export_Util eo, boolean debugInfo){
        StringBuilder s = new StringBuilder();
        s.append("SemiUnification problem: " + this.term1 + " <=? " + this.term2 + "\n\n");
        boolean semiUnify = this.semiUnify();

        if(semiUnify){
            s.append("These terms semiunify" + eo.linebreak() + eo.linebreak());
            long a = 0;
            long b = 0;
            if(debugInfo){
                a = System.nanoTime();
            }
            Pair<TRSSubstitution,TRSSubstitution> substPair = this.getSubstitutions();
            if(debugInfo){
                b = System.nanoTime();
            }
            TRSSubstitution ma = substPair.x;
            TRSSubstitution se = substPair.y;

            s.append("Matcher:     " + substPair.x + eo.linebreak());
            s.append("Semiunifier: " + substPair.y);

            if(debugInfo){
                TRSTerm newTerm1 = this.term1.applySubstitution(se).applySubstitution(ma);
                TRSTerm newTerm2 = this.term2.applySubstitution(se);
                s.append(eo.linebreak() + eo.linebreak());
                s.append("The terms after applying the substitutions:" + eo.linebreak());
                s.append(newTerm1 + " and " + eo.linebreak() + newTerm2);
                s.append(eo.linebreak() + eo.linebreak());
                s.append("It took " + ((b-a)/1000000) + " ms");
            }
        }
        else{
            s.append("These terms do not semiunify");
        }
        return s.toString();
    }

    @Override
    public String toString(){
        return this.export(new PLAIN_Util(),false);
    }

    /**
     * This prints out some extra stuff like used time or the terms after applying the substitutions.
     */
    public String debugOutput(Export_Util eo){
        return this.export(eo,true);
    }
}