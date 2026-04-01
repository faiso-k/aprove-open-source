package aprove.verification.oldframework.Rewriting.SemanticLabelling;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.MaxMinPolynomials.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * NOTE: All Function Symbols in rules must not have an arity bigger than 2.
 *
 * @author patwie
 *
 */

public class ModelSearch {

    private static Logger log =
        Logger.getLogger("aprove.verification.oldframework.Rewriting.SemanticLabelling.ModelSearch");


    private final Set<Rule> rRules;
    private final Set<FunctionSymbol> signature;
    private final int cSS;
    private final BigInteger maxCarrierElement;
    private final boolean searchQM;
    private final boolean difficultSignature = false;
    private       int fullInterpretationExpansions = 0;
    private final int maxFullExpansions = 0;
    private LinkedList<MyModel> initialModels;

    public ModelSearch(Collection<Rule> rules, int carrier, boolean searchqm, boolean difficultSignature) {
        if(Globals.useAssertions) {
            boolean arityConflict = false;
            Iterator<Rule> ruleIter = rules.iterator();
            while((!arityConflict) && ruleIter.hasNext()) {
                Set<FunctionSymbol> auxSet = ruleIter.next().getFunctionSymbols();
                Iterator<FunctionSymbol> iter = auxSet.iterator();
                while((!arityConflict) && iter.hasNext()) {
                    arityConflict = (iter.next().getArity() > 2);
                }
            }
            if(arityConflict) {
                throw new RuntimeException("A function symbol must not have an arity bigger than 2!");
            }
        }

        this.rRules = new LinkedHashSet<Rule>(rules);
        Set<FunctionSymbol> auxSet = new LinkedHashSet<FunctionSymbol>();
        for(Rule r : this.rRules) {
            auxSet.addAll(r.getFunctionSymbols());
        }
        this.signature = auxSet;
        this.cSS = carrier;
        this.maxCarrierElement = BigInteger.valueOf(carrier - 1);
        this.searchQM = searchqm;
        //this.difficultSignature = difficultSignature;
    }

    /**
     * Constructor with default values. They are: <br>
     * Carrier = -1, representing the natural numbers <br>
     * searchQM = false, only search for Models <br>
     * difficultSignature = false, full searchspace <br>
     * @param rules, the TRS for which Models should be found.
     */
    public ModelSearch(Collection<Rule> rules) {
        if(Globals.useAssertions) {
            boolean arityConflict = false;
            Iterator<Rule> ruleIter = rules.iterator();
            while((!arityConflict) && ruleIter.hasNext()) {
                Set<FunctionSymbol> auxSet = ruleIter.next().getFunctionSymbols();
                Iterator<FunctionSymbol> iter = auxSet.iterator();
                while((!arityConflict) && iter.hasNext()) {
                    arityConflict = (iter.next().getArity() >= 3);
                }
            }
            if(arityConflict) {
                throw new RuntimeException("A function symbol must not have an arity bigger than 2!");
            }
        }

        this.rRules = new LinkedHashSet<Rule>(rules);
        Set<FunctionSymbol> auxSet = new LinkedHashSet<FunctionSymbol>();
        for(Rule r : this.rRules) {
            auxSet.addAll(r.getFunctionSymbols());
        }
        this.signature = auxSet;
        this.cSS = -1;
        this.maxCarrierElement = BigInteger.valueOf(-2); // Must be < 0
        this.searchQM = true;
       // this.difficultSignature = false;
    }

    /**
     * Calculates all Models (and QuasiModels)
     * @return a list of all possible Models (and QuasiModels).
     */
    public LinkedList<MyModel> getAllModels () {
        LinkedList<MyModel> modelList;
        Iterator<Rule> ruleIter = this.rRules.iterator();
        if(this.initialModels == null) {
            Rule firstRule = ruleIter.next();
            this.initialModels = this.buildInitialModels(firstRule.getLeft());
        }
        else {
            throw new RuntimeException("Not yet implemented!");
        }
        modelList = this.calculateInterpretationsForSetOfRules(
                this.rRules, this.initialModels);
        modelList = this.completeAllModels(modelList);

        return modelList;
    }

    /**
     * Right now a convenience method, since the calculation can not start
     * with an empty list of models. Later this can be used as a heuristic
     * to start the calculation with an especially choosen rule, which has some
     * properties which speed up the model finding process.
     * @param fApp a function symbol by which the list is extendend
     * @return a nonempty list of model candidats.
     */
    private LinkedList<MyModel> buildInitialModels(TRSFunctionApplication fApp) {
        LinkedList<MyModel> resultList = new LinkedList<MyModel>();
        FunctionSymbol rootSymbol = fApp.getRootSymbol();
        Set<MaxMinPolynomial> auxSet = InterpretationPoolCreator.createIntSet(this.cSS, rootSymbol.getArity());
        Iterator<MaxMinPolynomial> iter = auxSet.iterator();
        while(iter.hasNext()) {
            resultList.add(MyModel.create(rootSymbol, iter.next(), this.cSS));
        }
        return resultList;
    }

    /**
     *
     * @param rules the rules of the TRS
     * @param initialModelList a nonempty list of Model candidats
     * @return a hopefuly nonempty list of models (and quasimodels)
     */
    private LinkedList<MyModel> calculateInterpretationsForSetOfRules (
            Set<Rule> rules, Collection<MyModel> initialModelList) {
        LinkedList<MyModel> workingList = new LinkedList<MyModel> (initialModelList);
        for(Rule actualRule : rules) {
            workingList = this.calculateIntSetForRule(actualRule, workingList);
        }
        return workingList;
    }


    private LinkedList<MyModel> calculateIntSetForRule(
            Rule rule, Collection<MyModel> modelCollection) {
        ModelSearch.log.fine("Iterative Model search for Rule: " + rule.toString() +"\n");
        long s = System.nanoTime();
        HashMap<LinkedList<MyModel>, LinkedList<MyModel>> cutDownModelMap =
            new HashMap<LinkedList<MyModel>, LinkedList<MyModel>>();

        LinkedList<MyModel> resultList =
            new LinkedList<MyModel>(modelCollection);

        Pair<InterpretationStatus, FunctionSymbol> statusPairOfRule =
            new Pair<InterpretationStatus, FunctionSymbol>(null, null);

        MyModel actualModel;

        int position = 0;
        while(position < resultList.size()) {
            actualModel = resultList.get(position);
            ModelSearch.log.fine("\n\nIterative Model search, actual size of list of modelcandidats: " + resultList.size() +"\n");
            ModelSearch.log.finest("actual Model: " + actualModel.toString() +"\n");

            statusPairOfRule = this.calculateIntStatusOfRule(rule, actualModel);
            if(statusPairOfRule.y == null) {// actualModel was defined enough to calculate the mmps
                                            // of both sides of the current rule.
                InterpretationStatus statusOfRule = statusPairOfRule.x;
                if(statusOfRule == InterpretationStatus.Incompareable) {//actualModel is no use, delete it
                    resultList.remove(position);
                }
                else{
                    if(this.searchQM) {
                        InterpretationStatus actualModelStatus = actualModel.getStatus();
                        if(actualModelStatus == statusPairOfRule.x) {//Nothing to change
                            position++;
                        }
                        else {
                            if(actualModelStatus == InterpretationStatus.Quasi) {
                                //We can be sure that only weakly monotonic functions are used.
                                //So we only have to increment the index position.
                                position++;
                            }
                            else {
                                if(actualModelStatus == InterpretationStatus.QuasiTry) {
                                    //We can be sure that only weakly monotonic functions are used.
                                    //So we only have to confirm the QuasiModel status.
                                    actualModel = actualModel.changeInterpretationStatus(InterpretationStatus.Quasi);
                                    resultList.set(position, actualModel);
                                    position++;
                                }
                                else {
                                    //actualModelStatus has to be try, so it solemly depends
                                    //upon the status of the current rule how to proceed.
                                    if(statusPairOfRule.x == InterpretationStatus.Model) {
                                        actualModel = actualModel.changeInterpretationStatus(InterpretationStatus.Model);
                                        resultList.set(position, actualModel);
                                        position++;
                                    }
                                    else {
                                        //Since the actual rule is only a QuasiModel
                                        //we have to check now that all Functions are weakly monotonic,
                                        //otherwise we have to delete the actualModel.
                                        if(actualModel.onlyWeaklyMonotonicFunctionsUsed()) {
                                            actualModel = actualModel.changeInterpretationStatus(InterpretationStatus.Quasi);
                                            resultList.set(position, actualModel);
                                            position++;
                                        }
                                        else {
                                            resultList.remove(position);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    else {
                        if(statusPairOfRule.x == InterpretationStatus.Model) {
                            actualModel = actualModel.changeInterpretationStatus(InterpretationStatus.Model);
                            resultList.set(position, actualModel);
                            position++;
                        }
                        else {//the actualModel is only a QuasiModel for the current rule,
                              //since we do not want QuasiModels simply delete it.
                            resultList.remove(position);
                        }
                    }
                }
            }
            else {
                // the actualModel needs to be extended to calculate the mmps of both sides of the current rule
                resultList.remove(position);

                //Debugging: Looking for duplicate models added to resultList
                /*
                List<MyModel> debugList = actualModel.extendInterpretation(statusPairOfRule.y);
                for(MyModel mod : debugList) {
                    if(resultList.contains(mod)) {
                        log.fine("\n duplicate model! : " + mod.toString() +"\n");
                    }
                }
                */
                LinkedList<MyModel> cutDownModelList = null;
                if(false) { // || this.difficultSignature) {
                    if(this.cSS < 2) {
                        if(statusPairOfRule.y == rule.getRootSymbol()) {
                            cutDownModelList = actualModel.extendInterpretation(statusPairOfRule.y, rule, true);
                        }
                        else {
                            cutDownModelList = actualModel.extendInterpretation(statusPairOfRule.y, rule, true);
                        }
                    }
                    else {
                        if(statusPairOfRule.y.getArity() > 1) {
                            if(this.fullInterpretationExpansions < this.maxFullExpansions) {
                                this.fullInterpretationExpansions ++;
                                cutDownModelList = actualModel.extendInterpretation(statusPairOfRule.y, rule, true);
                            }
                            else {
                                cutDownModelList = actualModel.extendInterpretation(statusPairOfRule.y, rule, true);
                            }
                        }
                        else {
                            cutDownModelList = actualModel.extendInterpretation(statusPairOfRule.y, rule, true);
                        }
                    }
                }
                else {
                    cutDownModelList = actualModel.extendInterpretation(statusPairOfRule.y, rule, true);
                }
                LinkedList<MyModel> workingList = cutDownModelMap.get(cutDownModelList);
                if(workingList == null) {
                    workingList = this.calculateIntSetForRule(rule, cutDownModelList);
                    cutDownModelMap.put(cutDownModelList, workingList);
                }
                workingList = this.merge(workingList, actualModel);
                resultList.addAll(position, workingList);
                position = (position + workingList.size());

                /*
                if(Globals.DEBUG_PATWIE) {
                    if((resultList.size() > 300) && (resultList.size()<310)) {
                        int counter = 0;
                        log.fine("Iterative Model search, actual size of list of modelcandidats: " + resultList.size() +"\n");
                        for(int j=0; j<resultList.size(); j++){
                            MyModel comparecandidat = resultList.get(j);
                            for(int i=j; i<resultList.size(); i++){
                                MyModel dummy = resultList.get(i);
                                if(comparecandidat.equals(resultList.get(i))){
                                    counter++;
                                    //log.fine("Error!! \n" + comparecandidat.toString() +"\n" + resultList.get(i).toString() +"\n");
                                }
                            }
                        }
                        log.fine("\nNumber of duplicate models: " + counter +"\n");
                    }
                }
                */
            }
        }
        long e = System.nanoTime();
        ModelSearch.log.fine("Calculation of interpret Set for one Rule : " + ((e-s)/1000000) +" ms\n");
       return resultList;
    }



    private Pair<InterpretationStatus, FunctionSymbol> calculateIntStatusOfRule(Rule rule, MyModel actModel) {
        Pair<InterpretationStatus, FunctionSymbol> resultPair =
            new Pair<InterpretationStatus, FunctionSymbol>(InterpretationStatus.Incompareable, null);
        TRSFunctionApplication lhs = rule.getLeft();
        TRSTerm rhs = rule.getRight();
        Pair<MaxMinPolynomial, FunctionSymbol> valuePairLhs = actModel.calculateMMpolyOfTerm(lhs);
        if(valuePairLhs.x != null) {//Calculation was successful, actual interpretation was defined enough
            Pair<MaxMinPolynomial, FunctionSymbol> valuePairRhs = actModel.calculateMMpolyOfTerm(rhs);
            if(valuePairRhs.x != null) {//Calculation was successful, actual interpretation was defined enough
                InterpretationStatus actStatus = this.compareTwoMMPs(valuePairLhs.x, valuePairRhs.x);
                if( actStatus == InterpretationStatus.Model || actStatus == InterpretationStatus.Quasi) {
                    resultPair.setKey(actStatus);
                }
                else {
                    if(!(actStatus == InterpretationStatus.Incompareable)) {
                        throw new RuntimeException("Illegal result for comparison of two MaxMinPolynomials!");
                    }
                }
            }
            else {//interpretation of MyModel actModel was not defined enough for
                  //the right hand side, valuePairRhs.getValue() returns the function symbol
                  //that needs to be extended in the interpretation of actModel.
                resultPair.setValue(valuePairRhs.getValue());
            }
        }
        else {//interpretation of MyModel actModel was not defined enough for
            //the left hand side, valuePairLhs.getValue() returns the function symbol
            //that needs to be extended in the interpretation of actModel.
            resultPair.setValue(valuePairLhs.getValue());
        }
        return resultPair;
    }


    public InterpretationStatus compareTwoMMPs (
            MaxMinPolynomial lhsMMP, MaxMinPolynomial rhsMMP) {
       // long s = System.nanoTime();
        if(this.cSS == -1) { //We are working on natural numbers!
            return this.compareTwoMMPsOnNaturals(lhsMMP, rhsMMP);
        }
        else{ //We are working on a finite carrier set!
            InterpretationStatus iStat = this.compareTwoMMPsModulo(lhsMMP, rhsMMP);
           // long e = System.nanoTime();
           // System.out.println("Comparison of two MMP's : " + ((e-s)/1000));
            return iStat;
        }
    }


    private InterpretationStatus compareTwoMMPsOnNaturals (
            MaxMinPolynomial lhsMMP, MaxMinPolynomial rhsMMP) {
        //Trivial, if both MMpolys are equal they have the same value.
        if(lhsMMP.equals(rhsMMP)) {
             return InterpretationStatus.Model;
        }
        else {
            if(rhsMMP.getMetaInf() == MMPolyMetaInf.Constant) {
                BigInteger rhsConstant = rhsMMP.getVarPolynomial().getConstantPart().getNumericalAddend();
                if(rhsConstant.signum() == 0) {
                    return InterpretationStatus.Quasi;
                }
                if(lhsMMP.getMetaInf() == MMPolyMetaInf.Constant) {
                    BigInteger lhsConstant = lhsMMP.getVarPolynomial().getConstantPart().getNumericalAddend();
                    if((lhsConstant.subtract(rhsConstant)).signum() == 1 ) {
                        return InterpretationStatus.Quasi;
                    }
                    else {
                        return InterpretationStatus.Incompareable;
                    }
                }
                else {
                    return InterpretationStatus.Incompareable;
                }
            }
            else {
                if(rhsMMP.getMetaInf() == MMPolyMetaInf.VarPoly) {
                    if(lhsMMP.getMetaInf() == MMPolyMetaInf.VarPoly) {
                        VarPolynomial rhsVP = rhsMMP.getVarPolynomial();
                        VarPolynomial lhsVP = lhsMMP.getVarPolynomial();
                        VarPolynomial diffVP = lhsVP.minus(rhsVP);
                        if(diffVP.allPositive()) {
                            return InterpretationStatus.Quasi;
                        }
                        else {
                            return InterpretationStatus.Incompareable;
                        }
                    }
                    else {
                        if(lhsMMP.getMetaInf() == MMPolyMetaInf.MaxInterpretation) {
                            //use transitivity property of maximum
                            return ModelSearch.myCheck(lhsMMP.getAllMinSets(), rhsMMP.getAllMinSets());
                        }
                        return InterpretationStatus.Incompareable;
                    }
                }
                else {
                    if(rhsMMP.getMetaInf() == MMPolyMetaInf.MinInterpretation) {
                        if(lhsMMP.getMetaInf() == MMPolyMetaInf.MinInterpretation) {
                            ImmutableMap<String, ImmutableList<VarPolynomial>> lhsMap =
                                lhsMMP.getVariableMapping().iterator().next();
                            ImmutableMap<String, ImmutableList<VarPolynomial>> rhsMap =
                                rhsMMP.getVariableMapping().iterator().next();
                            boolean qModel = MaxMinPolynomial.minTermDomination(
                                                    lhsMap, rhsMap);
                            if(qModel) {
                                return InterpretationStatus.Quasi;
                            }
                            else {
                                return InterpretationStatus.Incompareable;
                            }
                        }
                        else {
                            return InterpretationStatus.Incompareable;
                        }
                    }
                    else {
                        boolean qModel = lhsMMP.mmpDomination(rhsMMP);
                        if(qModel) {
                            return InterpretationStatus.Quasi;
                        }
                        else{
                            return InterpretationStatus.Incompareable;
                        }
                    }
                }
            }
        }
    }


    private InterpretationStatus compareTwoMMPsModulo(
            MaxMinPolynomial lhsMMP, MaxMinPolynomial rhsMMP) {

        MMPolyMetaInf lhsMMpMetaInf;
        MMPolyMetaInf rhsMMpMetaInf;


        //Trivial, if both MMpolys are equal they have the same value.
       if(lhsMMP.equals(rhsMMP)) {
            return InterpretationStatus.Model;
        }
       else {
           //Transform both polynomials modulo the carriersetsize
           MaxMinPolynomial lhsMMpModulo = lhsMMP.transformModulo(this.cSS);
           MaxMinPolynomial rhsMMpModulo = rhsMMP.transformModulo(this.cSS);

           //Check if both MMpolys are equal after modulo transformation
           if(lhsMMpModulo.equals(rhsMMpModulo)) {
               return InterpretationStatus.Model;
           }
           else {
               lhsMMpMetaInf = lhsMMpModulo.getMetaInf();
               rhsMMpMetaInf = rhsMMpModulo.getMetaInf();
               if(lhsMMpMetaInf == rhsMMpMetaInf) {
                   if(lhsMMpMetaInf == MMPolyMetaInf.Constant) {
                       BigInteger lhsValue = lhsMMpModulo.getVarPolynomial().getConstantPart().getNumericalAddend();
                       BigInteger rhsValue = rhsMMpModulo.getVarPolynomial().getConstantPart().getNumericalAddend();
                       int compareResult = (lhsValue.subtract(rhsValue)).signum();
                       switch (compareResult) {
                       case 0 :
                           return InterpretationStatus.Model;
                       case 1 :
                           return InterpretationStatus.Quasi;
                       case -1 :
                           return InterpretationStatus.Incompareable;
                       default :
                           throw new RuntimeException("Comparison should not yield " + compareResult);
                       }
                   }
                   else {
                       return InterpretationStatus.Incompareable;
                   }
               }
               else {
                   if(lhsMMpMetaInf == MMPolyMetaInf.Constant) {
                       BigInteger lhsValue = lhsMMpModulo.getVarPolynomial().getConstantPart().getNumericalAddend();
                       if(lhsValue.equals(this.maxCarrierElement)) {
                           return InterpretationStatus.Quasi;
                       }
                       else {
                           return InterpretationStatus.Incompareable;
                       }
                   }
                   else {
                       if(rhsMMpMetaInf == MMPolyMetaInf.Constant) {
                           BigInteger rhsValue = rhsMMpModulo.getVarPolynomial().getConstantPart().getNumericalAddend();
                           if(rhsValue.signum() == 0 ) {
                               return InterpretationStatus.Quasi;
                           }
                           else {
                               return InterpretationStatus.Incompareable;
                           }
                       }
                       else {
                           return InterpretationStatus.Incompareable;
                       }
                   }
               }
           }
       }
    }

    //TODO Think of better name for this method!
    //Make use of transitivity property of maxmimum
     public static InterpretationStatus myCheck(
             ImmutableSet<? extends ImmutableSet<VarPolynomial>> lhsMinSets,
             ImmutableSet<? extends ImmutableSet<VarPolynomial>> rhsMinSets)
     {
         boolean allRhsMinSetsFoundEqualSet = true;
         Iterator<?extends ImmutableSet<VarPolynomial>> iterRhs = rhsMinSets.iterator();
         while(allRhsMinSetsFoundEqualSet && iterRhs.hasNext()) {
             LinkedHashSet<VarPolynomial> dummySetRhs = new LinkedHashSet<VarPolynomial>(iterRhs.next());
             ImmutableLinkedHashSet<VarPolynomial> rhsMinSet =
                 ImmutableCreator.create(dummySetRhs);
             Iterator<?extends ImmutableSet<VarPolynomial>> iterLhs = lhsMinSets.iterator();
             boolean equalMinSetFound = false;
             while((!equalMinSetFound) && iterLhs.hasNext()) {
                 LinkedHashSet<VarPolynomial> dummySet = new LinkedHashSet<VarPolynomial>(iterLhs.next());
                 ImmutableLinkedHashSet<VarPolynomial> lhsMinSet =
                     ImmutableCreator.create(dummySet);
                 equalMinSetFound = (lhsMinSet.equals(rhsMinSet));
             }
             allRhsMinSetsFoundEqualSet = equalMinSetFound;
         }
         if(allRhsMinSetsFoundEqualSet) {
             return InterpretationStatus.Quasi;
         }
         else {
             return InterpretationStatus.Incompareable;
         }
     }

     private LinkedList<MyModel> merge(List<MyModel> modelList, MyModel actualmodel) {
         LinkedList<MyModel> resultList = new LinkedList<MyModel>();
         for(MyModel mergeModel : modelList) {
             resultList.add(MyModel.mergeInterpretations(mergeModel, actualmodel));
         }
         return resultList;
     }

     private LinkedList<MyModel> completeAllModels(LinkedList<MyModel> models) {
         int length = models.size();
         Set<FunctionSymbol> fSyms;
         for(int i=0; i<length; i++) {
             LinkedHashSet<FunctionSymbol> signatureCopy =
                 new LinkedHashSet<FunctionSymbol>(this.signature);
             MyModel m = models.get(i);
             fSyms = this.isModelComplete(m, signatureCopy);
             if(fSyms != null) {
                 MyModel completeM = m.completeInterpretation(fSyms);
                 models.set(i, completeM);
             }
         }
         return models;
     }

     private Set<FunctionSymbol> isModelComplete(MyModel actModel, Set<FunctionSymbol> signat) {
         Set<FunctionSymbol> aux = actModel.getSignature();
         if(aux.size() != signat.size()) {
             signat.removeAll(aux);
             return signat;
         }
         return null;
     }

}
