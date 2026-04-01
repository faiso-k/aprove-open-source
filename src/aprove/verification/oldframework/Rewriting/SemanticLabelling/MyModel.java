package aprove.verification.oldframework.Rewriting.SemanticLabelling;


import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.MaxMinPolynomials.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * This class stores all relevant information of a (Quasi-) Model.
 * It permits labelling with MaxMinPolynomials over a finite ring
 * or the natural numbers.
 *
 * @author Patrick Wiehe
 * @version $Id$
 */
public class MyModel {

    private static Logger log = Logger.getLogger("aprove.verification.oldframework.Rewriting.SemanticLabelling.MyModel");

    private final ImmutableMap<FunctionSymbol, MaxMinPolynomial> interpretation;
    private final ImmutableSet<FunctionSymbol> signature;
    private final Map<TRSFunctionApplication, MaxMinPolynomial> labelMap;
    private InterpretationStatus status;
    private YNM weaklyMonotonic;
    private final int carrier;
    private final int hashcode;
    private static final String firstArg = "x_0";
    private static final String scndArg = "x_1";
    private static Set<String> allowedVariableNames = MyModel.mycreate();
    private static final MaxMinPolynomial dummyInterpretation = MaxMinPolynomial.ZERO;

    private static Set<String> mycreate() {
        Set<String> auxSet = new HashSet<String>(2);
        auxSet.add(MyModel.firstArg);
        auxSet.add(MyModel.scndArg);
        auxSet.add(null);
        return auxSet;
    }

    /**
     * Creator with default values. <br>They are:<br>
     *  interpretation = empty Map <br>
     *  status = InterpretationStatus.Try <br>
     *  weaklymonotonic = YNM.YES <br>
     *  carrier = -1 <br>
     * @author patwie
     *
     */
    public static MyModel create() {
        return new MyModel();
    }

    /**
     * Creator with some default values. <br>They are:<br>
     *  status = InterpretationStatus.Try <br>
     *  weaklymonotonic = YNM.YES <br>
     *  carrier = -1 <br>
     * @author patwie
     *
     */
    public static MyModel create(FunctionSymbol fSym, MaxMinPolynomial mmp) {
        Map<FunctionSymbol, MaxMinPolynomial> map = new HashMap<FunctionSymbol, MaxMinPolynomial>(1);
        map.put(fSym, mmp);
        return  new MyModel(map, InterpretationStatus.Try, -1, YNM.YES);
    }

    /**
     * Creator with some default values. <br>They are:<br>
     *  status = InterpretationStatus.Try <br>
     *  weaklymonotonic = YNM.MAYBE on finite carrier,  <br>
     *  weaklymonotonic = YNM.YES on infinite carrier <br>
     * @author patwie
     *
     */
    public static MyModel create(FunctionSymbol fSym, MaxMinPolynomial mmp, int carrier) {
        Map<FunctionSymbol, MaxMinPolynomial> map = new HashMap<FunctionSymbol, MaxMinPolynomial>(1);
        map.put(fSym, mmp);
        return  new MyModel(map, InterpretationStatus.Try, carrier, YNM.MAYBE);
    }


    public static MyModel create(Map<FunctionSymbol, MaxMinPolynomial> interpretationMap, InterpretationStatus status, int cSS, YNM weaklyMonotonic) {
         return new MyModel(interpretationMap, status, cSS, weaklyMonotonic);
    }


    public static MyModel create(Map<FunctionSymbol, MaxMinPolynomial> interpretationMap, InterpretationStatus status, int cSS) {
        return new MyModel(interpretationMap, status, cSS);
    }



    private MyModel() {
        this.interpretation = ImmutableCreator.create(new HashMap<FunctionSymbol, MaxMinPolynomial>());
        this.signature = ImmutableCreator.create(new HashSet<FunctionSymbol>());
        this.labelMap = new HashMap<TRSFunctionApplication, MaxMinPolynomial>();
        this.status = InterpretationStatus.Try;
        this.weaklyMonotonic = YNM.YES;
        this.carrier = -1;
        this.hashcode = this.calcHashCode();
    }

    private MyModel(Map<FunctionSymbol,MaxMinPolynomial> interpret, InterpretationStatus stat, int cSS, YNM weakly) {
        if(Globals.useAssertions) {
            LinkedHashSet<MaxMinPolynomial> mmps = new LinkedHashSet<MaxMinPolynomial>(interpret.values());
            for(MaxMinPolynomial mmp : mmps){
                assert(mmp.containsMaximalSetOfVariables(MyModel.allowedVariableNames));
            }
        }
        this.signature = ImmutableCreator.create(interpret.keySet());
        this.labelMap = new HashMap<TRSFunctionApplication, MaxMinPolynomial>();
        if(cSS == -1) {
            this.interpretation = ImmutableCreator.create(interpret);
            this.status = stat;
            this.carrier = cSS;
            this.weaklyMonotonic = YNM.YES;
            this.hashcode = this.calcHashCode();
        }
        else {
            if(Globals.useAssertions) {
                if((weakly.isBool()) && (weakly.toBool()==true)) {
                    assert(MyModel.weaklyCheck(interpret));
                }
            }
            this.interpretation = ImmutableCreator.create(interpret);
            this.status = stat;
            this.carrier = cSS;
            this.weaklyMonotonic = weakly;
            this.hashcode = this.calcHashCode();
        }
    }


    private MyModel(Map<FunctionSymbol,MaxMinPolynomial> interpret, InterpretationStatus stat, int cSS) {
        if(Globals.useAssertions) {
            LinkedHashSet<MaxMinPolynomial> mmps = new LinkedHashSet<MaxMinPolynomial>(interpret.values());
            for(MaxMinPolynomial mmp : mmps){
                assert(mmp.containsMaximalSetOfVariables(MyModel.allowedVariableNames));
            }
        }
        this.signature = ImmutableCreator.create(interpret.keySet());
        this.labelMap = new HashMap<TRSFunctionApplication, MaxMinPolynomial>();
        if(cSS == -1) {
            this.interpretation = ImmutableCreator.create(interpret);
            this.status = stat;
            this.carrier = cSS;
            this.weaklyMonotonic = YNM.YES;
            this.hashcode = this.calcHashCode();
        }
        else {
            this.interpretation = ImmutableCreator.create(interpret);
            this.status = stat;
            this.carrier = cSS;
            this.weaklyMonotonic = YNM.MAYBE;
            this.hashcode = this.calcHashCode();
        }
    }

    //DeepCopy version to change InterpretationStatus of a model
    //Should not be called elswhere, since it is not checked if
    //the interpretation change is legal,
    //e.g. a change from QuasiModel to Model is never legal!
    private MyModel(
            ImmutableMap<FunctionSymbol, MaxMinPolynomial> interpretation,
            ImmutableSet<FunctionSymbol> signature,
            Map<TRSFunctionApplication, MaxMinPolynomial> labelMap,
            InterpretationStatus status,
            YNM weaklyMonotonic,
            int carrier) {
        this.interpretation = interpretation;
        this.signature = signature;
        this.labelMap = labelMap;
        this.status = status;
        this.weaklyMonotonic = weaklyMonotonic;
        this.carrier = carrier;
        this.hashcode = this.calcHashCode();
    }

    public int getCarrierSize() {
        return this.carrier;
    }

    public ImmutableMap<FunctionSymbol, MaxMinPolynomial> getInterpretation() {
        return this.interpretation;
    }

    public InterpretationStatus getStatus() {
        return this.status;
    }

    public ImmutableSet<FunctionSymbol> getSignature() {
        return this.signature;
    }

    public MyModel changeInterpretationStatus(InterpretationStatus status) {
        if(Globals.useAssertions) {
            if((this.status == InterpretationStatus.Quasi) && (status == InterpretationStatus.Model)) {
                throw new RuntimeException("Illegal modification! Can not convert a QuasiModel into a Model!");
            }
            if((this.status == InterpretationStatus.QuasiTry) && (status == InterpretationStatus.Model)) {
                throw new RuntimeException("Illegal modification! Can not convert a QuasiModel into a Model!");
            }
            if((this.status == InterpretationStatus.QuasiTry) && (status == InterpretationStatus.Try)) {
                throw new RuntimeException("Illegal modification! Can not convert a QuasiModel into a Model candidat!");
            }
        }
        return new MyModel(this.interpretation, this.signature, this.labelMap, status, this.weaklyMonotonic, this.carrier);
    }


    /**
     * Extends the interpretation of this by the possible interpretations
     * of funcsym
     * @param funcsym, the parameter whose possible interpretations are added
     * to this interpetation
     * @return a list of models with the extended interpretation
     */
    /*
    public List<MyModel> extendInterpretation(FunctionSymbol funcSym) {
        List<MyModel> result = new LinkedList<MyModel>();
        Set<MaxMinPolynomial> extensions = InterpretationPoolCreator.createIntSet(this.carrier, funcSym.getArity());
        Iterator<MaxMinPolynomial> iter = extensions.iterator();
        while(iter.hasNext()) {
            Map<FunctionSymbol, MaxMinPolynomial> deepCopy = new HashMap<FunctionSymbol, MaxMinPolynomial>(this.interpretation);
            deepCopy.put(funcSym, iter.next());
            if(this.status == InterpretationStatus.Quasi) {
                result.add(new MyModel(deepCopy, InterpretationStatus.QuasiTry, this.carrier));
            }
            else {
                result.add(new MyModel(deepCopy, InterpretationStatus.Try, this.carrier));
            }
        }
        return result;
    }
    */


    /**
     * Extends the interpretation of this by the possible interpretations
     * of funcsym, but only keeps the function symbols of the intersection of
     * the rule and the interpretation of this
     * @param funcsym, the parameter whose possible interpretations are added
     * to this interpetation
     * @param rule, the rule which could not be labelled with the actual
     * interpretation of this
     * @param fullInterpretation all possible interpretations or just a subset
     * @return a list of models with the extended interpretation
     */
    public LinkedList<MyModel> extendInterpretation(FunctionSymbol funcSym, Rule rule, boolean fullInterpretation) {
        Set<FunctionSymbol> ruleSignature = new HashSet<FunctionSymbol>();
        TRSTerm dummy = rule.getLeft();
        ruleSignature.addAll(dummy.getFunctionSymbols());
        dummy = rule.getRight();
        ruleSignature.addAll(dummy.getFunctionSymbols());
        ruleSignature.retainAll(this.interpretation.keySet());
        Set<FunctionSymbol> intersectionSignature = ruleSignature;
        Map<FunctionSymbol, MaxMinPolynomial> deepCopy = new HashMap<FunctionSymbol, MaxMinPolynomial>();
        //fill deeepCopy with relevant Function Symbols
        for(FunctionSymbol fSym : intersectionSignature) {
            deepCopy.put(fSym, this.interpretation.get(fSym));
        }
        LinkedList<MyModel> result = new LinkedList<MyModel>();
        Set<MaxMinPolynomial> extensions = InterpretationPoolCreator.createIntSet(this.carrier, funcSym.getArity());
        Iterator<MaxMinPolynomial> iter = extensions.iterator();
        while(iter.hasNext()) {
            Map<FunctionSymbol, MaxMinPolynomial> actualCopy = new HashMap<FunctionSymbol, MaxMinPolynomial>(deepCopy);
            actualCopy.put(funcSym, iter.next());
            if(this.status == InterpretationStatus.Quasi) {
                result.add(new MyModel(actualCopy, InterpretationStatus.QuasiTry, this.carrier));
            }
            else {
                result.add(new MyModel(actualCopy, InterpretationStatus.Try, this.carrier));
            }
        }
        return result;
    }


    /**
     * Extends the interpretation of this by the possible interpretations
     * of funcsym, but only keeps the function symbols of the intersection of
     * the rule and the interpretation of this
     * @param funcsym, the parameter whose possible interpretations are added
     * to this interpetation
     * @param rule, the rule which could not be labelled with the actual
     * interpretation of this
     * @return a list of models with the extended interpretation
     */

    /*
    public LinkedList<MyModel> extendInterpretation(FunctionSymbol funcSym, Rule rule) {
        Set<FunctionSymbol> ruleSignature = new HashSet<FunctionSymbol>();
        Term dummy = rule.getLeft();
        ruleSignature.addAll(dummy.getFunctionSymbols());
        dummy = rule.getRight();
        ruleSignature.addAll(dummy.getFunctionSymbols());
        ruleSignature.retainAll(this.interpretation.keySet());
        Set<FunctionSymbol> intersectionSignature = ruleSignature;
        Map<FunctionSymbol, MaxMinPolynomial> deepCopy = new HashMap<FunctionSymbol, MaxMinPolynomial>();
        //fill deeepCopy with relevant Function Symbols
        for(FunctionSymbol fSym : intersectionSignature) {
            deepCopy.put(fSym, this.interpretation.get(fSym));
        }
        LinkedList<MyModel> result = new LinkedList<MyModel>();
        Set<MaxMinPolynomial> extensions = InterpretationPoolCreator.createIntSet(this.carrier, funcSym.getArity());
        Iterator<MaxMinPolynomial> iter = extensions.iterator();
        while(iter.hasNext()) {
            Map<FunctionSymbol, MaxMinPolynomial> actualCopy = new HashMap<FunctionSymbol, MaxMinPolynomial>(deepCopy);
            actualCopy.put(funcSym, iter.next());
            if(this.status == InterpretationStatus.Quasi) {
                result.add(new MyModel(actualCopy, InterpretationStatus.QuasiTry, this.carrier));
            }
            else {
                result.add(new MyModel(actualCopy, InterpretationStatus.Try, this.carrier));
            }
        }
        return result;
    }
    */
    public static MyModel mergeInterpretations(MyModel model1, MyModel model2) {
        Map<FunctionSymbol, MaxMinPolynomial> actualCopy = new HashMap<FunctionSymbol, MaxMinPolynomial>(model2.interpretation);
        actualCopy.putAll(model1.interpretation);
        if(model1.status == InterpretationStatus.Quasi || model2.status == InterpretationStatus.Quasi ) {
            return (new MyModel(actualCopy, InterpretationStatus.Quasi, model1.carrier));
        }
        else {
            if(Globals.useAssertions) {
                assert(model1.status == InterpretationStatus.Model) ;
            }
            return (new MyModel(actualCopy, InterpretationStatus.Model, model1.carrier));
        }
    }

    /**
     * extends the interpretation of this
     * @param funcsym, the funcsym by which the interpretation is extended
     * @param extensions, the allowed interpretations for param funcsym
     * @return a model with the extended interpretation
     */
    public List<MyModel> extendInterpretation(FunctionSymbol funcsym, Collection<MaxMinPolynomial> extensions) {
        List<MyModel> result = new LinkedList<MyModel>();
        Iterator<MaxMinPolynomial> iter = extensions.iterator();
        if(Globals.useAssertions) {
            while(iter.hasNext()) {
                MaxMinPolynomial extensionCandidat = iter.next();
                assert(extensionCandidat.getAllVariableNames().size() <= funcsym.getArity());
                Map<FunctionSymbol, MaxMinPolynomial> deepCopy = new HashMap<FunctionSymbol, MaxMinPolynomial>(this.interpretation);
                deepCopy.put(funcsym, extensionCandidat);
                if(this.status == InterpretationStatus.Quasi) {
                    result.add(new MyModel(deepCopy, InterpretationStatus.QuasiTry, this.carrier));
                }
                else {
                    result.add(new MyModel(deepCopy, InterpretationStatus.Try, this.carrier));
                }
            }
        }
        else {
            while(iter.hasNext()) {
                Map<FunctionSymbol, MaxMinPolynomial> deepCopy = new HashMap<FunctionSymbol, MaxMinPolynomial>(this.interpretation);
                deepCopy.put(funcsym, iter.next());
                if(this.status == InterpretationStatus.Quasi) {
                    result.add(new MyModel(deepCopy, InterpretationStatus.QuasiTry, this.carrier));
                }
                else {
                    result.add(new MyModel(deepCopy, InterpretationStatus.Try, this.carrier));
                }
            }
        }
        return result;
    }

    /**
     * a method to "complete" a model <br>
     * <b>NOTE: </b> So far each function symbol is given the dummy interpretation 0!<br>
     * if a model still has some function symbols which have
     * no value assigned so far, it gets an assignement here.
     * @param fSyms the set of function symbols which need to get an interpretation assigned
     * @return a model where at least the function symbols of the set fSyms
     * have an interpretation assigned.
     */
    public MyModel completeInterpretation(Set<FunctionSymbol> fSyms) {
        Map<FunctionSymbol, MaxMinPolynomial> interpretMap =
            new LinkedHashMap<FunctionSymbol, MaxMinPolynomial>(this.interpretation);
        Set<FunctionSymbol> signat = new LinkedHashSet<FunctionSymbol>(this.signature);
        for(FunctionSymbol f : fSyms) {
            if(Globals.useAssertions) {
                if(interpretMap.containsKey(f)) {
                    throw new RuntimeException("Illegal modification! It is not allowed to overwite an interpretation assignement!");
                }
                //assert(! interpretMap.containsKey(f));
            }
            interpretMap.put(f, MyModel.dummyInterpretation);
            signat.add(f);
        }
        MyModel result =
        new MyModel(
                ImmutableCreator.create(interpretMap),
                ImmutableCreator.create(signat),
                this.labelMap,
                this.status,
                this.weaklyMonotonic,
                this.carrier);
        return result;
    }

    /**
     * This method returns exactly those function symbols which
     * have a different interpretation in other compared to the
     * interpretation in this.
     * @param other
     * @return the set of function symbols with different interpretations
     */
    public Set<FunctionSymbol> interpretationDifference(MyModel other) {
        Set<FunctionSymbol> differences = new LinkedHashSet<FunctionSymbol>();
        if(Globals.useAssertions) {
            assert(this.signature.equals(other.signature));
        }
        for(FunctionSymbol fSym : this.signature) {
            if(! this.interpretation.get(fSym).equals(other.interpretation.get(fSym))) {
                differences.add(fSym);
            }
        }
        return differences;
    }


    public boolean onlyWeaklyMonotonicFunctionsUsed() {
        if(this.weaklyMonotonic == YNM.MAYBE) {
            return MyModel.weaklyCheck(this.interpretation);
        }
        else {
            return this.weaklyMonotonic.toBool();
        }
    }

    public static boolean weaklyCheck (Map<FunctionSymbol, MaxMinPolynomial> interpretationMap) {
        Set<MaxMinPolynomial> mmps = new LinkedHashSet<MaxMinPolynomial>(interpretationMap.values());
        boolean returnValue = true;
        for(MaxMinPolynomial mmp : mmps) {
            if(returnValue) {
                if(mmp.getMetaInf() == MMPolyMetaInf.VarPoly) {
                    VarPolynomial vp = mmp.getVarPolynomial();
                    if(vp.getVariables().size()>1) {
                        returnValue = false;
                    }
                    else {
                        if(!vp.isVariable()) {
                            returnValue = false;
                        }
                    }
                }
            }
        }
        return returnValue;
    }


    public MaxMinPolynomial calculateMMpolyOfTermWithVarRenaming(TRSTerm t, Map<String, VarPolynomial> variableRenaming) {
        HashMap <String, MaxMinPolynomial> substMap = new HashMap<String, MaxMinPolynomial>(2);

        if(t.isVariable()) {
            TRSVariable v = (TRSVariable) t;
            VarPolynomial vp = variableRenaming.get(v.getName());
            if(Globals.useAssertions){
                assert(vp!=null) : "MyModel: variableRenaming was not complete!";
                assert(vp.isVariable()) : "MyModel : variableRenaming mapping is incorrect, only VarPolynomials which are encapsulated variables are allowed!";
            }
            return MaxMinPolynomial.create(vp);
        }
        else {
            TRSFunctionApplication fApp = (TRSFunctionApplication) t;
            FunctionSymbol fSym = fApp.getRootSymbol();
            MaxMinPolynomial actInterpr = this.interpretation.get(fSym);
            if(Globals.useAssertions){
                assert(actInterpr!=null) : "MyModel: interpretation was not complete!";
            }
            MMPolyMetaInf actMetaInf = actInterpr.getMetaInf();
            if(actMetaInf == MMPolyMetaInf.Constant) {
                return actInterpr;
            }
            else {
                MaxMinPolynomial mmp;
                // first check the number of Variables in the actInterpr,
                // to decide which arguments are relevant
                LinkedHashSet<String> actInterprVars = actInterpr.getAllVariableNames();
                int actInterprVarsSize = actInterprVars.size();

                if(actInterprVarsSize ==1) {
                    if(actInterprVars.contains(MyModel.firstArg)) {
                        MaxMinPolynomial firstArg = this.calculateMMpolyOfTermWithVarRenaming(fApp.getArgument(0), variableRenaming);
                        // check if the MaxMinPoly of the firstArg is just an encapsulated VarPolynomial
                        // Then we can use the substitution of the VarPolys.
                        MMPolyMetaInf firstArgMetaInf =  firstArg.getMetaInf();
                        if(firstArgMetaInf == MMPolyMetaInf.Constant || firstArgMetaInf == MMPolyMetaInf.VarPoly) {
                            VarPolynomial childX = firstArg.getVarPolynomial();
                            // The actual Interpretation needs to be just an encapsulated VarPoly as well,
                            // if we want to use the substitution of the VarPolys.
                            if(actMetaInf == MMPolyMetaInf.VarPoly) {
                                VarPolynomial vpParent = actInterpr.getVarPolynomial();
                                Map<String, VarPolynomial> auxMap = new LinkedHashMap<String, VarPolynomial>(1);
                                auxMap.put(MyModel.firstArg, childX);
                                if(Globals.DEBUG_PATWIE && MyModel.log.isLoggable(Level.FINEST)) {
                                    long l1 = System.nanoTime();
                                    VarPolynomial vp = vpParent.substituteVariables(auxMap);
                                    long l2 = System.nanoTime();
                                    mmp = MaxMinPolynomial.create(vp);
                                    long l3 = System.nanoTime();
                                    MyModel.log.log(Level.FINEST, "Time for substitution on VPs : " +(l2-l1));
                                    MyModel.log.log(Level.FINEST, "Time for substituition plus building the new MMP : " + (l3-l1));
                                }
                                else {
                                    VarPolynomial vp = vpParent.substituteVariables(auxMap);
                                    mmp = MaxMinPolynomial.create(vp);
                                }
                                this.labelMap.put(fApp, mmp);
                                return mmp;
                            }
                            else {
                                // fill substitutionMap
                                substMap.put(MyModel.firstArg, firstArg);
                                if(Globals.DEBUG_PATWIE && MyModel.log.isLoggable(Level.FINEST)) {
                                    long l1 = System.nanoTime();
                                    mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                    long l2 = System.nanoTime();
                                    MyModel.log.log(Level.FINEST, "Time for substitution on MMPs : " +(l2-l1));
                                }
                                else {
                                    mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                }
                                this.labelMap.put(fApp, mmp);
                                return mmp;
                            }
                        }
                        else {
                            //fill substitutionMap
                            substMap.put(MyModel.firstArg, firstArg);
                            if(Globals.DEBUG_PATWIE && MyModel.log.isLoggable(Level.FINEST)) {
                                long l1 = System.nanoTime();
                                mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                long l2 = System.nanoTime();
                                MyModel.log.log(Level.FINEST, "Time for substitution on MMPs : " +(l2-l1));
                            }
                            else {
                                mmp = actInterpr.substituteVariables(substMap, this.carrier);
                            }
                            this.labelMap.put(fApp, mmp);
                            return mmp;
                        }
                    }

                    else {// actInterpVars consists only of scndArg
                        MaxMinPolynomial scndArg = this.calculateMMpolyOfTermWithVarRenaming(fApp.getArgument(1), variableRenaming);
                        // check if the MaxMinPoly of the scndArg is just an encapsulated VarPolynomial
                        // Then we can use the substitution of the VarPolys.
                        MMPolyMetaInf scndArgMetaInf =  scndArg.getMetaInf();
                        if(scndArgMetaInf == MMPolyMetaInf.Constant || scndArgMetaInf == MMPolyMetaInf.VarPoly) {
                            VarPolynomial childY = scndArg.getVarPolynomial();
                            // The actual Interpretation needs to be just an encapsulated VarPoly as well,
                            // if we want to use the substitution of the VarPolys.
                            if(actMetaInf == MMPolyMetaInf.VarPoly) {
                                VarPolynomial vpParent = actInterpr.getVarPolynomial();
                                Map<String, VarPolynomial> auxMap = new LinkedHashMap<String, VarPolynomial>(1);
                                auxMap.put(MyModel.scndArg, childY);
                                if(Globals.DEBUG_PATWIE && MyModel.log.isLoggable(Level.FINEST)) {
                                    long l1 = System.nanoTime();
                                    VarPolynomial vp = vpParent.substituteVariables(auxMap);
                                    long l2 = System.nanoTime();
                                    mmp = MaxMinPolynomial.create(vp);
                                    long l3 = System.nanoTime();
                                    MyModel.log.log(Level.FINEST, "Time for substitution on VPs : " +(l2-l1));
                                    MyModel.log.log(Level.FINEST, "Time for substituition plus building the new MMP : " + (l3-l1));
                                }
                                else {
                                    VarPolynomial vp = vpParent.substituteVariables(auxMap);
                                    mmp = MaxMinPolynomial.create(vp);
                                }
                                this.labelMap.put(fApp, mmp);
                                return mmp;
                            }
                            else {
                                // fill substitutionMap
                                substMap.put(MyModel.scndArg, scndArg);
                                if(Globals.DEBUG_PATWIE && MyModel.log.isLoggable(Level.FINEST)) {
                                    long l1 = System.nanoTime();
                                    mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                    long l2 = System.nanoTime();
                                    MyModel.log.log(Level.FINEST, "Time for substitution on MMPs : " +(l2-l1));
                                }
                                else {
                                    mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                }
                                this.labelMap.put(fApp, mmp);
                                return mmp;
                            }
                        }
                        else {
                            // fill substitutionMap
                            substMap.put(MyModel.scndArg, scndArg);
                            if(Globals.DEBUG_PATWIE && MyModel.log.isLoggable(Level.FINEST)) {
                                long l1 = System.nanoTime();
                                mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                long l2 = System.nanoTime();
                                MyModel.log.log(Level.FINEST, "Time for substitution on MMPs : " +(l2-l1));
                            }
                            else {
                                mmp = actInterpr.substituteVariables(substMap, this.carrier);
                            }
                            this.labelMap.put(fApp, mmp);
                            return mmp;
                        }
                    }
                }

                else { // actInterpVars has size 2, consists of firstArg and scndArg, so both children are relevant!
                    MaxMinPolynomial firstArg = this.calculateMMpolyOfTermWithVarRenaming(fApp.getArgument(0), variableRenaming);
                    MaxMinPolynomial scndArg = this.calculateMMpolyOfTermWithVarRenaming(fApp.getArgument(1), variableRenaming);
                    // The actual Interpretation and both children need to be just encapsulated VarPolys,
                    // if we want to use the substitution of the VarPolys.
                    if (actMetaInf == MMPolyMetaInf.VarPoly) {
                        MMPolyMetaInf firstArgMetaInf =  firstArg.getMetaInf();
                        MMPolyMetaInf scndArgMetaInf  =  scndArg.getMetaInf();
                        if(((firstArgMetaInf == MMPolyMetaInf.Constant || firstArgMetaInf == MMPolyMetaInf.VarPoly)) &&
                            (scndArgMetaInf == MMPolyMetaInf.Constant || scndArgMetaInf == MMPolyMetaInf.VarPoly)) {

                            VarPolynomial childX = firstArg.getVarPolynomial();
                            VarPolynomial childY = scndArg.getVarPolynomial();
                            VarPolynomial parent = actInterpr.getVarPolynomial();

                            Map<String, VarPolynomial> auxMap = new LinkedHashMap<String, VarPolynomial>(2);
                            auxMap.put(MyModel.firstArg, childX);
                            auxMap.put(MyModel.scndArg, childY);

                            if(Globals.DEBUG_PATWIE && MyModel.log.isLoggable(Level.FINEST)) {
                                long l1 = System.nanoTime();
                                VarPolynomial vp = parent.substituteVariables(auxMap);
                                long l2 = System.nanoTime();
                                mmp = MaxMinPolynomial.create(vp);
                                long l3 = System.nanoTime();
                                MyModel.log.log(Level.FINEST, "Time for substitution on VPs : " +(l2-l1));
                                MyModel.log.log(Level.FINEST, "Time for substituition plus building the new MMP : " + (l3-l1));
                            }
                            else {
                                VarPolynomial vp = parent.substituteVariables(auxMap);
                                mmp = MaxMinPolynomial.create(vp);
                            }
                            this.labelMap.put(fApp, mmp);
                            return mmp;
                        }
                        else {
                            // fill substitutionMap
                            substMap.put(MyModel.firstArg, firstArg);
                            substMap.put(MyModel.scndArg, scndArg);
                            if(Globals.DEBUG_PATWIE && MyModel.log.isLoggable(Level.FINEST)) {
                                long l1 = System.nanoTime();
                                mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                long l2 = System.nanoTime();
                                MyModel.log.log(Level.FINEST, "Time for substitution on MMPs : " +(l2-l1));
                            }
                            else {
                                mmp = actInterpr.substituteVariables(substMap, this.carrier);
                            }
                            this.labelMap.put(fApp, mmp);
                            return mmp;
                        }
                    }
                    else {
                        // fill substitutionMap
                        substMap.put(MyModel.firstArg, firstArg);
                        substMap.put(MyModel.scndArg, scndArg);
                        if(Globals.DEBUG_PATWIE && MyModel.log.isLoggable(Level.FINEST)) {
                            long l1 = System.nanoTime();
                            mmp = actInterpr.substituteVariables(substMap, this.carrier);
                            long l2 = System.nanoTime();
                            MyModel.log.log(Level.FINEST, "Time for substitution on MMPs : " +(l2-l1));
                        }
                        else {
                            mmp = actInterpr.substituteVariables(substMap, this.carrier);
                        }
                        this.labelMap.put(fApp, mmp);
                        return mmp;
                    }

                }
            }
        }
    }

    /**
     *
     * @param term, the term which should be labelled with <b>this</b>
     * @return a MaxMinPolynomial iff <b>this</b> had all information which are necessary <br>
     * a function symbol iff the calculation depends on this function symbol
     * and it has not assigned an interpretation so far.
     */
    public Pair<MaxMinPolynomial, FunctionSymbol> calculateMMpolyOfTerm (TRSTerm term) {
        Pair<MaxMinPolynomial, FunctionSymbol> resultPair = new Pair<MaxMinPolynomial, FunctionSymbol>(null, null);
        HashMap <String, MaxMinPolynomial> substMap = new HashMap<String, MaxMinPolynomial>(2);
        MaxMinPolynomial labelOfActualTerm = this.labelMap.get(term);
        if(labelOfActualTerm != null){
            resultPair.setKey(labelOfActualTerm);
            return resultPair;
        }
        else{
            if(term.isVariable()) {
                TRSVariable v = (TRSVariable) term;
                resultPair.setKey(MaxMinPolynomial.create(VarPolynomial.createVariable(v.getName())));
            }
            else{
                TRSFunctionApplication fApp = (TRSFunctionApplication) term;
                FunctionSymbol fSym = fApp.getRootSymbol();
                MaxMinPolynomial actInterpr = this.interpretation.get(fSym);
                if(actInterpr == null) {
                    resultPair.setValue(fSym);
                }
                else {
                    MMPolyMetaInf actMetaInf = actInterpr.getMetaInf();
                    if(actMetaInf == MMPolyMetaInf.Constant) {
                        resultPair.setKey(actInterpr);
                        this.labelMap.put(fApp, actInterpr);
                    }
                    else {
                        MaxMinPolynomial mmp;
                        // first check the number of Variables in the actInterpr,
                        // to decide which arguments are relevant
                        LinkedHashSet<String> actInterprVars = actInterpr.getAllVariableNames();
                        int actInterprVarsSize = actInterprVars.size();

                        if(actInterprVarsSize ==1) {
                            if(actInterprVars.contains(MyModel.firstArg)) {
                                Pair<MaxMinPolynomial, FunctionSymbol> auxPairFirstArg =
                                    this.calculateMMpolyOfTerm(fApp.getArgument(0));
                                // Check if the intMap had all the information to label childX
                                if(auxPairFirstArg.x == null) {
                                    resultPair = auxPairFirstArg;
                                }
                                else {
                                    // check if the MaxMinPoly of the firstArg is just an encapsulated VarPolynomial
                                    // Then we can use the substitution of the VarPolys.
                                    MMPolyMetaInf firstArgMetaInf =  auxPairFirstArg.x.getMetaInf();
                                    if(firstArgMetaInf == MMPolyMetaInf.Constant || firstArgMetaInf == MMPolyMetaInf.VarPoly) {
                                        VarPolynomial childX = auxPairFirstArg.x.getVarPolynomial();
                                        // The actual Interpretation needs to be just an encapsulated VarPoly as well,
                                        // if we want to use the substitution of the VarPolys.
                                        if(actMetaInf == MMPolyMetaInf.VarPoly) {
                                            VarPolynomial vpParent = actInterpr.getVarPolynomial();
                                            Map<String, VarPolynomial> auxMap = new LinkedHashMap<String, VarPolynomial>(1);
                                            auxMap.put(MyModel.firstArg, childX);
                                            if(Globals.DEBUG_PATWIE && MyModel.log.isLoggable(Level.FINEST)) {
                                                long l1 = System.nanoTime();
                                                VarPolynomial vp = vpParent.substituteVariables(auxMap);
                                                long l2 = System.nanoTime();
                                                mmp = MaxMinPolynomial.create(vp);
                                                long l3 = System.nanoTime();
                                                MyModel.log.log(Level.FINEST, "Time for substitution on VPs : " +(l2-l1));
                                                MyModel.log.log(Level.FINEST, "Time for substituition plus building the new MMP : " + (l3-l1));
                                            }
                                            else {
                                                VarPolynomial vp = vpParent.substituteVariables(auxMap);
                                                mmp = MaxMinPolynomial.create(vp);
                                            }
                                            resultPair.setKey(mmp);
                                            this.labelMap.put(fApp, mmp);
                                        }
                                        else {
                                            // fill substitutionMap
                                            substMap.put(MyModel.firstArg, auxPairFirstArg.x);
                                            if(Globals.DEBUG_PATWIE && MyModel.log.isLoggable(Level.FINEST)) {
                                                long l1 = System.nanoTime();
                                                mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                                long l2 = System.nanoTime();
                                                MyModel.log.log(Level.FINEST, "Time for substitution on MMPs : " +(l2-l1));
                                            }
                                            else {
                                                mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                            }
                                            resultPair.setKey(mmp);
                                            this.labelMap.put(fApp, mmp);
                                        }
                                    }
                                    else {
                                        //fill substitutionMap
                                        substMap.put(MyModel.firstArg, auxPairFirstArg.x);
                                        if(Globals.DEBUG_PATWIE && MyModel.log.isLoggable(Level.FINEST)) {
                                            long l1 = System.nanoTime();
                                            mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                            long l2 = System.nanoTime();
                                            MyModel.log.log(Level.FINEST, "Time for substitution on MMPs : " +(l2-l1));
                                        }
                                        else {
                                            mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                            if(actMetaInf == MMPolyMetaInf.VarPoly) {
                                                VarPolynomial vpParent = actInterpr.getVarPolynomial();
                                                int consAddend = vpParent.getConstantPart().getNumericalAddend().intValue();
                                                if (consAddend != 0) {
                                                    mmp = mmp.plus(MaxMinPolynomial.create(VarPolynomial.create(consAddend)));
                                                }
                                            }
                                        }
                                        resultPair.setKey(mmp);
                                        this.labelMap.put(fApp, mmp);
                                    }
                                }
                            }
                            else {// actInterpVars consists only of scndArg
                                Pair<MaxMinPolynomial, FunctionSymbol> auxPairScndArg =
                                    this.calculateMMpolyOfTerm(fApp.getArgument(1));

                                // Check if the intMap had all the information to label childY
                                if(auxPairScndArg.x == null) {
                                    resultPair = auxPairScndArg;
                                }
                                else {
                                    // check if the MaxMinPoly of the scndArg is just an encapsulated VarPolynomial
                                    // Then we can use the substitution of the VarPolys.
                                    MMPolyMetaInf scndArgMetaInf =  auxPairScndArg.x.getMetaInf();
                                    if(scndArgMetaInf == MMPolyMetaInf.Constant || scndArgMetaInf == MMPolyMetaInf.VarPoly) {
                                        VarPolynomial childY = auxPairScndArg.x.getVarPolynomial();
                                        // The actual Interpretation needs to be just an encapsulated VarPoly as well,
                                        // if we want to use the substitution of the VarPolys.
                                        if(actMetaInf == MMPolyMetaInf.VarPoly) {
                                            VarPolynomial vpParent = actInterpr.getVarPolynomial();
                                            Map<String, VarPolynomial> auxMap = new LinkedHashMap<String, VarPolynomial>(1);
                                            auxMap.put(MyModel.scndArg, childY);
                                            if(Globals.DEBUG_PATWIE && MyModel.log.isLoggable(Level.FINEST)) {
                                                long l1 = System.nanoTime();
                                                VarPolynomial vp = vpParent.substituteVariables(auxMap);
                                                long l2 = System.nanoTime();
                                                mmp = MaxMinPolynomial.create(vp);
                                                long l3 = System.nanoTime();
                                                MyModel.log.log(Level.FINEST, "Time for substitution on VPs : " +(l2-l1));
                                                MyModel.log.log(Level.FINEST, "Time for substituition plus building the new MMP : " + (l3-l1));
                                            }
                                            else {
                                                VarPolynomial vp = vpParent.substituteVariables(auxMap);
                                                mmp = MaxMinPolynomial.create(vp);
                                            }
                                            resultPair.setKey(mmp);
                                            this.labelMap.put(fApp, mmp);
                                        }
                                        else {
                                            // fill substitutionMap
                                            substMap.put(MyModel.scndArg, auxPairScndArg.x);
                                            if(Globals.DEBUG_PATWIE && MyModel.log.isLoggable(Level.FINEST)) {
                                                long l1 = System.nanoTime();
                                                mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                                long l2 = System.nanoTime();
                                                MyModel.log.log(Level.FINEST, "Time for substitution on MMPs : " +(l2-l1));
                                            }
                                            else {
                                                mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                            }
                                            resultPair.setKey(mmp);
                                            this.labelMap.put(fApp, mmp);
                                        }
                                    }
                                    else {
                                        // fill substitutionMap
                                        substMap.put(MyModel.scndArg, auxPairScndArg.x);
                                        if(Globals.DEBUG_PATWIE && MyModel.log.isLoggable(Level.FINEST)) {
                                            long l1 = System.nanoTime();
                                            mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                            long l2 = System.nanoTime();
                                            MyModel.log.log(Level.FINEST, "Time for substitution on MMPs : " +(l2-l1));
                                        }
                                        else {
                                            mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                            if(actMetaInf == MMPolyMetaInf.VarPoly) {
                                                VarPolynomial vpParent = actInterpr.getVarPolynomial();
                                                int consAddend = vpParent.getConstantPart().getNumericalAddend().intValue();
                                                if (consAddend != 0) {
                                                    mmp = mmp.plus(MaxMinPolynomial.create(VarPolynomial.create(consAddend)));
                                                }
                                            }
                                        }
                                        resultPair.setKey(mmp);
                                        this.labelMap.put(fApp, mmp);
                                    }
                                }
                            }
                        }
                        else { // actInterpVars has size 2, consists of firstArg and scndArg, so both children are relevant!
                            Pair<MaxMinPolynomial, FunctionSymbol> auxPairFirstArg =
                                this.calculateMMpolyOfTerm(fApp.getArgument(0));
                            if(auxPairFirstArg.x == null) {
                                resultPair = auxPairFirstArg;
                            }
                            else {
                                Pair<MaxMinPolynomial, FunctionSymbol> auxPairScndArg =
                                    this.calculateMMpolyOfTerm(fApp.getArgument(1));
                                if(auxPairScndArg.x == null) {
                                    resultPair = auxPairScndArg;
                                }
                                else {
                                    // The actual Interpretation and both children need to be just encapsulated VarPolys,
                                    // if we want to use the substitution of the VarPolys.
                                    if (actMetaInf == MMPolyMetaInf.VarPoly) {
                                        MMPolyMetaInf firstArgMetaInf =  auxPairFirstArg.x.getMetaInf();
                                        MMPolyMetaInf scndArgMetaInf  =  auxPairScndArg.x.getMetaInf();
                                        if(((firstArgMetaInf == MMPolyMetaInf.Constant || firstArgMetaInf == MMPolyMetaInf.VarPoly)) &&
                                            (scndArgMetaInf == MMPolyMetaInf.Constant || scndArgMetaInf == MMPolyMetaInf.VarPoly)) {

                                            VarPolynomial childX = auxPairFirstArg.x.getVarPolynomial();
                                            VarPolynomial childY = auxPairScndArg.x.getVarPolynomial();
                                            VarPolynomial parent = actInterpr.getVarPolynomial();

                                            Map<String, VarPolynomial> auxMap = new LinkedHashMap<String, VarPolynomial>(2);
                                            auxMap.put(MyModel.firstArg, childX);
                                            auxMap.put(MyModel.scndArg, childY);

                                            if(Globals.DEBUG_PATWIE && MyModel.log.isLoggable(Level.FINEST)) {
                                                long l1 = System.nanoTime();
                                                VarPolynomial vp = parent.substituteVariables(auxMap);
                                                long l2 = System.nanoTime();
                                                mmp = MaxMinPolynomial.create(vp);
                                                long l3 = System.nanoTime();
                                                MyModel.log.log(Level.FINEST, "Time for substitution on VPs : " +(l2-l1));
                                                MyModel.log.log(Level.FINEST, "Time for substituition plus building the new MMP : " + (l3-l1));
                                            }
                                            else {
                                                VarPolynomial vp = parent.substituteVariables(auxMap);
                                                mmp = MaxMinPolynomial.create(vp);
                                            }
                                            resultPair.setKey(mmp);
                                            this.labelMap.put(fApp, mmp);
                                        }
                                        else {
                                            // fill substitutionMap
                                            substMap.put(MyModel.firstArg, auxPairFirstArg.x);
                                            substMap.put(MyModel.scndArg, auxPairScndArg.x);
                                            if(Globals.DEBUG_PATWIE && MyModel.log.isLoggable(Level.FINEST)) {
                                                long l1 = System.nanoTime();
                                                mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                                long l2 = System.nanoTime();
                                                MyModel.log.log(Level.FINEST, "Time for substitution on MMPs : " +(l2-l1));
                                            }
                                            else {
                                                mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                            }
                                            resultPair.setKey(mmp);
                                            this.labelMap.put(fApp, mmp);
                                        }
                                    }
                                    else {
                                        // fill substitutionMap
                                        substMap.put(MyModel.firstArg, auxPairFirstArg.x);
                                        substMap.put(MyModel.scndArg, auxPairScndArg.x);
                                        if(Globals.DEBUG_PATWIE && MyModel.log.isLoggable(Level.FINEST)) {
                                            long l1 = System.nanoTime();
                                            mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                            long l2 = System.nanoTime();
                                            MyModel.log.log(Level.FINEST, "Time for substitution on MMPs : " +(l2-l1));
                                        }
                                        else {
                                            mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                        }
                                        resultPair.setKey(mmp);
                                        this.labelMap.put(fApp, mmp);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            return resultPair;
        }
    }



    /**
     *
     * @param term, the term whose label should be calculated
     * @param intMap, a map where the interpretation to the function symbols is stored, <br>
     * <b> NOTE: this map has nothing to do with the interpretation stored in <i>this</i>, unless
     * the user calls it with the interpretation stored in <i>this</i>, which actually
     * has a method of its own!! </b>
     * @return a MaxMinPolynomial iff the intMap had all information which are necessary <br>
     * a function symbol iff the calculation depends on this function symbol
     * and it has not assigned an interpretation so far.
     */
    public Pair<MaxMinPolynomial, FunctionSymbol> calculateMMpolyOfTermWithIntMap (
            TRSTerm term, Map<FunctionSymbol, MaxMinPolynomial> intMap) {
        Pair<MaxMinPolynomial, FunctionSymbol> resultPair = new Pair<MaxMinPolynomial, FunctionSymbol>(null, null);
        HashMap <String, MaxMinPolynomial> substMap = new HashMap<String, MaxMinPolynomial>(2);

        if(term.isVariable()) {
            TRSVariable v = (TRSVariable) term;
            resultPair.setKey( MaxMinPolynomial.create(VarPolynomial.createVariable(v.getName())));
        }
        else{
            TRSFunctionApplication fApp = (TRSFunctionApplication) term;
            FunctionSymbol fSym = fApp.getRootSymbol();
            MaxMinPolynomial actInterpr = intMap.get(fSym);
            if(actInterpr == null) {
                resultPair.setValue(fSym);
            }
            else {
                MMPolyMetaInf actMetaInf = actInterpr.getMetaInf();
                if(actMetaInf == MMPolyMetaInf.Constant) {
                    resultPair.setKey(actInterpr);
                   // return resultPair;
                }
                else {
                    // first check the number of Variables in the actInterpr,
                    // to decide which arguments are relevant
                    LinkedHashSet<String> actInterprVars = actInterpr.getAllVariableNames();
                    int actInterprVarsSize = actInterprVars.size();

                    if(actInterprVarsSize ==1) {
                        if(actInterprVars.contains(MyModel.firstArg)) {
                            Pair<MaxMinPolynomial, FunctionSymbol> auxPairFirstArg =
                                this.calculateMMpolyOfTermWithIntMap(fApp.getArgument(0), intMap);
                            // Check if the intMap had all the information to label childX
                            if(auxPairFirstArg.x == null) {
                                resultPair = auxPairFirstArg;
                              //  return auxPairChildX;
                            }
                            else {
                                // check if the MaxMinPoly of the firstArg is just an encapsulated VarPolynomial
                                // Then we can use the substitution of the VarPolys.
                                MMPolyMetaInf firstArgMetaInf =  auxPairFirstArg.x.getMetaInf();
                                if(firstArgMetaInf == MMPolyMetaInf.Constant || firstArgMetaInf == MMPolyMetaInf.VarPoly) {
                                    VarPolynomial childX = auxPairFirstArg.x.getVarPolynomial();
                                    // The actual Interpretation needs to be just an encapsulated VarPoly as well,
                                    // if we want to use the substitution of the VarPolys.
                                    if(actMetaInf == MMPolyMetaInf.VarPoly) {
                                        VarPolynomial vpParent = actInterpr.getVarPolynomial();
                                        Map<String, VarPolynomial> auxMap = new LinkedHashMap<String, VarPolynomial>(1);
                                        auxMap.put(MyModel.firstArg, childX);
                                        VarPolynomial vp = vpParent.substituteVariables(auxMap);
                                        MaxMinPolynomial mmp = MaxMinPolynomial.create(vp);
                                        resultPair.setKey(mmp);
                                    }
                                    else {
                                        // fill substitutionMap
                                        substMap.put(MyModel.firstArg, auxPairFirstArg.x);
                                        MaxMinPolynomial mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                        resultPair.setKey(mmp);
                                    }
                                }
                                else {
                                    // fill substitutionMap
                                    substMap.put(MyModel.firstArg, auxPairFirstArg.x);
                                    MaxMinPolynomial mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                    resultPair.setKey(mmp);
                                }
                            }
                        }
                        else {// actInterpVars consists only of scndArg
                            Pair<MaxMinPolynomial, FunctionSymbol> auxPairScndArg =
                                this.calculateMMpolyOfTermWithIntMap(fApp.getArgument(1), intMap);

                            // Check if the intMap had all the information to label childY
                            if(auxPairScndArg.x == null) {
                                resultPair = auxPairScndArg;
                            }
                            else {
                                // check if the MaxMinPoly of the scndArg is just an encapsulated VarPolynomial
                                // Then we can use the substitution of the VarPolys.
                                MMPolyMetaInf scndArgMetaInf =  auxPairScndArg.x.getMetaInf();
                                if(scndArgMetaInf == MMPolyMetaInf.Constant || scndArgMetaInf == MMPolyMetaInf.VarPoly) {
                                    VarPolynomial childY = auxPairScndArg.x.getVarPolynomial();
                                    // The actual Interpretation needs to be just an encapsulated VarPoly as well,
                                    // if we want to use the substitution of the VarPolys.
                                    if(actMetaInf == MMPolyMetaInf.VarPoly) {
                                        VarPolynomial vpParent = actInterpr.getVarPolynomial();
                                        Map<String, VarPolynomial> auxMap = new LinkedHashMap<String, VarPolynomial>(1);
                                        auxMap.put(MyModel.scndArg, childY);
                                        VarPolynomial vp = vpParent.substituteVariables(auxMap);
                                        MaxMinPolynomial mmp = MaxMinPolynomial.create(vp);
                                        resultPair.setKey(mmp);
                                    }
                                    else {
                                        // fill substitutionMap
                                        substMap.put(MyModel.scndArg, auxPairScndArg.x);
                                        MaxMinPolynomial mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                        resultPair.setKey(mmp);
                                    }
                                }
                                else {
                                    // fill substitutionMap
                                    substMap.put(MyModel.scndArg, auxPairScndArg.x);
                                    MaxMinPolynomial mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                    resultPair.setKey(mmp);
                                }
                            }
                        }
                    }
                    else { // actInterpVars has size 2, consists of firstArg and scndArg, so both children are relevant!
                        Pair<MaxMinPolynomial, FunctionSymbol> auxPairFirstArg =
                            this.calculateMMpolyOfTermWithIntMap(fApp.getArgument(0), intMap);
                        if(auxPairFirstArg.x == null) {
                            resultPair = auxPairFirstArg;
                        }
                        else {
                            Pair<MaxMinPolynomial, FunctionSymbol> auxPairScndArg =
                                this.calculateMMpolyOfTermWithIntMap(fApp.getArgument(1), intMap);
                            if(auxPairScndArg.x == null) {
                                resultPair = auxPairScndArg;
                            }
                            else {
                                // The actual Interpretation and both children need to be just encapsulated VarPolys,
                                // if we want to use the substitution of the VarPolys.
                                if (actMetaInf == MMPolyMetaInf.VarPoly) {
                                    MMPolyMetaInf firstArgMetaInf =  auxPairFirstArg.x.getMetaInf();
                                    MMPolyMetaInf scndArgMetaInf  =  auxPairScndArg.x.getMetaInf();
                                    if(((firstArgMetaInf == MMPolyMetaInf.Constant || firstArgMetaInf == MMPolyMetaInf.VarPoly)) &&
                                        (scndArgMetaInf == MMPolyMetaInf.Constant || scndArgMetaInf == MMPolyMetaInf.VarPoly)) {

                                        VarPolynomial childX = auxPairFirstArg.x.getVarPolynomial();
                                        VarPolynomial childY = auxPairScndArg.x.getVarPolynomial();
                                        VarPolynomial parent = actInterpr.getVarPolynomial();

                                        Map<String, VarPolynomial> auxMap = new LinkedHashMap<String, VarPolynomial>(2);
                                        auxMap.put(MyModel.firstArg, childX);
                                        auxMap.put(MyModel.scndArg, childY);
                                        VarPolynomial vp = parent.substituteVariables(auxMap);
                                        MaxMinPolynomial mmp = MaxMinPolynomial.create(vp);
                                        resultPair.setKey(mmp);
                                    }
                                    else {
                                        // fill substitutionMap
                                        substMap.put(MyModel.firstArg, auxPairFirstArg.x);
                                        substMap.put(MyModel.scndArg, auxPairScndArg.x);
                                        MaxMinPolynomial mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                        resultPair.setKey(mmp);
                                    }
                                }
                                else {
                                    // fill substitutionMap
                                    substMap.put(MyModel.firstArg, auxPairFirstArg.x);
                                    substMap.put(MyModel.scndArg, auxPairScndArg.x);
                                    MaxMinPolynomial mmp = actInterpr.substituteVariables(substMap, this.carrier);
                                    resultPair.setKey(mmp);
                                }
                            }
                        }
                    }
                }
            }
        }
        return resultPair;
    }

    private int calcHashCode() {
        return (23*this.labelMap.hashCode() + this.carrier + this.status.hashCode());

    }

    @Override
    public int hashCode() {
        return this.hashcode;
    }

    @Override
    public boolean equals(Object other){
        if (other instanceof MyModel) {
            MyModel otherModel = (MyModel) other;
            if(this.hashcode == otherModel.hashcode) {
                if(this.carrier == otherModel.carrier) {
                    if(this.status.equals(otherModel.status)){
                        if(this.interpretation.equals(otherModel.interpretation)) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public void print() {
        System.out.println(this.toString());
    }

    public String toHTML() {
        return this.export(new HTML_Util());
    }

    public String export (Export_Util eu) {
        StringBuilder buffer = new StringBuilder();
        buffer.append("Status: ");
        buffer.append(this.status.toString());
        buffer.append(eu.linebreak());
        for(Map.Entry<FunctionSymbol, MaxMinPolynomial> entry : this.interpretation.entrySet()) {
            buffer.append(entry.getKey().getName());
            buffer.append(" : ");
            buffer.append(entry.getValue());
            buffer.append(eu.linebreak());
        }
        return buffer.toString();
    }

    public String exportInterpretation (Export_Util eu) {
        StringBuilder buffer = new StringBuilder();
        for(Map.Entry<FunctionSymbol, MaxMinPolynomial> entry : this.interpretation.entrySet()) {
            buffer.append(entry.getKey().getName());
            buffer.append(" : ");
            buffer.append(entry.getValue());
            buffer.append(eu.linebreak());
        }
        return buffer.toString();
    }



}
