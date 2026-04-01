package aprove.verification.dpframework.BasicStructures.MaxMinPolynomials;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.Processors.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * @author Patrick Wiehe
 * @version $Id$
 *
 *Representation of MaxMinPolynomials in a normal form.
 *A MaxMinPolynomial is represented as a set of sets of VarPolynomials.
 *The inner sets represent the minimum operation on the encapsulated
 *VarPolynomials and the outer set represents the maxmimum operation
 *on the encapsulated inner sets.
 *Every polynomial which makes use of the maximum and/or minimum operation
 *can be transformed into this normal form (simply by moving all other
 *operations further innward).
 *
 *Furthermore some helpful values are cashed to easen operations on
 *the MaxMinPolynomials.
 */

public class MaxMinPolynomial implements XMLObligationExportable {

    private final ImmutableSet<? extends ImmutableSet<VarPolynomial>> maxMinPoly;
    private final MMPolyMetaInf metaInf;
    private final VarPolynomial encapsulatedVarPoly;
    private final ImmutableSet<ImmutableMap<String, ImmutableList<VarPolynomial>>> varMapping;

    private static Set<VarPolynomial> dummySetZero = java.util.Collections.<VarPolynomial>singleton(VarPolynomial.ZERO);
    private static Set<VarPolynomial> dummySetOne = java.util.Collections.<VarPolynomial>singleton(VarPolynomial.ONE);
    public static final MaxMinPolynomial ZERO = MaxMinPolynomial.create();
    public static MaxMinPolynomial getZERO() {
        return MaxMinPolynomial.ZERO;
    }
    public static final MaxMinPolynomial ONE = MaxMinPolynomial.createMinPoly(MaxMinPolynomial.dummySetOne);
    public static MaxMinPolynomial getONE() {
        return MaxMinPolynomial.ONE;
    }

    public static LinkedList<LinkedList<VarPolynomial>> myMin(final MaxMinPolynomial mmp1, final MaxMinPolynomial mmp2) {
        final LinkedList<LinkedList<VarPolynomial>> resultList =
            new LinkedList<LinkedList<VarPolynomial>>();
        final LinkedList<ArrayList<ArrayList<VarPolynomial>>> storeList =
            new LinkedList<ArrayList<ArrayList<VarPolynomial>>>();
        VarPolynomial diff;
        for(final ImmutableSet<VarPolynomial> minSet1 : mmp1.maxMinPoly) {
            final ArrayList<ArrayList<VarPolynomial>> minList =
                new ArrayList<ArrayList<VarPolynomial>>();
            for(final ImmutableSet<VarPolynomial> minSet2 : mmp2.maxMinPoly) {
                for(final VarPolynomial vp1 : minSet1) {
                    final ArrayList<VarPolynomial> maxList = new ArrayList<VarPolynomial>();
                    for(final VarPolynomial vp2 : minSet2) {
                        diff = vp1.minus(vp2);
                        maxList.add(diff);
                    }
                    minList.add(maxList);
                }
            }
            storeList.add(minList);
        }
        for(final ArrayList<ArrayList<VarPolynomial>> maxSetList : storeList) {
            resultList.addAll(MaxMinPolynomial.minOverMaxFunction(maxSetList));
        }
        return resultList;
    }

    public static LinkedList<LinkedList<VarPolynomial>> minOverMaxFunction(final ArrayList<ArrayList<VarPolynomial>> maxSetList) {
        final int[] restrictingArray = new int[maxSetList.size()];
        int[] counterArray = new int[maxSetList.size()];

        final LinkedList<LinkedList<VarPolynomial>> resultList =
            new LinkedList<LinkedList<VarPolynomial>>();
        for(int i=0; i<maxSetList.size(); i++) {
            restrictingArray[i] = (maxSetList.get(i).size() -1);
            counterArray[i] = 0;
        }
        LinkedList<VarPolynomial> innerResult = new LinkedList<VarPolynomial>();
        for(int j=0; j<maxSetList.size(); j++) {
            final ArrayList<VarPolynomial> actList = maxSetList.get(j);
            innerResult.add(actList.get(0));
        }
        resultList.add(innerResult);
        while(MaxMinPolynomial.myHasNext(counterArray, restrictingArray)) {
            innerResult = new LinkedList<VarPolynomial>();
            counterArray = MaxMinPolynomial.myGetNext(counterArray, restrictingArray);
            for(int i=0; i<maxSetList.size(); i++){
                final ArrayList<VarPolynomial> actList = maxSetList.get(i);
                innerResult.add(actList.get(counterArray[i]));
            }
            resultList.add(innerResult);
        }
        return resultList;
    }

    private static boolean myHasNext(final int[] array, final int[] restrictingArray) {
        for (int i=(array.length -1); i>-1; i--) {
            if(array[i] < restrictingArray[i]) {
                return true;
            }
        }
        return false;
    }

    private static int[] myGetNext(final int[] array, final int[] restrictingArray) {
        for (int i=(array.length -1); i>-1; i--) {
            if(array[i] < restrictingArray[i]) {
                array[i] = (array[i] +1);
                return array;
            }
            else {
                if(array[i] == restrictingArray[i]) {
                    array[i] = 0;
                }
            }
        }
        return null;
    }


    private Triple<Set<ImmutableMap<String, ImmutableList<VarPolynomial>>>, MMPolyMetaInf, VarPolynomial>
                calculateMetaInf(final Collection<? extends Set<VarPolynomial>> mmpoly)
    {
        final Pair<Boolean, VarPolynomial> encapsVpAuxPair = new Pair<Boolean, VarPolynomial>(true, null);
        final Set<ImmutableMap<String, ImmutableList<VarPolynomial>>> mapSet =
            new LinkedHashSet<ImmutableMap<String, ImmutableList<VarPolynomial>>>();
        final Triple<Set<ImmutableMap<String, ImmutableList<VarPolynomial>>>, MMPolyMetaInf, VarPolynomial> resultTriple =
            new Triple<Set<ImmutableMap<String,ImmutableList<VarPolynomial>>>, MMPolyMetaInf, VarPolynomial>(null, null, null);
        if(mmpoly.size()>1) {
            encapsVpAuxPair.x = false;
            resultTriple.setY(MMPolyMetaInf.MaxInterpretation);
        }
        for(final Set<VarPolynomial> vpSet : mmpoly) {
            if( encapsVpAuxPair.x &&(vpSet.size() > 1) ) {
                encapsVpAuxPair.x = false;
                resultTriple.setY(MMPolyMetaInf.MinInterpretation);
            }

            final Map<String, LinkedList<VarPolynomial>> workingMap =
                new HashMap <String, LinkedList<VarPolynomial>>();
            for (final VarPolynomial vp : vpSet) {
                if(encapsVpAuxPair.x) {
                    resultTriple.setZ(vp);
                    if(vp.isConstant()) {
                        resultTriple.setY(MMPolyMetaInf.Constant);
                    }
                    else {
                        resultTriple.setY(MMPolyMetaInf.VarPoly);
                    }
                }
                final Set<String> vars = vp.getVariables();
                if(vars.size() == 0) {
                    final LinkedList<VarPolynomial> actList = new LinkedList<VarPolynomial>();
                    actList.add(vp);
                    workingMap.put(null, actList);
                }
                else {
                    for(final String var : vars) {
                        LinkedList<VarPolynomial> actList = workingMap.get(var);
                        if(actList == null) {
                            actList = new LinkedList<VarPolynomial>();
                        }
                        actList.add(vp);
                        workingMap.put(var, actList);
                    }
                }
            }
            final Map<String, ImmutableList<VarPolynomial>> auxMap =
                new HashMap <String, ImmutableList<VarPolynomial>>();
            final Set<Map.Entry<String, LinkedList<VarPolynomial>>> immutableAuxSet =  workingMap.entrySet();
            for(final Map.Entry<String, LinkedList<VarPolynomial>> workingEntry : immutableAuxSet) {
                final ImmutableList<VarPolynomial> immuList = ImmutableCreator.create(workingEntry.getValue());
                auxMap.put(workingEntry.getKey(), immuList);
            }
            final ImmutableMap<String, ImmutableList<VarPolynomial>> immuAuxMap = ImmutableCreator.create(auxMap);
            mapSet.add(immuAuxMap);
        }
        final ImmutableSet<ImmutableMap<String, ImmutableList<VarPolynomial>>> immuSet =
            ImmutableCreator.create(mapSet);
        resultTriple.setX(immuSet);
        return resultTriple;
    }

    private MaxMinPolynomial (final Collection<? extends Set<VarPolynomial>> mmpoly) {
        Triple<Set<ImmutableMap<String, ImmutableList<VarPolynomial>>>, MMPolyMetaInf, VarPolynomial> metaInfTriple;
        final LinkedHashSet<ImmutableLinkedHashSet<VarPolynomial>> dummySet = new LinkedHashSet<ImmutableLinkedHashSet<VarPolynomial>>();
        for (final Set<VarPolynomial>  minSet : mmpoly) {
            final LinkedHashSet<VarPolynomial> dummyMinSet = new LinkedHashSet<VarPolynomial>(minSet);
            dummySet.add(ImmutableCreator.create(dummyMinSet));
        }
        this.maxMinPoly = ImmutableCreator.create(dummySet);
        metaInfTriple = this.calculateMetaInf(mmpoly);
        this.metaInf = metaInfTriple.getY();
        this.encapsulatedVarPoly = metaInfTriple.getZ();
        this.varMapping = ImmutableCreator.create(metaInfTriple.getX());
    }

    private MaxMinPolynomial (final Collection<? extends Set<VarPolynomial>> mmpoly,
                              final Set<ImmutableMap<String, ImmutableList<VarPolynomial>>> mapSet,
                              final VarPolynomial encapsVP)
    {
        final LinkedHashSet<ImmutableLinkedHashSet<VarPolynomial>> dummySet = new LinkedHashSet<ImmutableLinkedHashSet<VarPolynomial>>();
        for (final Set<VarPolynomial>  minSet : mmpoly) {
            final LinkedHashSet<VarPolynomial> dummyMinSet = new LinkedHashSet<VarPolynomial>(minSet);
            dummySet.add(ImmutableCreator.create(dummyMinSet));
        }
        this.maxMinPoly = ImmutableCreator.create(dummySet);
        this.varMapping = ImmutableCreator.create(mapSet);
        this.encapsulatedVarPoly = encapsVP;
        if(encapsVP.isConstant()) {
            this.metaInf = MMPolyMetaInf.Constant;
        }
        else {
            this.metaInf = MMPolyMetaInf.VarPoly;
        }
    }

    private MaxMinPolynomial(final ImmutableLinkedHashSet<ImmutableLinkedHashSet<VarPolynomial>> mmp,
                             final ImmutableLinkedHashSet<ImmutableMap<String, ImmutableList<VarPolynomial>>> mapSet,
                             final MMPolyMetaInf mInf,
                             final VarPolynomial encapsVP) {
        this.maxMinPoly = mmp;
        this.varMapping = mapSet;
        this.metaInf = mInf;
        this.encapsulatedVarPoly = encapsVP;
    }

    public static MaxMinPolynomial create () {
        final HashSet<Set<VarPolynomial>> maxminSet = new HashSet<Set<VarPolynomial>>(1);
        maxminSet.add(MaxMinPolynomial.dummySetZero);
        final LinkedList<VarPolynomial> dummyList = new LinkedList<VarPolynomial>();
        dummyList.add(VarPolynomial.ZERO);
        final HashMap<String, ImmutableList<VarPolynomial>> dummyMap = new HashMap<String, ImmutableList<VarPolynomial>>(1);
        dummyMap.put(null, ImmutableCreator.create(dummyList));
        final Set<ImmutableMap<String, ImmutableList<VarPolynomial>>> maps =
            new HashSet<ImmutableMap<String, ImmutableList<VarPolynomial>>>();
        maps.add(ImmutableCreator.create(dummyMap));
        return new MaxMinPolynomial(maxminSet, maps, VarPolynomial.ZERO);
    }

    public static MaxMinPolynomial create (final VarPolynomial varPoly) {
        final Set<VarPolynomial> mpolys = new HashSet<VarPolynomial>(1);
        mpolys.add(varPoly);
        final Set<Set<VarPolynomial>> mmPoly = new HashSet<Set<VarPolynomial>>(1);
        mmPoly.add(mpolys);
        final LinkedList<VarPolynomial> dummyList = new LinkedList<VarPolynomial>();
        dummyList.add(varPoly);
        final HashMap<String, ImmutableList<VarPolynomial>> dummyMap = new HashMap<String, ImmutableList<VarPolynomial>>(1);
        final Set<String> varPolyNames = varPoly.getVariables();
        if(varPolyNames.size() == 0) {
            dummyMap.put(null, ImmutableCreator.create(dummyList));
        }
        for(final String varName : varPolyNames) {
            dummyMap.put(varName, ImmutableCreator.create(dummyList));
        }
        final Set<ImmutableMap<String, ImmutableList<VarPolynomial>>> maps =
            new HashSet<ImmutableMap<String, ImmutableList<VarPolynomial>>>();
        maps.add(ImmutableCreator.create(dummyMap));
        return new MaxMinPolynomial(mmPoly, maps, varPoly);
    }

    public static MaxMinPolynomial createMinPoly (final Collection<VarPolynomial> mpoly) {
        final Set<VarPolynomial> dummySet = new HashSet<VarPolynomial>(mpoly);
        final Set<Set<VarPolynomial>> mmPoly = new HashSet<Set<VarPolynomial>>(1);
        mmPoly.add(dummySet);
        return new MaxMinPolynomial(mmPoly);
    }

    public static MaxMinPolynomial create (final Collection<? extends Set<VarPolynomial>> mmpoly) {
        return new MaxMinPolynomial(mmpoly);
    }

    public ImmutableSet< ? extends ImmutableSet<VarPolynomial>> getAllMinSets(){
        return this.maxMinPoly;
    }


    /**
     * Returns the VarPolynomial of this
     * iff this is just a VarPolynomial
     * encapsulated in a MaxMinPolynomial,
     * null otherwise
     */
    public VarPolynomial getVarPolynomial () {
        return this.encapsulatedVarPoly;
    }

    public MMPolyMetaInf getMetaInf () {
        return this.metaInf;
    }

    public ImmutableSet<ImmutableMap<String, ImmutableList<VarPolynomial>>> getVariableMapping() {
        return this.varMapping;
    }

    public boolean containsVariable(final String variable) {
        switch(this.metaInf) {
        case Constant : {
            return false;
        }
        case VarPoly : {
            return this.varMapping.iterator().next().containsKey(variable);
        }
        case MinInterpretation : {
            return this.varMapping.iterator().next().containsKey(variable);
        }
        case MaxInterpretation : {
            boolean variableFound = false;
            final Iterator<ImmutableMap<String, ImmutableList<VarPolynomial>>> iter =
                this.varMapping.iterator();
            while((!variableFound) && iter.hasNext()) {
                variableFound = iter.next().containsKey(variable);
            }
            return variableFound;
        }
        default : {
            throw new RuntimeException("Enum MMPolyMetaInf has been modified!");
        }
        }
    }

    /**
     *
     * @param vars the set of "allowed" variable names
     * @return true, if this contains only variables
     * with names out of <i>vars </i>. <br>
     * false otherwise
     */
    public boolean containsMaximalSetOfVariables(final Set<String> vars) {
        switch(this.metaInf) {
        case Constant : {
            return true;
        }
        case VarPoly : {
            final Set<String> varsOfPoly = this.varMapping.iterator().next().keySet();
            return vars.containsAll(varsOfPoly);
        }
        case MinInterpretation : {
            final Set<String> varsOfPoly = this.varMapping.iterator().next().keySet();
            return vars.containsAll(varsOfPoly);
        }
        case MaxInterpretation : {
            boolean allVariableNamesLegal = true;
            final Iterator<ImmutableMap<String, ImmutableList<VarPolynomial>>> iter =
                this.varMapping.iterator();
            while(allVariableNamesLegal && iter.hasNext()) {
                final Set<String> varsOfPoly = iter.next().keySet();
                allVariableNamesLegal =  vars.containsAll(varsOfPoly);
            }
            return allVariableNamesLegal;
        }
        default : {
            throw new RuntimeException("Enum MMPolyMetaInf has been modified!");
        }
        }
    }


    public boolean mmpDomination (final MaxMinPolynomial other) {
        final Iterator<ImmutableMap<String, ImmutableList<VarPolynomial>>> otherOuterIter =  other.varMapping.iterator();
        final Iterator<ImmutableMap<String, ImmutableList<VarPolynomial>>> thisOuterIter =  this.varMapping.iterator();

        boolean otherAllDominated = true;

        while(otherAllDominated && otherOuterIter.hasNext()) {
            final ImmutableMap<String , ImmutableList<VarPolynomial>> otherMap = otherOuterIter.next();

            boolean dominated = false;
            while((!dominated) && thisOuterIter.hasNext()) {
                final ImmutableMap<String , ImmutableList<VarPolynomial>> thisMap = thisOuterIter.next();
                dominated = MaxMinPolynomial.minTermDomination(otherMap, thisMap);
            }
            if(!dominated) {
                otherAllDominated = false;
            }

        }
        return otherAllDominated;

        /*
        Map<String , ImmutableList<VarPolynomial>> otherMap = otherOuterIter.next();
        Set<Map.Entry<String, ImmutableList<VarPolynomial>>> otherMapEntrys = otherMap.entrySet();
        Iterator <Map.Entry<String, ImmutableList<VarPolynomial>>> otherMapEntrysIterator = otherMapEntrys.iterator();

        Map<String , ImmutableList<VarPolynomial>> thisMap = thisOuterIter.next();

        //boolean noConflict = true;

        while((otherMapEntrysIterator.hasNext()) && noConflict) {
            Map.Entry<String, ImmutableList<VarPolynomial>> actEntry = otherMapEntrysIterator.next();
            ImmutableList<VarPolynomial> smallTermList = actEntry.getValue();
            ImmutableList<VarPolynomial> bigTermList = thisMap.get(actEntry.getKey());

            Iterator<VarPolynomial> smalltermListIterator = smallTermList.iterator();
            Iterator<VarPolynomial> bigtermListIterator = bigTermList.iterator();

            while((smalltermListIterator.hasNext()) && noConflict ) {

                VarPolynomial actSmallVp = smalltermListIterator.next();
                boolean notDominated = true;

                while((bigtermListIterator.hasNext()) && notDominated ) {

                    VarPolynomial actBigVp = bigtermListIterator.next();
                    VarPolynomial difference = actBigVp.minus(actSmallVp);

                    if(difference.allPositive()) {
                        notDominated = false;
                    }
                }
                if(notDominated) {
                    noConflict = false;
                }
            }
        }
        return noConflict;
        */
    }


    /**
     *
     * @param smallSetMap representing the MinSet smallCandidat, for which should
     * be checked if it is dominated by bigCandidat
     * @param bigSetMap representing the MinSet bigCandidat, for which should
     * be checked if it dominates smallCandidat
     * @return true if bigCandidat dominates smallCandidat, false otherwise
     */

    //Check if every Vp in bigSetMap dominates one Vp in smallSetMap.
    public static boolean minTermDomination (
                final ImmutableMap<String, ImmutableList<VarPolynomial>> smallSetMap,
                final ImmutableMap<String, ImmutableList<VarPolynomial>> bigSetMap)
    {
        final Set<Map.Entry<String, ImmutableList<VarPolynomial>>> bigSetMapEntrys = bigSetMap.entrySet();
        final Iterator<Map.Entry<String, ImmutableList<VarPolynomial>>> bigSetMapEntrysIterator = bigSetMapEntrys.iterator();

        boolean noConflict = true;

        while(noConflict && bigSetMapEntrysIterator.hasNext()) {
            final Map.Entry<String, ImmutableList<VarPolynomial>> actEntry = bigSetMapEntrysIterator.next();
            final ImmutableList<VarPolynomial> bigTermList = actEntry.getValue();
            ImmutableList<VarPolynomial> smalltermList;
            final Iterator<VarPolynomial> bigTermListIterator = bigTermList.iterator();
            //Check for every Vp in bigTermList if it dominates one Vp in smallTermList.
            //If it doesn't, set noConflict to false, to indicate that the minSet bigCandidat
            //represented by bigSetMap doesn't dominate the minSet represented by smallSetMap.
            while(noConflict && (bigTermListIterator.hasNext())) {
                final VarPolynomial actBigVp = bigTermListIterator.next();
                smalltermList = smallSetMap.get(actEntry.getKey());
                if(smalltermList == null) {
                    noConflict = false;
                }
                else {
                    final Iterator<VarPolynomial> smallTermListIterator = smalltermList.iterator();

                    boolean notDominated = true;
                    //Try to find a Vp in the smallTermList which is dominated by the
                    //actBigVp, since every Vp in the bigTermList has to dominate one Vp
                    //in the minSet smallCandidat represented by smallSetMap,
                    //to fulflill the domination criteria.
                    while(notDominated && (smallTermListIterator.hasNext())) {
                        final VarPolynomial actSmallVp = smallTermListIterator.next();
                        final VarPolynomial difference = actBigVp.minus(actSmallVp);

                        if(difference.allPositive()) {
                            notDominated = false;
                        }
                    }
                    //If the actBigVp doesn't dominate one Vp in in smallSetMap
                    //the MinSet bigCandidat can not dominate the minSet smallCandidat.
                    //Set noConflict to false to abort calculation.
                    if(notDominated) {
                        noConflict = false;
                    }
                }
            }
        }
        return noConflict;
    }

    // Checks if this dominates other,
    // returns this if successful, null otherwise.
    public MaxMinPolynomial dominanceCheck (final MaxMinPolynomial other) {

            final Iterator<ImmutableMap<String, ImmutableList<VarPolynomial>>> otherOuterIter =  other.varMapping.iterator();
            final Map<String , ImmutableList<VarPolynomial>> otherMap = otherOuterIter.next();
            final Set<Map.Entry<String, ImmutableList<VarPolynomial>>> otherMapEntrys = otherMap.entrySet();
            final Iterator <Map.Entry<String, ImmutableList<VarPolynomial>>> otherMapEntrysIterator = otherMapEntrys.iterator();

            final Iterator<ImmutableMap<String, ImmutableList<VarPolynomial>>> thisOuterIter =  this.varMapping.iterator();
            final Map<String , ImmutableList<VarPolynomial>> thisMap = thisOuterIter.next();
            /*
            Set<Map.Entry<String, ImmutableList<VarPolynomial>>> thisMapEntrys = thisMap.entrySet();
            Iterator <Map.Entry<String, ImmutableList<VarPolynomial>>> thisMapEntrysIterator = thisMapEntrys.iterator();
            */
            boolean noConflict = true;

            while((otherMapEntrysIterator.hasNext()) && noConflict) {
                final Map.Entry<String, ImmutableList<VarPolynomial>> actEntry = otherMapEntrysIterator.next();
                final ImmutableList<VarPolynomial> smallTermList = actEntry.getValue();
                final ImmutableList<VarPolynomial> bigTermList = thisMap.get(actEntry.getKey());

                final Iterator<VarPolynomial> smalltermListIterator = smallTermList.iterator();
                final Iterator<VarPolynomial> bigtermListIterator = bigTermList.iterator();

                while((smalltermListIterator.hasNext()) && noConflict ) {

                    final VarPolynomial actSmallVp = smalltermListIterator.next();
                    boolean notDominated = true;

                    while((bigtermListIterator.hasNext()) && notDominated ) {

                        final VarPolynomial actBigVp = bigtermListIterator.next();
                        final VarPolynomial difference = actBigVp.minus(actSmallVp);

                        if(difference.allPositive()) {
                            notDominated = false;
                        }
                    }
                    if(notDominated) {
                        noConflict = false;
                    }
                }
            }
            if(noConflict) {
                return this;
            }
            else {
                return null;
            }

    }

    public MaxMinPolynomial renameVariables(final Map<String, String> newNames) {
        MaxMinPolynomial resultMMP;

        LinkedList<VarPolynomial> vpList;
        final Map<String, LinkedList<VarPolynomial>> workingMap =
            new LinkedHashMap<String, LinkedList<VarPolynomial>>();
        final Map<String, ImmutableList<VarPolynomial>> dummyMap =
            new HashMap<String, ImmutableList<VarPolynomial>>();
        final LinkedHashSet<ImmutableMap<String, ImmutableList<VarPolynomial>>> metaInf =
            new LinkedHashSet<ImmutableMap<String,ImmutableList<VarPolynomial>>>();
        Set<String> vars;

        final Map<String, VarPolynomial> substMap = new LinkedHashMap<String, VarPolynomial>();
        final Set<Entry<String, String>> entries = newNames.entrySet();
        for(final Entry<String, String> e : entries){
            substMap.put(e.getKey(), VarPolynomial.createVariable(e.getValue()));
        }
        final LinkedHashSet<ImmutableLinkedHashSet<VarPolynomial>> newMaxSet =
            new LinkedHashSet<ImmutableLinkedHashSet<VarPolynomial>>();
        for( final Set<VarPolynomial> minSet : this.maxMinPoly) {
            final LinkedHashSet<VarPolynomial> newMinSet = new LinkedHashSet<VarPolynomial>();
            for(final VarPolynomial actVP : minSet) {
                final VarPolynomial newVP = actVP.substituteVariables(substMap);
                newMinSet.add(newVP);

                vars = newVP.getVariables();
                for(final String v : vars) {
                    vpList = workingMap.get(v);
                    if (vpList == null) {
                        vpList = new LinkedList<VarPolynomial>();
                    }
                    vpList.add(actVP);
                    workingMap.put(v, vpList);
                }
            }
            newMaxSet.add(ImmutableCreator.create(newMinSet));
            for(final Entry<String, LinkedList<VarPolynomial>> e : workingMap.entrySet()) {
                dummyMap.put(e.getKey(), ImmutableCreator.create(e.getValue()));
            }
            metaInf.add(ImmutableCreator.create(dummyMap));
        }
        resultMMP =
            new MaxMinPolynomial(ImmutableCreator.create(newMaxSet),
                                 ImmutableCreator.create(metaInf),
                                 this.metaInf,
                                 this.encapsulatedVarPoly);
        return resultMMP;
    }

    //Diese Methode bei Umstellung auf Maps nicht aendern!!
    public MaxMinPolynomial substituteVariables(final Map<String, MaxMinPolynomial> substMap, final int cSS) {
        MaxMinPolynomial resultMMP = null;

        for( final Set<VarPolynomial> minSets : this.maxMinPoly) {
            MaxMinPolynomial newMinMMP = null;

            for(final VarPolynomial actVP : minSets) {

                MaxMinPolynomial resultVP = null;
                final Map<IndefinitePart, SimplePolynomial> monomMap = actVP.getVarMonomials();
                if(monomMap.size() == 0) {
                    resultVP = MaxMinPolynomial.create(actVP);
                    newMinMMP = resultVP;
                }
                else{
                    for (final Map.Entry<IndefinitePart, SimplePolynomial> monomEntry : monomMap.entrySet()) {
                        MaxMinPolynomial resultMonom = MaxMinPolynomial.create();
                        final IndefinitePart key = monomEntry.getKey();
                        final BigInteger consMultiplikant = monomEntry.getValue().getNumericalAddend();
                        for (final Map.Entry<String, MaxMinPolynomial> substMapEntry : substMap.entrySet()){
                            final String variable = substMapEntry.getKey();
                            final int power = key.getExponent(variable);
                            if(power > 0) {// the Variable of the substitution occurs in the actual monom.
                                MaxMinPolynomial mmpToSubstitute = substMap.get(variable);
                                if (power > 1) {
                                    mmpToSubstitute = mmpToSubstitute.powerOf(power);
                                }
                                if(consMultiplikant.compareTo(BigInteger.ONE) > 0) {
                                    final MaxMinPolynomial consMultMMP = MaxMinPolynomial.create(VarPolynomial.create(consMultiplikant));
                                    resultMonom = consMultMMP.times(mmpToSubstitute);
                                }
                                else {
                                    resultMonom = mmpToSubstitute;
                                }
                                if(resultVP == null) {
                                    resultVP = resultMonom;
                                }
                                else {
                                    resultVP = resultVP.plus(resultMonom);
                                }
                            }
                        }

                    }
                    if (newMinMMP == null) {
                        if(resultVP==null) {
                            int foo = 5;
                            foo += 1;
                        }
                        newMinMMP = resultVP;
                    }
                    else {
                        if(cSS == -1) {
                            if(resultVP==null) {
                                int foo = 5;
                                foo += 1;
                            }
                            newMinMMP = newMinMMP.minimumInfiniteCarrier(resultVP);
                        }
                        else {
                            newMinMMP = newMinMMP.minimumFiniteCarrier(resultVP);
                        }
                    }
                }
            }
            if (resultMMP == null) {
                resultMMP = newMinMMP;
            }
            else {//TODO distinguish here between finite and infinite carrier!!
                if(cSS == -1) {
                    resultMMP = resultMMP.maximumFiniteCarrier(newMinMMP);
                }
                else {
                    resultMMP = resultMMP.maximumFiniteCarrier(newMinMMP);
                }
            }
        }
        return resultMMP;
    }


    public ImmutableLinkedHashSet<VarPolynomial> getAllMinTerms() {
        final LinkedHashSet<VarPolynomial> resultSet = new LinkedHashSet<VarPolynomial>();
        for(final Set<VarPolynomial> minSets : this.maxMinPoly) {
            resultSet.addAll(minSets);
        }
        return ImmutableCreator.create(resultSet);
    }

    public LinkedHashSet<String> getAllVariableNames() {
        final LinkedHashSet<String> resultSet = new LinkedHashSet<String>();
        for(final ImmutableMap<String, ImmutableList<VarPolynomial>> varMap : this.varMapping) {
            resultSet.addAll(varMap.keySet());
        }
        return resultSet;
    }

    @Override
    public boolean equals (final Object other) {
        if (other instanceof MaxMinPolynomial) {
            final MaxMinPolynomial otherPoly = (MaxMinPolynomial)other;
            return this.maxMinPoly.equals(otherPoly.maxMinPoly);
        }
        return false;
    }

    @Override
    public int hashCode() {
        return this.maxMinPoly.hashCode();
    }

    public int numberOfMinClauses() {
        return this.maxMinPoly.size();
    }

    public int numberOfVarPolys() {
        int number = 0;
        for(final Set<VarPolynomial> minClause : this.maxMinPoly){
            number = number + minClause.size();
        }
        return number;
    }

    /**
     * Adds two MaxMinPolynomials.
     * The result is again in "Normal Form",
     * e.g. a Set of Sets of VarPolynomial.
     * @param poly, the poly added to <b>this</b>
     * @return MaxMinPolynomial, the sum of <b>this</b> and <b>poly</b>
     * No simplification neccessary.
     */
    public MaxMinPolynomial plus (final MaxMinPolynomial poly) {
        return new PlusInterpretation(new ArgumentInterpretation(1),
                                      new ArgumentInterpretation(2)).interpret(this, poly);

    }

    /**
     * Multiplies two MaxMinPolynomials.
     * The result is again in "Normal Form",
     * e.g. a Set of Sets of VarPolynomial.
     * @param poly, the poly multiplied with <b>this</b>
     * @return MaxMinPolynomial, the product of <b>this</b> and <b>poly</b>
     * No simplification neccessary.
     */
    public MaxMinPolynomial times (final MaxMinPolynomial poly) {
        return new TimesInterpretation(new ArgumentInterpretation(1),
                                      new ArgumentInterpretation(2)).interpret(this, poly);

    }

    /**
     * Subtracts <b>poly</b> from <b>this</b>. <br>
     * <b>!NOTE!</b>The minimum is 0, there are no negative values! <br>
     * @param poly
     * @return maximum(0, (<b>this</b> minus <b>poly</b>))
     * The result is again in "Normal Form",
     * e.g. a Set of Sets of VarPolynomial.
     */

    public MaxMinPolynomial monos (final MaxMinPolynomial poly) {
        return  new MonosInterpretation(new ArgumentInterpretation(1), new ArgumentInterpretation(2)).interpret(this, poly);
    }

    public MaxMinPolynomial maximumFiniteCarrier (final MaxMinPolynomial poly) {
        return new MaximumInterpretationFiniteCarrier(new ArgumentInterpretation(1), new ArgumentInterpretation(2)).interpret(this, poly);
    }

    public MaxMinPolynomial maximumInfiniteCarrier (final MaxMinPolynomial poly) {
        return new MaximumInterpretationInfiniteCarrier(new ArgumentInterpretation(1), new ArgumentInterpretation(2)).interpret(this, poly);
    }

    public MaxMinPolynomial minimumFiniteCarrier (final MaxMinPolynomial poly) {
        return new MinimumInterpretationFiniteCarrier (new ArgumentInterpretation(1), new ArgumentInterpretation(2)).interpret(this, poly);
    }

    public MaxMinPolynomial minimumInfiniteCarrier (final MaxMinPolynomial poly) {
        return new MinimumInterpretationInfiniteCarrier (new ArgumentInterpretation(1), new ArgumentInterpretation(2)).interpret(this, poly);
    }


    public MaxMinPolynomial powerOf (final int exponent) {
        if(exponent<1) {
            return MaxMinPolynomial.create();
        }
        else {
            final Abortion aborter = AbortionFactory.create();
            final Set<Set<VarPolynomial>> resultSet = new LinkedHashSet<Set<VarPolynomial>>();
            for(final Set<VarPolynomial> minSets : this.maxMinPoly) {
                final LinkedHashSet<VarPolynomial> newMinSet = new LinkedHashSet<VarPolynomial>();
                for(final VarPolynomial vp : minSets) {
                    try {
                        // using an ad-hoc Abortion is nasty, do this only if you
                        // know what you are doing
                        newMinSet.add(vp.power(exponent, aborter));
                    } catch (final AbortionException e) {
                        throw new RuntimeException(e);
                    }
                }
                resultSet.add(newMinSet);
            }
            return MaxMinPolynomial.create(resultSet);
        }
    }

    public MaxMinPolynomial transformModulo(final int i) {
        if(Globals.useAssertions) {
            assert (i>0);
        }
        //iterate over the Sets of the MMP to transform every Varpoly modulo i
        final Iterator<? extends ImmutableSet<VarPolynomial>> iterMinSets = this.maxMinPoly.iterator();
        final Set<Set<VarPolynomial>> maxSetsModulo = new HashSet<Set<VarPolynomial>>();
        while(iterMinSets.hasNext()) {
            final Set<VarPolynomial> minSetOld  = iterMinSets.next();
            final Iterator<VarPolynomial> iterVarPoly = minSetOld.iterator();
            final Set<VarPolynomial> minSetsModulo = new HashSet<VarPolynomial>();
            while(iterVarPoly.hasNext()) {
                final VarPolynomial vp = iterVarPoly.next();
                minSetsModulo.add(vp.normalizeModulo(i));
            }
            maxSetsModulo.add(minSetsModulo);
        }
        return new MaxMinPolynomial(maxSetsModulo);
    }

    public BigInteger evaluate(final Map<String, Integer> valueMap) {

        switch(this.metaInf) {
        case Constant : {
            return this.getVarPolynomial().getConstantPart().getNumericalAddend();
        }
        case VarPoly : {
            final SimplePolynomial sp =this.getVarPolynomial().evaluate(valueMap);
            if(Globals.useAssertions) {
                assert(sp.isConstant());
            }
            return sp.getNumericalAddend();
        }
        case MinInterpretation : {
            final ImmutableLinkedHashSet<VarPolynomial> minSet = this.getAllMinTerms();
            BigInteger minValue = null;
            SimplePolynomial dummySP;
            for(final VarPolynomial vp : minSet) {
                dummySP = vp.evaluate(valueMap);
                if(Globals.useAssertions) {
                    assert(dummySP.isConstant());
                }
                if(minValue == null || dummySP.getNumericalAddend().compareTo(minValue) < 0) {
                    minValue = dummySP.getNumericalAddend();
                }
            }
            return minValue;
        }
        case MaxInterpretation : {
            BigInteger maxValue = BigInteger.ZERO;
            for(final ImmutableSet<VarPolynomial> minSet : this.maxMinPoly) {
                BigInteger minValue = null;
                SimplePolynomial dummySP;
                for(final VarPolynomial vp : minSet) {
                    dummySP = vp.evaluate(valueMap);
                    if(Globals.useAssertions) {
                        assert(dummySP.isConstant());
                    }
                    if(minValue == null || dummySP.getNumericalAddend().compareTo(minValue) < 0) {
                        minValue = dummySP.getNumericalAddend();
                    }
                }
                if(minValue.compareTo(maxValue) > 0) {
                    maxValue = minValue;
                }
            }
            return maxValue;
        }
        default : {
            throw new RuntimeException("Enum MMPolyMetaInf has been modified!");
        }
        }
    }

    public static void main (final String[] args) {
        /*
        MaxMinPolynomial mmPoly1 = MaxMinPolynomial.createAPoly(8);
        MaxMinPolynomial mmPoly2 = MaxMinPolynomial.createAPoly(9);
        MaxMinPolynomial mmPoly3 = MaxMinPolynomial.createAPoly(10);
        MaxMinPolynomial mmPoly4 = MaxMinPolynomial.createAPoly(11);
        MaxMinPolynomial mmPoly5 = MaxMinPolynomial.createAPoly(12);

        System.out.println(mmPoly3.varMapping.iterator().next());
        System.out.println(mmPoly3.varMapping.iterator().next().size());
        System.out.println(mmPoly3.varMapping.iterator().next().keySet());
        System.out.println(mmPoly3.varMapping.iterator().next().values());
        System.out.println();

        /*
        MaxMinPolynomial mmPoly6 = MaxMinPolynomial.createAPoly(8);
        MaxMinPolynomial mmPoly7 = MaxMinPolynomial.createAPoly(18);

        ImmutableSet<? extends ImmutableSet<VarPolynomial>> dummySet = mmPoly6.getAllMinSets();
        dummySet.clear();

        System.out.println("\nAddiere zwei Polys:");
        mmPoly6.addTwoMMpolys(mmPoly7);


        System.out.println("\nMultipliziere zwei Polys:");
        mmPoly3.timesiplyTwoMMpolys(mmPoly4);

        System.out.println("\nMaximum von zwei Polys:");
        mmPoly3.maxTwoMMpolys(mmPoly5);

        System.out.println("\nDifferenz von zwei Polys:");
        mmPoly1.subtractTwoMMpolys(mmPoly4);
        /*
        System.out.println("\nMinimum von zwei Polys:");
        mmPoly1.minTwoMMpolys(mmPoly4);
        */
        /*
        MaxMinPolynomial mmPolyA = createAPoly(20);
        MaxMinPolynomial mmPolyB = createAPoly(18);
        MaxMinPolynomial mmPolyResult;
        System.out.println();
        System.out.print("this  : ");
        mmPolyA.printMMpoly();
        System.out.print("other : ");
        mmPolyB.printMMpoly();

        mmPolyResult = mmPolyA.minimumInfiniteCarrier(mmPolyB);
        if(mmPolyResult!= null) {
            System.out.print("Result: ");
            mmPolyResult.printMMpoly();
        }

        System.out.println("\nDomCheck this >> other :");
        boolean bool1 = mmPolyA.mmpDomination(mmPolyB);
        System.out.println(bool1);

        System.out.println("\nDomCheck other >> this :");
        bool1 = mmPolyB.mmpDomination(mmPolyA);
        System.out.println(bool1);
        */


        /*
        System.out.println("\nMinimum of two Polys over natural numbers :");
        mmPolyA.minTwoMMpolysInfiniteCarrier(mmPolyB);

        System.out.println("\nMinimum of two Polys over natural numbers :");
        mmPolyB.minTwoMMpolysInfiniteCarrier(mmPolyA);
        */



        //TODO
        //TODO
        //TODO

        final MaxMinPolynomial mmp1 = MaxMinPolynomial.createAPoly(18);
        final MaxMinPolynomial mmp2 = MaxMinPolynomial.createAPoly(20);

        mmp1.maxTwoMMpolysInfiniteCarrier(mmp2);


        //MaxMinPolynomial mamipo = createAPoly(18);
        //System.out.println("\n" + mamipo.toString());
        /*
        MaxMinPolynomial lhsmmp = createAPoly(27);
        MaxMinPolynomial rhsmmp = createAPoly(28);
        System.out.println("MMP of lhs: " );
        lhsmmp.printMMpoly();
        System.out.println("MMP of rhs: " );
        rhsmmp.printMMpoly();
        LinkedList<LinkedList<VarPolynomial>> result = myMin(lhsmmp, rhsmmp);
        System.out.println("Result of minus operation :");
        System.out.println("Max {");
        boolean firstEntry1 = true;
        boolean firstEntry2 = true;
        for(LinkedList<VarPolynomial> mins : result) {
            if(firstEntry1) {
                System.out.print("min {");
                for(VarPolynomial vp : mins) {
                    if(firstEntry2) {
                        System.out.print(vp.toString());
                        firstEntry2 = false;
                    }
                    else {
                        System.out.print(", " + vp.toString());
                    }
                }
                System.out.println("}, ");
                firstEntry2 = true;
            }
            else {
                System.out.print(", min {");
                for(VarPolynomial vp : mins) {
                    if(firstEntry2) {
                        System.out.print(vp.toString());
                        firstEntry2 = false;
                    }
                    else {
                        System.out.print(", " + vp.toString());
                    }
                }
                System.out.println("}, ");
                firstEntry2 = true;
            }
        }
        System.out.println("}");
        */
        /*
        InterpretationStatus intStatus = ModelSearch.myCheck(
                lhsmmp.getAllMinSets(), rhsmmp.getAllMinSets());
        System.out.println("Interpretation Status: " + intStatus.toString());
        /*
        LinkedHashSet<Rule> auxSet = new LinkedHashSet<Rule>();
        auxSet.add(createARule(1));
        auxSet.add(createARule(2));
        auxSet.add(createARule(3));
        //auxSet.add(createARule(6));
        //auxSet.add(createARule(9));
        System.out.println("\nRules of the TRS : ");
        for(Rule rule : auxSet) {
            System.out.println(rule.toString());
        }
        System.out.println();
        for(int i=0; i<1 ; i++) {
            long start = System.nanoTime();
            SemLabProc proc = new SemLabProc();
            proc.pseudoMain(auxSet, -1);
            long end = System.nanoTime();
            System.out.println(((end-start)/1000));

        }




        /*
        Map<String, MaxMinPolynomial> arguMap = createSubstitutionMap(1);
        MaxMinPolynomial substPoly = mmPoly7.substituteVariables(arguMap);


        HashMap<FunctionSymbol, MaxMinPolynomial> substMap = new HashMap<FunctionSymbol, MaxMinPolynomial>();
        substMap.put(FunctionSymbol.create("f", 2), createAPoly(8));
        substMap.put(FunctionSymbol.create("g", 2), createAPoly(9));

        SemLabProc semLabProc = new SemLabProc();
        Rule dummyRule = createARule(7);
        Term t = dummyRule.getLeft();
        semLabProc.pseudoMain2(t, substMap);
        */
    }



    public void multiplyTwoMMpolys( final MaxMinPolynomial poly2 ) {

        MaxMinPolynomial poly3;
        System.out.println("\nthis:");
        this.printMMpoly();
        System.out.println("\nOther:");
        poly2.printMMpoly();
        poly3 = this.times(poly2);
        System.out.println("\nResult:");
        poly3.printMMpoly();
    }


    public void addTwoMMpolys( final MaxMinPolynomial poly2 ) {

        MaxMinPolynomial poly3;
        System.out.println("\nthis:");
        this.printMMpoly();
        System.out.println("\nOther:");
        poly2.printMMpoly();
        poly3 = this.plus(poly2);
        System.out.println("\nResult:");
        poly3.printMMpoly();

    }

    public void subtractTwoMMpolys( final MaxMinPolynomial poly2 ) {

        MaxMinPolynomial poly3;
        System.out.println("\nthis:");
        this.printMMpoly();
        System.out.println("\nOther:");
        poly2.printMMpoly();
        poly3 = this.monos(poly2);
        System.out.println("\nResult:");
        poly3.printMMpoly();
    }

    public void maxTwoMMpolys( final MaxMinPolynomial poly2 ) {

        MaxMinPolynomial poly3;
        System.out.println("\nthis:");
        this.printMMpoly();
        System.out.println("\nOther:");
        poly2.printMMpoly();
        poly3 = this.maximumFiniteCarrier(poly2);
        System.out.println("\nResult:");
        poly3.printMMpoly();
    }

public void maxTwoMMpolysInfiniteCarrier( final MaxMinPolynomial poly2 ) {

        MaxMinPolynomial poly3;
        System.out.println("\nthis:");
        this.printMMpoly();
        System.out.println("\nOther:");
        poly2.printMMpoly();
        poly3 = this.maximumInfiniteCarrier(poly2);
        System.out.println("\nResult:");
        poly3.printMMpoly();
    }

    public void minTwoMMpolys( final MaxMinPolynomial poly2 ) {

        MaxMinPolynomial poly3;
        System.out.println("\nthis:");
        this.printMMpoly();
        System.out.println("\nOther:");
        poly2.printMMpoly();
        poly3 = this.minimumFiniteCarrier(poly2);
        System.out.println("\nResult:");
        poly3.printMMpoly();
    }

    public void minTwoMMpolysInfiniteCarrier(final MaxMinPolynomial poly2) {
        MaxMinPolynomial poly3;
        System.out.println("\nthis:");
        this.printMMpoly();
        System.out.println("\nOther:");
        poly2.printMMpoly();
        poly3 = this.minimumInfiniteCarrier(poly2);
        System.out.println("\nResult:");
        poly3.printMMpoly();
    }

    public void printMMpoly() {
        System.out.println(this.toString());
    }

    public String export (final Export_Util eu) {
        final boolean slimOutput = true;
        final StringBuilder buffer = new StringBuilder();
        if(slimOutput) {
            switch (this.metaInf) {
            case Constant : {
                buffer.append(this.getVarPolynomial().toString());
                return buffer.toString();
            }
            case VarPoly : {
                buffer.append(this.getVarPolynomial().toString());
                return buffer.toString();
            }
            case MinInterpretation : {
                buffer.append("min");
                buffer.append(eu.set(this.getAllMinSets(), 0));
                return buffer.toString();
            }
            case MaxInterpretation : {
                buffer.append("max");
                final LinkedHashSet<String> minSetsToString = new LinkedHashSet<String>();
                for(final ImmutableSet<VarPolynomial> mins : this.maxMinPoly) {
                    final StringBuilder auxBuffer = new StringBuilder();
                    auxBuffer.append("min");
                    auxBuffer.append(eu.set(mins, 0));
                    minSetsToString.add(auxBuffer.toString());
                }
                buffer.append(eu.set(minSetsToString, 0));
                return buffer.toString();
            }
            default : {
                throw new RuntimeException("Enum MMPolyMetaInf has been modified!");
            }
            }

        }
        else {
            buffer.append("max");
            final LinkedHashSet<String> minSetsToString = new LinkedHashSet<String>();
            for(final ImmutableSet<VarPolynomial> mins : this.maxMinPoly) {
                final StringBuilder auxBuffer = new StringBuilder();
                auxBuffer.append("min");
                auxBuffer.append(eu.set(mins, 0));
                minSetsToString.add(auxBuffer.toString());
            }
            buffer.append(eu.set(minSetsToString, 0));
            return buffer.toString();
        }
    }


    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    public String toHTML() {
        return this.export(new HTML_Util());
    }

    public static Rule createARule (final int i) {
        final ArrayList<TRSTerm>  argsArray0 = new ArrayList<TRSTerm>(1);
        final ArrayList<TRSTerm>  argsArray1 = new ArrayList<TRSTerm>(1);
        final ArrayList<TRSTerm>  argsArray4 = new ArrayList<TRSTerm>(1);
        final ArrayList<TRSTerm>  argsArray5 = new ArrayList<TRSTerm>(2);
        final ArrayList<TRSTerm>  argsArray6 = new ArrayList<TRSTerm>(2);
        final ArrayList<TRSTerm>  argsArray7 = new ArrayList<TRSTerm>(2);
        final ArrayList<TRSTerm>  argsArray8 = new ArrayList<TRSTerm>(2);
        final ArrayList<TRSTerm>  argsArray9 = new ArrayList<TRSTerm>(0);

        argsArray0.add(TRSTerm.createVariable("x"));


        switch(i) {
        case(1) : {
            final TRSFunctionApplication b = TRSTerm.createFunctionApplication(FunctionSymbol.create("b", 0), ImmutableCreator.create(argsArray9));
            argsArray5.add(b);
            argsArray5.add(TRSTerm.createVariable("x"));
            final TRSFunctionApplication a = TRSTerm.createFunctionApplication(FunctionSymbol.create("a", 2), ImmutableCreator.create(argsArray5));
            return Rule.create(a, b);

        }
        case(2) : {
            final TRSFunctionApplication c = TRSTerm.createFunctionApplication(FunctionSymbol.create("c", 0), ImmutableCreator.create(argsArray9));
            argsArray5.add(TRSTerm.createVariable("x"));
            argsArray5.add(c);
            final TRSFunctionApplication a = TRSTerm.createFunctionApplication(FunctionSymbol.create("a", 2), ImmutableCreator.create(argsArray5));
            return Rule.create(a, TRSTerm.createVariable("x"));
        }

        case(3) : {
            final TRSFunctionApplication c = TRSTerm.createFunctionApplication(FunctionSymbol.create("c", 0), ImmutableCreator.create(argsArray9));
            argsArray5.add(c);
            argsArray5.add(TRSTerm.createVariable("x"));
            final TRSFunctionApplication aL = TRSTerm.createFunctionApplication(FunctionSymbol.create("a", 2), ImmutableCreator.create(argsArray5));

            final TRSFunctionApplication b = TRSTerm.createFunctionApplication(FunctionSymbol.create("b", 0), ImmutableCreator.create(argsArray9));
            argsArray8.add(b);
            argsArray8.add(TRSTerm.createVariable("x"));
            final TRSFunctionApplication aR = TRSTerm.createFunctionApplication(FunctionSymbol.create("a", 2), ImmutableCreator.create(argsArray8));
            return Rule.create(aL, aR);

        }
        case(4) : {
            final TRSFunctionApplication mySucc1 = TRSTerm.createFunctionApplication(FunctionSymbol.create("succ", 1), ImmutableCreator.create(argsArray0));
            argsArray8.add(mySucc1);
            argsArray8.add(TRSTerm.createVariable("y"));
            final TRSFunctionApplication myTimes1 = TRSTerm.createFunctionApplication(FunctionSymbol.create("times", 2), ImmutableCreator.create(argsArray8));
            argsArray1.add(TRSTerm.createVariable("x"));
                // FunctionApplication myTimes0 = Term.createFunctionApplication(FunctionSymbol.create("times", 1), ImmutableCreator.create(argsArray1));
                // argsArray5.add(myTimes0);
            argsArray5.add(TRSTerm.createVariable("x"));
            argsArray5.add(TRSTerm.createVariable("y"));
            final TRSFunctionApplication myTimes2 = TRSTerm.createFunctionApplication(FunctionSymbol.create("times", 2), ImmutableCreator.create(argsArray5));
            argsArray4.add(mySucc1);
            argsArray4.add(myTimes2);
            final TRSFunctionApplication myPlus1 = TRSTerm.createFunctionApplication(FunctionSymbol.create("plus", 2), ImmutableCreator.create(argsArray4));
            return Rule.create(myTimes1, myPlus1);
        }
        case(5) : {
            final TRSFunctionApplication mySucc1 = TRSTerm.createFunctionApplication(FunctionSymbol.create("succ", 1), ImmutableCreator.create(argsArray1));
            final TRSFunctionApplication mySucc2 = TRSTerm.createFunctionApplication(FunctionSymbol.create("succ", 1), ImmutableCreator.create(argsArray1));
            return Rule.create(mySucc1, mySucc2);
        }

        case 6 : {
            argsArray8.add(TRSTerm.createVariable("z1"));
            argsArray8.add(TRSTerm.createVariable("z2"));
            final TRSFunctionApplication g = TRSTerm.createFunctionApplication(FunctionSymbol.create("g", 2), ImmutableCreator.create(argsArray8));
            argsArray7.add(g);
            argsArray7.add(TRSTerm.createVariable("z3"));
            final TRSFunctionApplication f = TRSTerm.createFunctionApplication(FunctionSymbol.create("f", 2), ImmutableCreator.create(argsArray7));
            return Rule.create(f, TRSTerm.createVariable("z1"));

        }

        case 7 : {
            argsArray5.add(TRSTerm.createVariable("x"));
            argsArray5.add(TRSTerm.createVariable("y"));
            final TRSFunctionApplication g = TRSTerm.createFunctionApplication(FunctionSymbol.create("g", 2), ImmutableCreator.create(argsArray5));
            return Rule.create(g, TRSTerm.createVariable("x"));
        }

        case 8 : {
            argsArray5.add(TRSTerm.createVariable("x"));
            argsArray5.add(TRSTerm.createVariable("y"));
            final TRSFunctionApplication g = TRSTerm.createFunctionApplication(FunctionSymbol.create("g", 2), ImmutableCreator.create(argsArray5));
            return Rule.create(g, TRSTerm.createVariable("y"));
        }

        case 9 : {
            argsArray5.add(TRSTerm.createVariable("x"));
            argsArray5.add(TRSTerm.createVariable("y"));
            final TRSFunctionApplication g = TRSTerm.createFunctionApplication(FunctionSymbol.create("g", 2), ImmutableCreator.create(argsArray5));
            argsArray6.add(g);
            argsArray6.add(TRSTerm.createVariable("z"));
            final TRSFunctionApplication f = TRSTerm.createFunctionApplication(FunctionSymbol.create("f", 2), ImmutableCreator.create(argsArray6));
            argsArray7.add(TRSTerm.createVariable("x"));
            argsArray7.add(TRSTerm.createVariable("z"));
            final TRSFunctionApplication g2 = TRSTerm.createFunctionApplication(FunctionSymbol.create("g", 2), ImmutableCreator.create(argsArray7));
            return Rule.create(f, g2);
        }

        case 10 : {
            argsArray5.add(TRSTerm.createVariable("x"));
            argsArray5.add(TRSTerm.createVariable("y"));
            final TRSFunctionApplication g = TRSTerm.createFunctionApplication(FunctionSymbol.create("g", 2), ImmutableCreator.create(argsArray5));
            argsArray6.add(g);
            argsArray6.add(TRSTerm.createVariable("z"));
            final TRSFunctionApplication f = TRSTerm.createFunctionApplication(FunctionSymbol.create("f", 2), ImmutableCreator.create(argsArray6));
            return Rule.create(f, g);

        }

        default : {
            return null;
        }
        }

    }


    private static MaxMinPolynomial createAPoly (final int i){
        final Set<Set<VarPolynomial>> pol1= new LinkedHashSet<Set<VarPolynomial>>();
        final Set<Set<VarPolynomial>> pol2 = new LinkedHashSet<Set<VarPolynomial>>();

        final Set<VarPolynomial> auxmins1 = new LinkedHashSet<VarPolynomial>();
        final Set<VarPolynomial> auxmins2 = new LinkedHashSet<VarPolynomial>();
        final Set<VarPolynomial> auxmins3 = new LinkedHashSet<VarPolynomial>();

        VarPolynomial varpol1;
        VarPolynomial varpol2;


        switch(i) {
        case(1) : {
            varpol1 = VarPolynomial.createVariable("a");
            auxmins1.add(varpol1);

            varpol1 = VarPolynomial.createVariable("b");
            auxmins1.add(varpol1);

            varpol1 = VarPolynomial.createVariable("c");
            auxmins2.add(varpol1);

            varpol1 = VarPolynomial.createVariable("d");
            auxmins2.add(varpol1);

            varpol1 = VarPolynomial.createVariable("e");
            auxmins3.add(varpol1);

            varpol1 = VarPolynomial.createVariable("f");
            auxmins3.add(varpol1);

            pol1.add(auxmins1);
            pol1.add(auxmins2);
            pol1.add(auxmins3);
            return MaxMinPolynomial.create(pol1);
        }

        case(2) : {
            varpol1 = VarPolynomial.createVariable("u");
            auxmins1.add(varpol1);

            varpol1 = VarPolynomial.createVariable("v");
            auxmins1.add(varpol1);

            varpol1 = VarPolynomial.createVariable("w");
            auxmins2.add(varpol1);

            varpol1 = VarPolynomial.createVariable("x");
            auxmins2.add(varpol1);

            varpol1 = VarPolynomial.createVariable("y");
            auxmins3.add(varpol1);

            varpol1 = VarPolynomial.createVariable("z");
            auxmins3.add(varpol1);

            pol2.add(auxmins1);
            pol2.add(auxmins2);
            pol2.add(auxmins3);
            return MaxMinPolynomial.create(pol2);
        }

        case(3) : {
            varpol1 = VarPolynomial.createVariable("x");
            varpol2 = VarPolynomial.create(SimplePolynomial.create(3));
            auxmins1.add(varpol1.plus(varpol2));

            varpol1 = VarPolynomial.createVariable("y");
            varpol2 = VarPolynomial.create(SimplePolynomial.create(1));
            auxmins1.add(varpol1.plus(varpol2));

            varpol1 = VarPolynomial.createVariable("u");
            varpol2 = VarPolynomial.create(SimplePolynomial.create(2));
            auxmins2.add(varpol1.plus(varpol2));

            varpol1 = VarPolynomial.createVariable("v");
            varpol2 = VarPolynomial.create(SimplePolynomial.create(4));
            auxmins2.add(varpol1.plus(varpol2));

            pol1.add(auxmins1);
            pol1.add(auxmins2);
            return MaxMinPolynomial.create(pol1);
        }

        case(4) : {
            varpol1 = VarPolynomial.createVariable("x");
            varpol2 = VarPolynomial.create(SimplePolynomial.create(3));
            auxmins1.add(varpol1.plus(varpol2));

            varpol1 = VarPolynomial.createVariable("y");
            varpol2 = VarPolynomial.create(SimplePolynomial.create(1));
            auxmins1.add(varpol1.plus(varpol2));

            varpol1 = VarPolynomial.createVariable("c");
            varpol2 = VarPolynomial.create(SimplePolynomial.create(5));
            auxmins2.add(varpol1.plus(varpol2));

            varpol1 = VarPolynomial.createVariable("d");
            varpol2 = VarPolynomial.create(SimplePolynomial.create(7));
            auxmins2.add(varpol1.plus(varpol2));

            pol2.add(auxmins1);
            pol2.add(auxmins2);
            return MaxMinPolynomial.create(pol2);
        }

        case(5) : {
            return MaxMinPolynomial.ONE;
        }

        case(6) : {
            varpol1 = VarPolynomial.createVariable("a");
            auxmins1.add(varpol1);

            varpol1 = VarPolynomial.createVariable("b");
            auxmins1.add(varpol1);

            varpol1 = VarPolynomial.createVariable("c");
            auxmins2.add(varpol1);

            varpol1 = VarPolynomial.createVariable("d");
            auxmins2.add(varpol1);

            varpol1 = VarPolynomial.createVariable("e");
            auxmins3.add(varpol1);

            varpol1 = VarPolynomial.createVariable("f");
            auxmins3.add(varpol1);

            pol1.add(auxmins1);
            pol1.add(auxmins2);
            pol1.add(auxmins3);
            return MaxMinPolynomial.create(pol1);
        }

        case(7) : {
            varpol1 = VarPolynomial.createVariable("x");
            varpol1 = varpol1.times(SimplePolynomial.create(2));
            varpol1 = varpol1.plus(VarPolynomial.createVariable("y"));
            auxmins1.add(varpol1);

            varpol2 = VarPolynomial.createVariable("y");
            varpol2 = varpol2.times(SimplePolynomial.create(3));

            //varpol2 = varpol2.plus(VarPolynomial.createVariable("x"));


            varpol1 = VarPolynomial.createVariable("x");
            varpol1 = varpol1.times(varpol1);
            varpol1 = varpol1.times(varpol1);
            varpol2 = varpol2.plus(varpol1);

            auxmins1.add(varpol2);
            pol1.add(auxmins1);
            return MaxMinPolynomial.create(pol1);

        }

        case 8 : { // {x}, {y}
            varpol1 = VarPolynomial.createVariable("x");
            varpol2 = VarPolynomial.createVariable("y");
            auxmins1.add(varpol1);
            auxmins2.add(varpol2);
            pol1.add(auxmins1);
            pol1.add(auxmins2);
            return MaxMinPolynomial.create(pol1);
        }

        case 9 : {  // 2x + y
            varpol1 = VarPolynomial.createVariable("x");
            varpol1 = varpol1.times(SimplePolynomial.create(2));
            varpol1 = varpol1.plus(VarPolynomial.createVariable("y"));
            auxmins1.add(varpol1);
            pol1.add(auxmins1);
            return MaxMinPolynomial.create(pol1);
        }

        case 10 : { // 2y + x
            varpol1 = VarPolynomial.createVariable("y");
            varpol1 = varpol1.times(SimplePolynomial.create(2));
            varpol1 = varpol1.plus(VarPolynomial.createVariable("x"));
            auxmins1.add(varpol1);
            pol1.add(auxmins1);
            return MaxMinPolynomial.create(pol1);

        }

        case 11 : { // x + y
            varpol1 = VarPolynomial.createVariable("x");
            varpol1 = varpol1.plus(VarPolynomial.createVariable("y"));
            auxmins1.add(varpol1);
            pol1.add(auxmins1);
            return MaxMinPolynomial.create(pol1);
        }

        case 12 : { // {5u + 2v , 3x + 4y}
            varpol1 = VarPolynomial.createVariable("u");
            varpol1 = varpol1.times(SimplePolynomial.create(5));
            varpol2 = VarPolynomial.createVariable("v");
            varpol2 = varpol2.times(SimplePolynomial.create(2));
            varpol1 = varpol1.plus(varpol2);
            auxmins1.add(varpol1);

            varpol1 = VarPolynomial.createVariable("x");
            varpol1 = varpol1.times(SimplePolynomial.create(3));
            varpol2 = VarPolynomial.createVariable("y");
            varpol2 = varpol2.times(SimplePolynomial.create(4));
            varpol1 = varpol1.plus(varpol2);
            auxmins1.add(varpol1);
            pol1.add(auxmins1);
            return MaxMinPolynomial.create(pol1);
        }

        case 13 : { // {4u + v ,  5x + 6y}
            varpol1 = VarPolynomial.createVariable("u");
            varpol1 = varpol1.times(SimplePolynomial.create(4));
            varpol2 = VarPolynomial.createVariable("v");
            varpol2 = varpol2.times(SimplePolynomial.create(1));
            varpol1 = varpol1.plus(varpol2);
            auxmins1.add(varpol1);

            varpol1 = VarPolynomial.createVariable("x");
            varpol1 = varpol1.times(SimplePolynomial.create(5));
            varpol2 = VarPolynomial.createVariable("y");
            varpol2 = varpol2.times(SimplePolynomial.create(6));
            varpol1 = varpol1.plus(varpol2);
            auxmins1.add(varpol1);
            pol1.add(auxmins1);
            return MaxMinPolynomial.create(pol1);

        }

        case 14 : { // {5u + v , 2x + 2y, z}
            varpol1 = VarPolynomial.createVariable("u");
            varpol1 = varpol1.times(SimplePolynomial.create(5));
            varpol2 = VarPolynomial.createVariable("v");
            varpol2 = varpol2.times(SimplePolynomial.create(1));
            varpol1 = varpol1.plus(varpol2);
            auxmins1.add(varpol1);

            varpol1 = VarPolynomial.createVariable("x");
            varpol1 = varpol1.times(SimplePolynomial.create(2));
            varpol2 = VarPolynomial.createVariable("y");
            varpol2 = varpol2.times(SimplePolynomial.create(2));
            varpol1 = varpol1.plus(varpol2);
            auxmins1.add(varpol1);

            varpol1 = VarPolynomial.createVariable("z");
            auxmins1.add(varpol1);

            pol1.add(auxmins1);
            return MaxMinPolynomial.create(pol1);

        }

        case 15 : { // {4u + 3v , 3x + 4y}
            varpol1 = VarPolynomial.createVariable("u");
            varpol1 = varpol1.times(SimplePolynomial.create(4));
            varpol2 = VarPolynomial.createVariable("v");
            varpol2 = varpol2.times(SimplePolynomial.create(3));
            varpol1 = varpol1.plus(varpol2);
            auxmins1.add(varpol1);

            varpol1 = VarPolynomial.createVariable("x");
            varpol1 = varpol1.times(SimplePolynomial.create(3));
            varpol2 = VarPolynomial.createVariable("y");
            varpol2 = varpol2.times(SimplePolynomial.create(4));
            varpol1 = varpol1.plus(varpol2);
            auxmins1.add(varpol1);
            pol1.add(auxmins1);
            return MaxMinPolynomial.create(pol1);

        }

        case 16 : { // {xy}
            varpol1 = VarPolynomial.createVariable("x");
            varpol2 = VarPolynomial.createVariable("y");
            varpol1 = varpol1.times(varpol2);
            auxmins1.add(varpol1);
            pol1.add(auxmins1);
            return MaxMinPolynomial.create(pol1);
        }
        case 17 : { // {2xy}
            varpol1 = VarPolynomial.createVariable("x");
            varpol2 = VarPolynomial.createVariable("y");
            varpol1 = varpol1.times(varpol2);
            varpol1 = varpol1.times(SimplePolynomial.create(2));
            auxmins1.add(varpol1);
            pol1.add(auxmins1);
            return MaxMinPolynomial.create(pol1);

        }

        case 18 : {//  {{4x, 2y}, {6s, 7t}}
            varpol1 = VarPolynomial.createVariable("x");
            varpol1 = varpol1.times(SimplePolynomial.create(4));
            varpol2 = VarPolynomial.createVariable("y");
            varpol2 = varpol2.times(SimplePolynomial.create(2));
            auxmins1.add(varpol1);
            auxmins1.add(varpol2);

            varpol1 = VarPolynomial.createVariable("s");
            varpol1 = varpol1.times(SimplePolynomial.create(6));
            varpol2 = VarPolynomial.createVariable("t");
            varpol2 = varpol2.times(SimplePolynomial.create(7));
            auxmins2.add(varpol1);
            auxmins2.add(varpol2);

            pol1.add(auxmins1);
            pol1.add(auxmins2);

            return MaxMinPolynomial.create(pol1);
        }

        case 19 : {//  {{6x, 3y}, {8u, 9v}}
            varpol1 = VarPolynomial.createVariable("x");
            varpol1 = varpol1.times(SimplePolynomial.create(6));
            varpol2 = VarPolynomial.createVariable("y");
            varpol2 = varpol2.times(SimplePolynomial.create(3));
            auxmins1.add(varpol1);
            auxmins1.add(varpol2);

            varpol1 = VarPolynomial.createVariable("u");
            varpol1 = varpol1.times(SimplePolynomial.create(8));
            varpol2 = VarPolynomial.createVariable("v");
            varpol2 = varpol2.times(SimplePolynomial.create(9));
            auxmins2.add(varpol1);
            auxmins2.add(varpol2);

            pol1.add(auxmins1);
            pol1.add(auxmins2);

            return MaxMinPolynomial.create(pol1);
        }

        case 20 : {//  {{6x, 3y}, {8s, 9t}}
            varpol1 = VarPolynomial.createVariable("x");
            varpol1 = varpol1.times(SimplePolynomial.create(6));
            varpol2 = VarPolynomial.createVariable("y");
            varpol2 = varpol2.times(SimplePolynomial.create(3));
            auxmins1.add(varpol1);
            auxmins1.add(varpol2);

            varpol1 = VarPolynomial.createVariable("s");
            varpol1 = varpol1.times(SimplePolynomial.create(8));
            varpol2 = VarPolynomial.createVariable("t");
            varpol2 = varpol2.times(SimplePolynomial.create(9));
            auxmins2.add(varpol1);
            auxmins2.add(varpol2);

            pol1.add(auxmins1);
            pol1.add(auxmins2);

            return MaxMinPolynomial.create(pol1);
        }

        case 21 : {// {{5x, 4y}, {8s, 9t}}
            varpol1 = VarPolynomial.createVariable("x");
            varpol1 = varpol1.times(SimplePolynomial.create(5));
            varpol2 = VarPolynomial.createVariable("y");
            varpol2 = varpol2.times(SimplePolynomial.create(4));
            auxmins1.add(varpol1);
            auxmins1.add(varpol2);

            varpol1 = VarPolynomial.createVariable("s");
            varpol1 = varpol1.times(SimplePolynomial.create(8));
            varpol2 = VarPolynomial.createVariable("t");
            varpol2 = varpol2.times(SimplePolynomial.create(9));
            auxmins2.add(varpol1);
            auxmins2.add(varpol2);

            pol1.add(auxmins1);
            pol1.add(auxmins2);

            return MaxMinPolynomial.create(pol1);
        }

        case 22 : {// {{5x, 4y}, {8u, 9v}}
            varpol1 = VarPolynomial.createVariable("x");
            varpol1 = varpol1.times(SimplePolynomial.create(5));
            varpol2 = VarPolynomial.createVariable("y");
            varpol2 = varpol2.times(SimplePolynomial.create(4));
            auxmins1.add(varpol1);
            auxmins1.add(varpol2);

            varpol1 = VarPolynomial.createVariable("u");
            varpol1 = varpol1.times(SimplePolynomial.create(8));
            varpol2 = VarPolynomial.createVariable("v");
            varpol2 = varpol2.times(SimplePolynomial.create(9));
            auxmins2.add(varpol1);
            auxmins2.add(varpol2);

            pol1.add(auxmins1);
            pol1.add(auxmins2);

            return MaxMinPolynomial.create(pol1);
        }

        case(23) : { // {{x}, {y}, {z}}
            varpol1 = VarPolynomial.createVariable("x");
            auxmins1.add(varpol1);

            varpol1 = VarPolynomial.createVariable("y");
            auxmins2.add(varpol1);

            varpol1 = VarPolynomial.createVariable("z");
            auxmins3.add(varpol1);

            pol1.add(auxmins1);
            pol1.add(auxmins2);
            pol1.add(auxmins3);
            return MaxMinPolynomial.create(pol1);
        }

        case(24) : { // {{x}, {y}}
            varpol1 = VarPolynomial.createVariable("x");
            auxmins1.add(varpol1);

            varpol1 = VarPolynomial.createVariable("y");
            auxmins2.add(varpol1);

            pol1.add(auxmins1);
            pol1.add(auxmins2);
            return MaxMinPolynomial.create(pol1);
        }
        case 25 : { // {{4, 6}, {2,10}}
            varpol1 = VarPolynomial.create(4);
            auxmins1.add(varpol1);
            varpol1 = VarPolynomial.create(6);
            auxmins1.add(varpol1);

            varpol1 = VarPolynomial.create(2);
            auxmins2.add(varpol1);
            varpol1 = VarPolynomial.create(10);
            auxmins2.add(varpol1);

            pol1.add(auxmins1);
            pol1.add(auxmins2);
            return MaxMinPolynomial.create(pol1);
        }
        case 26 : { // {{3, 5}, {7, 9}}
            varpol1 = VarPolynomial.create(3);
            auxmins1.add(varpol1);
            varpol1 = VarPolynomial.create(5);
            auxmins1.add(varpol1);

            varpol1 = VarPolynomial.create(7);
            auxmins2.add(varpol1);
            varpol1 = VarPolynomial.create(9);
            auxmins2.add(varpol1);

            pol1.add(auxmins1);
            pol1.add(auxmins2);
            return MaxMinPolynomial.create(pol1);

        }

        case 27 : { // {{a, b}, {c, d}}
            varpol1 = VarPolynomial.createVariable("a");
            auxmins1.add(varpol1);
            varpol1 = VarPolynomial.createVariable("b");
            auxmins1.add(varpol1);

            varpol1 = VarPolynomial.createVariable("c");
            auxmins2.add(varpol1);
            varpol1 = VarPolynomial.createVariable("d");
            auxmins2.add(varpol1);

            pol1.add(auxmins1);
            pol1.add(auxmins2);
            return MaxMinPolynomial.create(pol1);
        }
        case 28 : { // {{e, f}, {g, h}}
            varpol1 = VarPolynomial.createVariable("e");
            auxmins1.add(varpol1);
            varpol1 = VarPolynomial.createVariable("f");
            auxmins1.add(varpol1);

            varpol1 = VarPolynomial.createVariable("g");
            auxmins2.add(varpol1);
            varpol1 = VarPolynomial.createVariable("h");
            auxmins2.add(varpol1);
            pol1.add(auxmins1);
            pol1.add(auxmins2);
            return MaxMinPolynomial.create(pol1);
        }
        case 29 : { // 2xyz
            varpol1 = VarPolynomial.createVariable("x");
            varpol2 = VarPolynomial.createVariable("y");
            final VarPolynomial varpol3 = VarPolynomial.createVariable("z");
            varpol1 = varpol1.times(varpol2);
            varpol1 = varpol1.times(varpol3);
            varpol1 = varpol1.times(SimplePolynomial.create(2));
            auxmins1.add(varpol1);
            pol1.add(auxmins1);
            return MaxMinPolynomial.create(pol1);
        }
        case 30 : { // 2vwxyz
            varpol1 = VarPolynomial.createVariable("v");
            varpol2 = VarPolynomial.createVariable("w");
            final VarPolynomial varpol3 = VarPolynomial.createVariable("x");
            final VarPolynomial varpol4 = VarPolynomial.createVariable("y");
            final VarPolynomial varpol5 = VarPolynomial.createVariable("z");
            varpol1 = varpol1.times(varpol2);
            varpol1 = varpol1.times(varpol3);
            varpol1 = varpol1.times(varpol4);
            varpol1 = varpol1.times(varpol5);
            varpol1 = varpol1.times(SimplePolynomial.create(2));
            auxmins1.add(varpol1);
            pol1.add(auxmins1);
            return MaxMinPolynomial.create(pol1);
        }

        default : {
            return MaxMinPolynomial.ZERO;
        }
        }
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        throw new UnsupportedOperationException("Not yet implemented!");
    }

}
