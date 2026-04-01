/*
 * Created on 18.03.2005
 */
package aprove.verification.dpframework.BasicStructures.AFSPrecalculation;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A Partially evaluated variable list (set) (PEVL) is like a PEP,
 * but it only considers variables, not full polynomials. It is
 * used for a combined check of a set of PEVL-constraints whether they
 * are satisfiable. This is done by incrementally (de)activating positions
 * until we find a contradiction or can not conclude
 * anything further.
 *
 * (This check may also be used for AFSSolver, as we do nothing but
 *  to check which (non-collapsing) filterings are possible.
 *
 * @author thiemann
 */
public class YnmPEVL {

    private final static YNM YES = YNM.YES;
    private final static YNM NO = YNM.NO;
    private final static YNM MAYBE = YNM.MAYBE;


    /*
     * real values
     */
    private final FunctionSymbol f; // the top most symbol, if non-null
    private final ArrayList<YnmPEVL> args; // the arguments PEVLs
    private final boolean leftMode;  // see uncertainVarMap
    private final Set<String> certainVars; // the vars that must occur in this PEVL

    /*
     * calculated values
     */
    private final Map<String, Set<Pair<FunctionSymbol, Integer>>> uncertainVarMap;
      // a mapping from variables that may occur to a set of positions
      // in left mode these are the positions that must be regarded to get this variables
      // and in right mode these are the positions that must be disregarded to not get this variable
    private final Set<FunctionSymbol> missInter; // the top-most interpretation that are missing
                    // to get an empty uncertainVarMap (and hence a fully specified set of certain vars)


    private YnmPEVL(FunctionSymbol f,
            ArrayList<YnmPEVL> args,
            boolean leftMode,
            Set<String> certainVars,
            Map<String, Set<Pair<FunctionSymbol, Integer>>> uncertainVarMap) {
        this.f = f;
        this.leftMode = leftMode;
        this.certainVars = certainVars;
        this.uncertainVarMap = uncertainVarMap;
        this.missInter = new LinkedHashSet<FunctionSymbol>();
        if (f != null) {
            this.missInter.add(f);
        }
        if (args != null) {
            if (f == null) {
                for (YnmPEVL arg : args) {
                    this.missInter.addAll(arg.missInter);
                }
            }
//            if (f == null) {
//                // flattening!
//                List<YnmPEVL> newArgs = new LinkedList<YnmPEVL>();
//                for (YnmPEVL arg : args) {
//                    if (arg.args != null && arg.f == null) {
//                        for (YnmPEVL subArg : arg.args) {
//                            newArgs.add(subArg);
//                        }
//                    } else {
//                        newArgs.add(arg);
//                    }
//                }
//                args = new YnmPEVL[newArgs.size()];
//                int i = 0;
//                for (YnmPEVL newArg : newArgs) {
//                    args[i] = newArg;
//                    i++;
//                }
//            }
        }

        this.args = args;
    }


    private static final YnmPEVL NULL = new YnmPEVL(null, new ArrayList<YnmPEVL>(0), true, new LinkedHashSet<String>(), new LinkedHashMap<String, Set<Pair<FunctionSymbol, Integer>>>());

    /**
     * creates unevaluated PEVL for the given term in the given mode
     */
    public static YnmPEVL create(TRSTerm t, boolean leftMode) {
        // setup needed datastructures for result
        FunctionSymbol f;
        Set<String> certainVars = new LinkedHashSet<String>();
        ArrayList<YnmPEVL> pevlArgs;
        Map<String, Set<Pair<FunctionSymbol, Integer>>> uncertainVarMap =
            new LinkedHashMap<String, Set<Pair<FunctionSymbol, Integer>>>();

        // and fill these values
        if (t.isVariable()) {
            f = null;
            pevlArgs = new ArrayList<YnmPEVL>(0);
            certainVars.add(((TRSVariable) t).getName());
        } else {
            TRSFunctionApplication fTerm = (TRSFunctionApplication) t;
            f = fTerm.getRootSymbol();
            List<? extends TRSTerm> args = fTerm.getArguments();
            pevlArgs = new ArrayList<YnmPEVL>(f.getArity());

            // deal with arguments
            int i = 0;
            Pair<FunctionSymbol, Integer> pair;
            YnmPEVL pevlArg;
            for (TRSTerm arg : args) {
                pevlArg = YnmPEVL.create(arg, leftMode);
                pevlArgs.add(pevlArg);
                if (pevlArg != YnmPEVL.NULL) { // there are variables in this subterm
                    // merge certain vars of the argument
                    pair = new Pair<FunctionSymbol, Integer>(f, i);
                    YnmPEVL.mergeCertainIntoVarMap(uncertainVarMap, pevlArg.certainVars, certainVars, pair, leftMode);

                    // and the uncertain vars of the argument
                    YnmPEVL.mergeVarMaps(uncertainVarMap, pevlArg.uncertainVarMap, certainVars, pair, leftMode);
                }
                i++;
            }

            // and see whether we have some variables
            if (uncertainVarMap.isEmpty()) {
                return YnmPEVL.NULL;
            }
        }

        return new YnmPEVL(f, pevlArgs, leftMode, certainVars, uncertainVarMap);
    }


    public Pair<Set<FunctionSymbol>, YnmPEVL> getMissingInterpretationAndSimplifiedPevl(Map<FunctionSymbol, YNM[]> interpretation) {
        YnmPEVL pevl = this.specialize(null, new LinkedHashSet<String>(), interpretation, false);
        return new Pair<Set<FunctionSymbol>, YnmPEVL>(pevl.missInter, pevl);
    }

    public boolean isFullySpecified() {
        return this.uncertainVarMap.isEmpty();
    }

    public YnmPEVL specialize(Set<FunctionSymbol> fs, Map<FunctionSymbol, YNM[]> interpretation) {
        return this.specialize(fs, new LinkedHashSet<String>(), interpretation, false);
    }


    private YnmPEVL specialize(Set<FunctionSymbol> fs, Set<String> certainVars, Map<FunctionSymbol, YNM[]> interpretation, boolean certainMode) {
        // first determine whether we need to specialize ourselves!
        boolean needSpecialization = false;

        if (fs != null) {
            needSpecialization = false;
            for (String var : this.uncertainVarMap.keySet()) {
                if (!certainVars.contains(var)) {
                    needSpecialization = true;
                    break;
                }
            }
            if (needSpecialization) {
                needSpecialization = false;
                for (FunctionSymbol g : this.missInter) {
                    if (fs.contains(g)) {
                        needSpecialization = true;
                        break;
                    }
                }
            }
        } else {
            needSpecialization = true;
        }

        if (needSpecialization) {
            boolean haveF = this.f != null;
            YNM[] inter;
            if (haveF) {
                inter = interpretation.get(this.f);
                if (inter == null) {
                    int m = this.f.getArity();
                    inter = new YNM[m];
                    for (int i=0; i<m; i++) {
                        inter[i] = YnmPEVL.MAYBE;
                    }
                    interpretation.put(this.f, inter);
                }
            } else {
                inter = null;
            }

            Set<String> oldCertainVars = null;
            if (!certainMode) {
                // create a copy
                oldCertainVars = certainVars;
                certainVars = new LinkedHashSet<String>(certainVars);
            }


            // first add my own certainVars
            certainVars.addAll(this.certainVars);


            // next add certain vars from YES-args
            // and specialize YES-args
            int n = this.args.size();
            YnmPEVL[] specArgs = new YnmPEVL[n];
            int i = 0;
            int j = 0;
            for (YnmPEVL arg : this.args) {

                YNM interState = haveF ? inter[i] : YnmPEVL.YES;

                // calculate new Arg
                if (arg != YnmPEVL.NULL) {
                    if (interState == YnmPEVL.YES) {
                        arg = arg.specialize(fs, certainVars, interpretation, true);
                        certainVars.addAll(arg.certainVars);
                    } else if (interState == YnmPEVL.NO) {
                        arg = YnmPEVL.NULL;
                    }
                }

                if (arg != YnmPEVL.NULL) {
                    j++;
                }

                specArgs[i] = arg;
                i++;
            }

            // now we have all YES args in specialized form,
            // and we know the exact set of certain vars!!

            // let us now calculate the uncertainVarMap

            Map<String, Set<Pair<FunctionSymbol, Integer>>> newUncertainVarMap =
                new LinkedHashMap<String, Set<Pair<FunctionSymbol, Integer>>>();
            ArrayList<YnmPEVL> newArgs = new ArrayList<YnmPEVL>(haveF ? n : j);
            boolean haveMaybe = false;
            for (i=0; i<n; i++) {

                YnmPEVL arg = specArgs[i];

                boolean maybeArg;
                // specialize args for maybe
                if (arg != YnmPEVL.NULL && haveF && inter[i] == YnmPEVL.MAYBE) {
                    maybeArg = true;
                    arg = arg.specialize(fs, certainVars, interpretation, false);
                } else {
                    maybeArg = false;
                }

                if (arg != YnmPEVL.NULL) {
                    Pair<FunctionSymbol, Integer> pair;
                    if (maybeArg) {
                        haveMaybe = true;
                        pair = new Pair<FunctionSymbol, Integer>(this.f, i);
                        YnmPEVL.mergeCertainIntoVarMap(newUncertainVarMap, arg.certainVars, certainVars, pair, this.leftMode);
                    } else {
                        pair = null;
                    }

                    YnmPEVL.mergeVarMaps(newUncertainVarMap, arg.uncertainVarMap, certainVars, pair, this.leftMode);
                }

                // and store argument
                if (haveF || arg != YnmPEVL.NULL) {
                    newArgs.add(arg);
                }
            }

            // calculate new certain vars
            Set<String> newCertainVars;
            if (certainMode) {
                // in certain mode the certain vars are already
                // stored in the paramter certain vars!
                // so here we have the empty set
                newCertainVars = new LinkedHashSet<String>();
            } else {
                // all certain vars are in certain vars
                // but only those vars not in oldCertain vars
                // are from us.
                newCertainVars = certainVars;
                certainVars.removeAll(oldCertainVars);
            }

            // let us see whether we can return NULL:
            if (newCertainVars.isEmpty() && newUncertainVarMap.isEmpty()) {
                return YnmPEVL.NULL;
            }

            // calculate new function symbol
            FunctionSymbol newF = haveMaybe ? this.f : null;

            return new YnmPEVL(newF, newArgs, this.leftMode, newCertainVars, newUncertainVarMap);

        } else {
            return this;
        }
    }

    /**
     * performs deductions for the constraint. Changes the interpretation.
     * Returns null in case of a contradiction and the set of those symbols
     * where the interpretation has been changed, otherwise.
     * @param constraint
     * @param interpretation
     * @return
     */
    public static Set<FunctionSymbol> deduce(Pair<YnmPEVL, YnmPEVL> constraint, Map<FunctionSymbol, YNM[]> interpretation, int restriction) {
        Set<FunctionSymbol> changed = new LinkedHashSet<FunctionSymbol>();
        YnmPEVL left = constraint.x;
        YnmPEVL right = constraint.y;

        // do positive deduction
        Set<String> leftCertain = left.certainVars();
        Map<String, Set<Pair<FunctionSymbol, Integer>>> leftUncertain = left.getUncertainVars();
        for (String var : right.certainVars()) {
            if (leftCertain.contains(var)) {
                continue; // nothing to deduce
            }

            Set<Pair<FunctionSymbol, Integer>> necessary = leftUncertain.get(var);
            if (necessary == null) {
                // var does not exist in left!
                return null;
            }

            // check necessary positions
            for (Pair<FunctionSymbol, Integer> necEntry : necessary) {
                FunctionSymbol f = necEntry.x;
                YNM[] current = interpretation.get(f);
                int n;
                if (current == null) {
                    n = f.getArity();
                    current = new YNM[n];
                    YNM value = restriction == 0 ? YnmPEVL.NO : YnmPEVL.MAYBE;
                    for (int j=0; j<n; j++) {
                        current[j] = value;
                    }
                    interpretation.put(f, current);
                } else {
                    n = current.length;
                }
                int i = necEntry.y.intValue();
                YNM status = current[i];
                if (status == YnmPEVL.MAYBE) {
                    current[i] = YnmPEVL.YES;
                    if (restriction != -1 && restriction < n) {
                        // check for restriction
                        int nrYes = 0;
                        for (YNM stat : current) {
                            if (stat == YnmPEVL.YES) {
                                nrYes++;
                            }
                        }
                        assert(nrYes <= restriction);
                        if (nrYes == restriction && nrYes < n) {
                            // put all maybe's to NO's
                            for (i=0; i<n; i++) {
                                if (current[i] == YnmPEVL.MAYBE) {
                                    current[i] = YnmPEVL.NO;
                                }
                            }
                        }
                    }
                    changed.add(f);
                } else if (status == YnmPEVL.NO) {
                    // contradiction
                    return null;
                }
            }
        }

        // do negative deduction
        Set<String> allLeft = new LinkedHashSet<String>(leftCertain);
        allLeft.addAll(leftUncertain.keySet());

        for (Map.Entry<String, Set<Pair<FunctionSymbol, Integer>>> entry : right.getUncertainVars().entrySet()) {
            Set<Pair<FunctionSymbol, Integer>> positionsToDelete = entry.getValue();
            if (positionsToDelete.isEmpty())
             {
                continue; // nothing to infer
            }
            String var = entry.getKey();
            if (allLeft.contains(var))
             {
                continue; // nothing to infer
            }

            // ah, we have a variable not occurring on the left
            // and we have to delete all positions in the positions-set

            // check NO positions
            for (Pair<FunctionSymbol, Integer> noEntry : positionsToDelete) {
                FunctionSymbol f = noEntry.x;
                YNM[] current = interpretation.get(f);
                if (current == null) {
                    int n = f.getArity();
                    current = new YNM[n];
                    for (int j=0; j<n; j++) {
                        current[j] = YnmPEVL.MAYBE;
                    }
                    interpretation.put(f, current);
                }
                int i = noEntry.y.intValue();
                YNM status = current[i];
                if (status == YNM.MAYBE) {
                    current[i] = YNM.NO;
                    changed.add(f);
                } else if (status == YNM.YES) {
                    // contradiction
                    return null;
                }
            }
        }
        return changed;
    }


    public Set<String> certainVars() {
        return this.certainVars;
    }

    public Map<String, Set<Pair<FunctionSymbol, Integer>>> getUncertainVars() {
        return this.uncertainVarMap;
    }

    /**
     *
     * @param varMapChanged
     * @param certainVarsToMerge - the vars to merge into the map
     * @param certainVars - the varMapChanged must not contain vars of this set,
     *                      and these variables will not be added later on
     * @param position - non null
     * @param leftMode
     */
    private static void mergeCertainIntoVarMap(
            Map<String, Set<Pair<FunctionSymbol, Integer>>> varMapChanged,
            Set<String> certainVarsToMerge,
            Set<String> certainVars,
            Pair<FunctionSymbol, Integer> position,
            boolean leftMode) {
        if (leftMode) {
            for (String var : certainVarsToMerge) {
                if (certainVars.contains(var)) {
                    continue;
                }
                Set<Pair<FunctionSymbol, Integer>> set =
                    new LinkedHashSet<Pair<FunctionSymbol, Integer>>();
                set.add(position);
                Set<Pair<FunctionSymbol, Integer>> setToChange = varMapChanged.get(var);
                if (setToChange == null) {
                    varMapChanged.put(var, set);
                } else {
                    setToChange.retainAll(set);
                }
            }
        } else {
            for (String var : certainVarsToMerge) {
                if (certainVars.contains(var)) {
                    continue;
                }
                Set<Pair<FunctionSymbol, Integer>> setToChange = varMapChanged.get(var);
                if (setToChange == null) {
                    Set<Pair<FunctionSymbol, Integer>> set =
                        new LinkedHashSet<Pair<FunctionSymbol, Integer>>();
                    set.add(position);
                    varMapChanged.put(var, set);
                } else {
                    setToChange.add(position);
                }
            }
        }
    }

    /**
     * merges the second map into the first one. if a new entry is given, then
     * this entry will be added to the second map (but only for the merge!)
     * @param varMapChanged - must not contain entries for vars in certainVars!
     * @param varMapNotChanged
     * @param certainVars - the variables of this set may not be present in varMapChanged,
     *             and entries will not be created for this set of variables!
     * @param position - this position will be combined with the non-changed var map, if non-null.
     * @param leftMode
     */
    private static void mergeVarMaps(
            Map<String, Set<Pair<FunctionSymbol, Integer>>> varMapChanged,
            Map<String, Set<Pair<FunctionSymbol, Integer>>> varMapNotChanged,
            Set<String> certainVars,
            Pair<FunctionSymbol, Integer> position,
            boolean leftMode) {
        if (leftMode) {
            for (Map.Entry<String, Set<Pair<FunctionSymbol, Integer>>> entry : varMapNotChanged.entrySet()) {
                String var = entry.getKey();
                if (certainVars.contains(var)) {
                    continue;
                }
                Set<Pair<FunctionSymbol, Integer>> set = entry.getValue();
                if (position != null) {
                    set = new LinkedHashSet<Pair<FunctionSymbol, Integer>>(set);
                    set.add(position);
                }
                Set<Pair<FunctionSymbol, Integer>> setToChange = varMapChanged.get(var);
                if (setToChange == null) {
                    varMapChanged.put(var, set);
                } else {
                    setToChange.retainAll(set);
                }
            }
        } else {
            for (Map.Entry<String, Set<Pair<FunctionSymbol, Integer>>> entry : varMapNotChanged.entrySet()) {
                String var = entry.getKey();
                if (certainVars.contains(var)) {
                    continue;
                }

                // calculate the new set for the entry to be merged
                Set<Pair<FunctionSymbol, Integer>> set = entry.getValue();
                if (position != null) {
                    boolean keep = set.contains(position);
                    set = new LinkedHashSet<Pair<FunctionSymbol, Integer>>();
                    if (keep) {
                        set.add(position);
                    }
                } else {
                    // here we have to create a copy of set
                    // this is only done if we really put the set into the varMap!
                }

                Set<Pair<FunctionSymbol, Integer>> setToChange = varMapChanged.get(var);
                if (setToChange == null) {
                    // create copy, as this set is inserted into the destrucively changed varMap.
                    if (position == null) {
                        set = new LinkedHashSet<Pair<FunctionSymbol, Integer>>(set);
                    }
                    varMapChanged.put(var, set);
                } else {
                    setToChange.addAll(set);
                }
            }
        }
    }


    @Override
    public int hashCode() {
        throw new RuntimeException("PEVL do not possess hashCodes");
    }

    @Override
    public boolean equals(Object other) {
        throw new RuntimeException("PEVL should not be compared!");
    }

    @Override
    public String toString() {
        return this.toString("");
    }

    public String toString(String indent) {
        if (this == YnmPEVL.NULL) {
            return indent+"NULL\n";
        } else {
            String s = indent + (this.f == null ? "No function symbol" : ("Function: "+this.f.getName())) + "\n";
            if (this.certainVars.isEmpty()) {
                s += indent + "no certain variables\n";
            } else {
                s += indent + "certain variables: ";
                for (String var : this.certainVars) {
                    s += var+" ";
                }
                s += "\n";
            }
            if (this.uncertainVarMap.isEmpty()) {
                s += indent + "no uncertain variables\n";
            } else {
                s += indent + "uncertain variables: ";
                for (String var : this.uncertainVarMap.keySet()) {
                    s += var+" ";
                }
                s += "\n";
            }

            if (this.args == null || this.args.isEmpty()) {
                s += indent + "no arguments\n";
            } else {
                s += indent + "Arguments:\n";
                indent = indent+"  ";
                for (YnmPEVL pevl : this.args) {
                    s += pevl.toString(indent);
                }
            }
            return s;
        }
    }

    public String fullOut() {
        if (this == YnmPEVL.NULL) {
            return "NULL";
        } else {
            String s = "";
            if (this.f == null) {
                s += "noF";
            } else {
                s += "f="+this.f.getName();
            }
            if (this.args == null) {
                s += "noArgs";
            } else {
                s += "args=";
                for (YnmPEVL arg : this.args) {
                    s += arg.fullOut()+",";
                }
            }
            s += " Vars=";
            Set<String> sortedCertain = new TreeSet<String>(this.certainVars);
            for (String var : sortedCertain) {
                s += var+",";
            }

            s += " Miss=";
            Set<String> sortedMiss = new TreeSet<String>();
            for (FunctionSymbol g : this.missInter) {
                sortedMiss.add(g.getName());
            }
            for (String g : sortedCertain) {
                s += g+",";
            }

            s += " uncertains=";
            Map<String, String> sortedVarMap =
                new TreeMap<String, String>();
            for (Map.Entry<String, Set<Pair<FunctionSymbol, Integer>>> entry : this.uncertainVarMap.entrySet()) {
                Set<String> sortedSet = new TreeSet<String>();
                for (Pair<FunctionSymbol, Integer> pair : entry.getValue()) {
                    sortedSet.add(pair.x.getName()+"/"+pair.y+",");
                }
                String ss = "";
                for (String sss : sortedSet) {
                    ss += sss;
                }
                sortedVarMap.put(entry.getKey(), ss);
            }
            for (Map.Entry<String, String> entry : sortedVarMap.entrySet()) {
                s += entry.getKey()+": "+entry.getValue();
            }

            return s;
        }
    }

}
