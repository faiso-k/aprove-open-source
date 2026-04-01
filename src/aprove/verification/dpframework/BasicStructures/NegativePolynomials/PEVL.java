/*
 * Created on 18.03.2005
 */
package aprove.verification.dpframework.BasicStructures.NegativePolynomials;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A Partially evaluated variable list (PEVL) is like a PEP,
 * but it only considers variables, not full polynomials. It is
 * used for a combined check of a set of PEP-constraints whether they
 * are satisfiable. This is done by incrementally (de)activating positions
 * until we find a contradiction or can not conclude
 * anything further.
 *
 * (This check may also be used for AFSSolver, as we do nothing but
 *  to check which (non-collapsing) filterings are possible.
 *
 * @author thiemann
 */
public class PEVL {

    private final static YNM YES = YNM.YES;
    private final static YNM NO = YNM.NO;
    private final static YNM MAYBE = YNM.MAYBE;


    private final static PEVL NULL = new PEVL(
            null,
            null,
            true,
            new LinkedHashSet<String>(),
            new LinkedHashMap<String, Set<Pair<FunctionSymbol, Integer>>>()
            );

    /*
     * real values
     */
    private final FunctionSymbol f;
    private final PEVL[] args;
    private final boolean leftMode;
    private final Set<String> certainVars;

    /*
     * calculated values
     */
    private final Map<String, Set<Pair<FunctionSymbol, Integer>>> uncertainVarMap;
    private final Set<FunctionSymbol> missInter;

    private PEVL(FunctionSymbol f,
            PEVL[] args,
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
            for (PEVL arg : args) {
                this.missInter.addAll(arg.missInter);
            }
            if (f == null) {
                // flattening!
                List<PEVL> newArgs = new LinkedList<PEVL>();
                for (PEVL arg : args) {
                    if (arg.args != null && arg.f == null) {
                        for (PEVL subArg : arg.args) {
                            newArgs.add(subArg);
                        }
                    } else {
                        newArgs.add(arg);
                    }
                }
                args = new PEVL[newArgs.size()];
                int i = 0;
                for (PEVL newArg : newArgs) {
                    args[i] = newArg;
                    i++;
                }
            }
        }

        this.args = args;

//        int hashCode = 493012389;
//        if (this.f != null) {
//            hashCode += this.f.hashCode();
//        }
//        if (this.args == null) {
//            hashCode += this.certainVars.hashCode();
//        } else {
//            hashCode += this.args.hashCode();
//        }
//        this.hashCode = hashCode;
    }


    /**
     * create variable PEVL
     */
    public static PEVL create(String var, boolean leftMode) {
        Set<String> certainVars = new LinkedHashSet<String>();
        certainVars.add(var);
        Map<String, Set<Pair<FunctionSymbol, Integer>>> uncertainVarMap =
            new LinkedHashMap<String, Set<Pair<FunctionSymbol, Integer>>>();
        return new PEVL(null, null, leftMode, certainVars, uncertainVarMap);
    }

    /**
     * creates unevaluated PEVL
     * @param f - if given, the arity of the args must be the arity of n,
     *    if null, args must be an arbitrary non-null array
     * @param args
     */
    public static PEVL create(FunctionSymbol f, PEVL[] args, boolean leftMode) {
        Set<String> certainVars = new LinkedHashSet<String>();
        Map<String, Set<Pair<FunctionSymbol, Integer>>> uncertainVarMap =
            new LinkedHashMap<String, Set<Pair<FunctionSymbol, Integer>>>();
        int n = args.length;
        int j = 0;
        boolean haveF = f != null;

        // first determine nr of non-null arguments
        // and the set of certain vars
        for (int i=0; i<n; i++) {
            PEVL arg = args[i];
            if (arg == PEVL.NULL) {
                continue;
            }

            j++;

            if (!haveF) {
                certainVars.addAll(arg.certainVars);
            }
        }

        if (j == 0) {
            return PEVL.NULL;
        }

        // next calculate the new uncertainVarMap
        int newN = haveF ? n : j;
        PEVL[] newArgs = new PEVL[newN];
        j = 0;
        Pair<FunctionSymbol, Integer> pair = null;
        for (int i=0; i<n; i++) {
            PEVL arg = args[i];
            if (arg == PEVL.NULL) {
                if (haveF) {
                    newArgs[j] = PEVL.NULL;
                    j++;
                }
                continue;
            }

            if (haveF) {
                pair = new Pair<FunctionSymbol, Integer>(f, i);
                PEVL.mergeCertainIntoVarMap(uncertainVarMap, arg.certainVars, certainVars, pair, leftMode);
            }

            PEVL.mergeVarMaps(uncertainVarMap, arg.uncertainVarMap, certainVars, pair, leftMode);

            newArgs[j] = arg;
            j++;
        }


        return new PEVL(f, newArgs, leftMode, certainVars, uncertainVarMap);
    }

    public PEVL specialize(FunctionSymbol g, Map<FunctionSymbol, YNM[]> interpretation) {
        if (this.missInter.contains(g)) {
            boolean haveF = this.f != null;
            boolean haveMaybe = false;
            YNM[] inter;
            if (haveF) {
                inter = interpretation.get(this.f);
            } else {
                inter = null;
            }

            // first compute certainVars and specialized arguments (if needed)
            Set<String> certainVars = new LinkedHashSet<String>();
            int n = this.args.length;
            PEVL[] specializedArgs = new PEVL[n];
            int j = 0;
            for (int i=0; i<n; i++) {
                PEVL arg = this.args[i];

                YNM interState = haveF ? inter[i] : PEVL.YES;

                // calculate new Arg
                if (arg != PEVL.NULL && interState != PEVL.NO) {
                    arg = arg.specialize(g, interpretation);
                    if (interState == PEVL.YES) {
                        // and store certain vars
                        certainVars.addAll(arg.certainVars);
                    }
                } else {
                    arg = PEVL.NULL;
                }

                // incr non-null counter
                if (arg != PEVL.NULL) {
                    j++;
                    if (interState == PEVL.MAYBE) {
                        haveMaybe = true;
                    }
                }

                // and store specialized arg
                specializedArgs[i] = arg;
            }


            // if all NULL then we can return NULL
            if (j == 0) {
                return PEVL.NULL;
            }

            // store only non-NULL args in case that we have no unspecified argument
            int newN = haveMaybe ? n : j;

            PEVL[] newArgs = new PEVL[newN];

            /*
             * build new varMap and new args
             */
            Map<String, Set<Pair<FunctionSymbol, Integer>>> uncertainVarMap =
                new LinkedHashMap<String, Set<Pair<FunctionSymbol, Integer>>>();
            j = 0;
            for (int i=0; i<n; i++) {
                PEVL arg = specializedArgs[i];

                // first store argument
                if (arg == PEVL.NULL && !haveMaybe) {
                    continue;
                } else {
                    newArgs[j] = arg;
                    j++;
                }

                YNM interState = haveF ? inter[i] : PEVL.YES;

                if (interState != PEVL.NO) {
                    // new position entry needed?
                    Pair<FunctionSymbol, Integer> pair;
                    if (interState == PEVL.MAYBE) {
                        pair = new Pair<FunctionSymbol, Integer>(this.f, i);
                        PEVL.mergeCertainIntoVarMap(uncertainVarMap, arg.certainVars, certainVars, pair, this.leftMode);
                    } else {
                        pair = null;
                    }

                    PEVL.mergeVarMaps(uncertainVarMap, arg.uncertainVarMap, certainVars, pair, this.leftMode);
                }
            }

            boolean fullySpecified = uncertainVarMap.isEmpty();
            FunctionSymbol newF = fullySpecified ? null : this.f;
            return new PEVL(newF, newArgs, this.leftMode, certainVars, uncertainVarMap);

        } else {
            return this;
        }
    }

    public PEVL specialize(Set<FunctionSymbol> toSpecialize, Map<FunctionSymbol, YNM[]> inter) {
        PEVL pevl = this;
        for (FunctionSymbol f : toSpecialize) {
            if (pevl == PEVL.NULL) {
                return PEVL.NULL;
            } else {
                pevl = pevl.specialize(f, inter);
            }
        }
        return pevl;
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

//    private final int hashCode;

    @Override
    public int hashCode() {
        throw new RuntimeException("PEVL do not possess hashCodes");
//        return this.hashCode;
    }

    @Override
    public boolean equals(Object other) {
        throw new RuntimeException("PEVL should not be compared!");
//        if (other instanceof PEVL) {
//            PEVL pevl = (PEVL) other;
//            if (pevl.hashCode != this.hashCode) return false;
//
//            if (this.f == null) {
//                if (pevl.f != null) {
//                    return false;
//                }
//            } else {
//                if (!this.f.equals(pevl.f)) return false;
//            }
//
//            if (this.args == null) {
//                if (pevl.args == null) {
//                    return this.certainVars.equals(pevl.certainVars);
//                } else {
//                    return false;
//                }
//            } else {
//                return (this.args.equals(pevl.args));
//            }
//        } else {
//            return false;
//        }
    }

    @Override
    public String toString() {
        if (this == PEVL.NULL) {
            return "NULL";
        } else {
            if (this.args == null) {
                return this.certainVars.iterator().next();
            } else {
                String s = this.f == null ? "" : this.f.getName();
                s += "(";
                boolean first = true;
                for (PEVL pevl : this.args) {
                    if (first) {
                        s += pevl;
                        first = false;
                    } else {
                        s += ","+pevl;
                    }
                }
                return s+")";
            }
        }
    }

    public String fullOut() {
        if (this == PEVL.NULL) {
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
                for (PEVL arg : this.args) {
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
