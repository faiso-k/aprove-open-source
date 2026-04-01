/*
 * Created on 18.03.2005
 */
package aprove.verification.dpframework.BasicStructures.NegativePolynomials;

import java.util.*;

import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public abstract class PEVLSolver {

    /**
     * takes a partially specified poly interpretation and a set of constraints.
     * Returns null, if the poly interpretation cannot solve the constraints for
     * all specializations. Otherwise, it returns a mapping from functionsymbols
     * to YNM-vectors which represent to not/maybe/do keep each argument.
     * @param polyInterpretation
     * @param pepConstraints
     * @return
     */
    public static Map<FunctionSymbol, YNM[]> solve(Map<FunctionSymbol, int[]> polyInterpretation, Collection<PEP> pepConstraints, Map<FunctionSymbol, YNM[]> oldSolutionInterpretation) {
        // first: create signature of constraints
        Set<FunctionSymbol> sig = new LinkedHashSet<FunctionSymbol>();
        for (PEP pep : pepConstraints) {
            sig.addAll(pep.getMissingInterpretations());
        }


        // second: create YNM interpretation for this signature
        //         regarding the given interpretation
        Map<FunctionSymbol, YNM[]> interpretation = new LinkedHashMap<FunctionSymbol, YNM[]>();
        Set<FunctionSymbol> directSpecialize = new LinkedHashSet<FunctionSymbol>();
        for (FunctionSymbol f : sig) {
            int n = f.getArity();
            YNM[] inter = new YNM[n];
            int[] polyInter = polyInterpretation.get(f);
            if (polyInter == null) {
                YNM[] oldInter = oldSolutionInterpretation.get(f);
                if (oldInter == null) {
                    for (int i=0; i<n; i++) {
                        inter[i] = YNM.MAYBE;
                    }
                } else {
                    directSpecialize.add(f);
                    for (int i=0; i<n; i++) {
                        inter[i] = oldInter[i];
                    }
                }
            } else {
                for (int i=n; i != 0;) {
                    boolean value = polyInter[i] != 0;
                    i--;
                    inter[i] = YNM.fromBool(value);
                }
            }
            interpretation.put(f, inter);
        }

        // third: Setup PEVL-Constraints
        List<Pair<PEVL, PEVL>> constraints = new ArrayList<Pair<PEVL, PEVL>>(pepConstraints.size());
//        System.out.println("New PEVL solver:");
        for (PEP pep : pepConstraints) {
            Pair<PEVL, PEVL> constraint = pep.createPEVLConstraint();
//            System.out.println(constraint.x +" / "+ constraint.y);
            constraint.x = constraint.x.specialize(directSpecialize, interpretation);
            constraint.y = constraint.y.specialize(directSpecialize, interpretation);
            constraints.add(constraint);
        }


        State state = State.create(constraints, interpretation);
//        if (bug) {
//            throw new RuntimeException();
//        }

        if (state == null) {
            return null;
        } else {
            return state.interpretation;
        }
    }

    private static class State {

        List<Pair<PEVL, PEVL>> constraints;
        Map<FunctionSymbol, YNM[]> interpretation;

        private State(List<Pair<PEVL, PEVL>> constraints, Map<FunctionSymbol, YNM[]> interpretation) {
            this.constraints = constraints;
            this.interpretation = interpretation;
        }

        /**
         * destructively changes the list of constraints!
         * @param constraints
         * @param interpretation
         * @return
         */
        public static State create(List<Pair<PEVL, PEVL>> constraints, Map<FunctionSymbol, YNM[]> interpretation) {
            State state = new State(constraints, interpretation);
            return state.destructiveSimplify();
        }

        public State destructiveSimplify() {
            boolean somethingChanged = true;
            while (somethingChanged) {
                Set<FunctionSymbol> changed = new LinkedHashSet<FunctionSymbol>();
                for (Pair<PEVL, PEVL> constraint : this.constraints) {
                    PEVL left = constraint.x;
                    PEVL right = constraint.y;

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
                            YNM[] current = this.interpretation.get(f);
                            int i = necEntry.y.intValue();
                            YNM status = current[i];
                            if (status == YNM.MAYBE) {
                                current[i] = YNM.YES;
                                changed.add(f);
                            } else if (status == YNM.NO) {
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
                            YNM[] current = this.interpretation.get(f);
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
                }

                somethingChanged = !changed.isEmpty();

                if (somethingChanged) {
                    for (Pair<PEVL, PEVL> cons : this.constraints) {
                        cons.x = cons.x.specialize(changed, this.interpretation);
                        cons.y = cons.y.specialize(changed, this.interpretation);
                    }
                }
            } // end global loop

            return this;

        }

        public static String toString(FunctionSymbol f, YNM[] interpretation) {
            String s = f.getName()+": (";
            boolean first = true;
            for (YNM status : interpretation) {
                if (first) {
                    first = false;
                } else {
                    s += ",";
                }
                if (status == YNM.YES) {
                    s += "Y";
                } else if (status == YNM.NO) {
                    s += "N";
                } else {
                    s += "?";
                }
            }
            return s+")";

        }

        public static void outputInterpretation(Map<FunctionSymbol, YNM[]> interpretation) {
            System.out.println("Interpretation:");
            for (Map.Entry<FunctionSymbol, YNM[]> entry : interpretation.entrySet()) {
                System.out.println(State.toString(entry.getKey(), entry.getValue()));
            }
        }

    }

}
