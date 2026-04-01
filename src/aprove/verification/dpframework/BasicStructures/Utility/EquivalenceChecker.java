package aprove.verification.dpframework.BasicStructures.Utility;

import java.io.*;
import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.TypeAnalyzers.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.Variable;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class EquivalenceChecker {

    private static class EquivalenceObject {

        public EquivalenceObject(Object o, List<FunctionSymbol> list) {
            this.o = o;
            this.list = list;
        }

        private Object o;
        private List<FunctionSymbol> list;

        public Object getObject() {
            return this.o;
        }

        public List<FunctionSymbol> getList() {
            return this.list;
        }

        @Override
        public boolean equals(Object o) {
            EquivalenceObject eo = (EquivalenceObject) o;
            return this.o.equals(eo.o);
        }

        @Override
        public int hashCode() {
            return this.o.hashCode();
        }

        @Override
        public String toString() {
            return this.o + " (" + this.list + ")";
        }

    }

    private static TRSTerm toEquiv(TRSTerm t, Map<FunctionSymbol, FunctionSymbol> map, List<FunctionSymbol> list, Wrapper<Integer> i) {
        if (t.isVariable()) {
            return t;
        } else {
            TRSFunctionApplication ft = (TRSFunctionApplication) t;
            FunctionSymbol f = ft.getRootSymbol();
            FunctionSymbol g = map.get(f);
            if (g == null) {
                Integer id = i.x;
                g = FunctionSymbol.create("f"+id, f.getArity());
                map.put(f, g);
                list.add(f);
                i.x = id+1;
            }
            ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
            for (TRSTerm arg : ft.getArguments()) {
                newArgs.add(EquivalenceChecker.toEquiv(arg, map, list, i));
            }
            return TRSTerm.createFunctionApplication(g, ImmutableCreator.create(newArgs));
        }
    }

    private static EquivalenceObject fromTerm(TRSTerm t) {
        t = t.getStandardRenumbered();
        Map<FunctionSymbol, FunctionSymbol> map = new HashMap<FunctionSymbol, FunctionSymbol>();
        final List<FunctionSymbol> fList = new ArrayList<FunctionSymbol>();
        Wrapper<Integer> i = new Wrapper<Integer>(0);
        final TRSTerm et = EquivalenceChecker.toEquiv(t, map, fList, i);
        return new EquivalenceObject(et, fList);
    }

    private static EquivalenceObject fromRule(GeneralizedRule r) {
        Map<FunctionSymbol, FunctionSymbol> map = new HashMap<FunctionSymbol, FunctionSymbol>();
        final List<FunctionSymbol> fList = new ArrayList<FunctionSymbol>();
        Wrapper<Integer> i = new Wrapper<Integer>(0);
        TRSTerm left = r.getLhsInStandardRepresentation();
        TRSTerm right = r.getRhsInStandardRepresentation();
        TRSTerm eLeft = EquivalenceChecker.toEquiv(left, map, fList, i);
        TRSTerm eRight = EquivalenceChecker.toEquiv(right, map, fList, i);
        final GeneralizedRule eRule = GeneralizedRule.create((TRSFunctionApplication)eLeft, eRight);
        return new EquivalenceObject(eRule, fList);
    }

    private static EquivalenceMap eqMapFromRules(Set<Rule> rules) {
        EquivalenceMap map = new EquivalenceMap();
        for (Rule rule : rules) {
            map.add(EquivalenceChecker.fromRule(rule));
        }
        return map;
    }

    private static EquivalenceMap eqMapFromTerms(Set<? extends TRSTerm> terms) {
        EquivalenceMap map = new EquivalenceMap();
        for (TRSTerm t : terms) {
            map.add(EquivalenceChecker.fromTerm(t));
        }
        return map;
    }

    /**
     * Tries to relate to QTRSs by function renaming.
     * @param trs1
     * @param trs2
     * @return null, if there is no renaming alpha such that alpha(trs1) = trs2.
     *  Otherwise, a renaming map alpha is returned such that alpha(trs1) = trs2.
     */
    public static Map<FunctionSymbol, FunctionSymbol> relate(QTRSProblem trs1, QTRSProblem trs2) {
        Set<Rule> R1 = trs1.getR();
        Set<Rule> R2 = trs2.getR();
        Set<TRSFunctionApplication> Q1 = trs1.getQ().getTerms();
        Set<TRSFunctionApplication> Q2 = trs2.getQ().getTerms();

        // first some easy checks with sizes
        if (R1.size() != R2.size() || Q1.size() != Q2.size()) {
            return null;
        }

        // then try to relate rules
        EquivalenceMap map1 = EquivalenceChecker.eqMapFromRules(R1);
        EquivalenceMap map2 = EquivalenceChecker.eqMapFromRules(R2);

        List<Pair<Set<List<FunctionSymbol>>, Set<List<FunctionSymbol>>>> toSolve = new ArrayList<Pair<Set<List<FunctionSymbol>>, Set<List<FunctionSymbol>>>>();
        boolean okay = map1.relateTo(map2, toSolve);

        if (!okay) {
            return null;
        }

        // next try to relate terms
        map1 = EquivalenceChecker.eqMapFromTerms(Q1);
        map2 = EquivalenceChecker.eqMapFromTerms(Q2);
        okay = map1.relateTo(map2, toSolve);
        if (!okay) {
            return null;
        }

        // okay, we have to start SAT encoding
        Encoder e = new Encoder();
        e.encode(toSolve);
        return e.getMapping();
    }

    /**
     * Tries to relate to RelTRSs by function renaming.
     * @param trs1
     * @param trs2
     * @return null, if there is no renaming alpha such that alpha(trs1) = trs2.
     *  Otherwise, a renaming map alpha is returned such that alpha(trs1) = trs2.
     */
    public static Map<FunctionSymbol, FunctionSymbol> relate(RelTRSProblem trs1, RelTRSProblem trs2) {
        Set<Rule> R1 = trs1.getR();
        Set<Rule> R2 = trs2.getR();
        Set<Rule> S1 = trs1.getS();
        Set<Rule> S2 = trs2.getS();
        // first some easy checks with sizes
        if (R1.size() != R2.size() || S1.size() != S2.size()) {
            return null;
        }

        // then try to relate rules
        EquivalenceMap map1 = EquivalenceChecker.eqMapFromRules(R1);
        EquivalenceMap map2 = EquivalenceChecker.eqMapFromRules(R2);

        List<Pair<Set<List<FunctionSymbol>>, Set<List<FunctionSymbol>>>> toSolve = new ArrayList<Pair<Set<List<FunctionSymbol>>, Set<List<FunctionSymbol>>>>();
        boolean okay = map1.relateTo(map2, toSolve);

        if (!okay) {
            return null;
        }

        // next try to relate relative rules
        map1 = EquivalenceChecker.eqMapFromRules(S1);
        map2 = EquivalenceChecker.eqMapFromRules(S2);
        okay = map1.relateTo(map2, toSolve);
        if (!okay) {
            return null;
        }

        // okay, we have to start SAT encoding
        Encoder e = new Encoder();
        e.encode(toSolve);
        return e.getMapping();
    }

    /**
     * @author thiemann
     * This class collects equivalence objects and groups
     * them into equivalence classes by the {@link add}-method.
     *
     * Then finally it can be tried to relate two equivalence classes
     * by {@link relateTo} which directly detects unrelateability or
     * produces constraints which can then be passed to the {@link Encoder}.
     */
    private static class EquivalenceMap {
        Map<Object,Set<List<FunctionSymbol>>> eqClasses;

        /**
         * creates a new empty EquivalenceMap
         */
        public EquivalenceMap() {
            this.eqClasses = new HashMap<Object,Set<List<FunctionSymbol>>>();
        }

        /**
         * adds all pairs of sets that have to be connected to toSolve
         * @param em another equivalence Map which we want to relate against
         * @param toSolve a list of constraints that have to be satisfied. It will
         *   be expanded by constraints that need to be satisfied in order
         *   to relate this map with em.
         * @return false if this map cannot be related with em. true otherwise. in
         *   that case all equivalence classes that have to be related are added to
         *   toSolve
         */
        public boolean relateTo(EquivalenceMap em, List<Pair<Set<List<FunctionSymbol>>, Set<List<FunctionSymbol>>>> toSolve) {
            final Map<Object,Set<List<FunctionSymbol>>> one, two;
            one = this.eqClasses;
            two = em.eqClasses;
            if (!one.keySet().equals(two.keySet())) {
                return false;
            }
            for (Map.Entry<Object, Set<List<FunctionSymbol>>> entry : one.entrySet()) {
                Set<List<FunctionSymbol>> oneSet = entry.getValue();
                Set<List<FunctionSymbol>> twoSet = two.get(entry.getKey()); // must exist, since keysets are identical
                if (oneSet.size() != twoSet.size()) {
                    return false;
                }
                toSolve.add(new Pair<Set<List<FunctionSymbol>>, Set<List<FunctionSymbol>>>(oneSet, twoSet));
            }
            return true;
        }

        /**
         * adds a new Equivalence Object to this map
         * @param eo
         */
        public void add(EquivalenceObject eo) {
            Object o = eo.getObject();
            Set<List<FunctionSymbol>> eqClass = this.eqClasses.get(o);
            if (eqClass == null) {
                eqClass = new HashSet<List<FunctionSymbol>>();
                this.eqClasses.put(o, eqClass);
            }
            eqClass.add(eo.getList());
        }

        @Override
        public String toString() {
            String res = "";
            for (Map.Entry<Object, Set<List<FunctionSymbol>>> e : this.eqClasses.entrySet()) {
                res += e.getKey() + "  ====>  " + e.getValue() + "\n";
            }
            return res;
        }
    }

    /**
     * An Encoder accepts a list of constraints and then encodes
     * everything into SAT and tries to find an bijective mapping
     * from the one signature to the other
     *
     * @author thiemann
     */
    private static class Encoder {

        Map<Pair<FunctionSymbol,FunctionSymbol>, Variable<None>> fgToProp = new HashMap<Pair<FunctionSymbol,FunctionSymbol>, Variable<None>>();
        FormulaFactory<None> ff = new FullSharingFactory<None>(); // AtomCachingFactory<None>();
        // the big conjunction will be formed from these conditions
        List<Formula<None>> conditions = new ArrayList<Formula<None>>();
        // the following maps stores all properties f = g_1, ..., f = g_n
        Map<FunctionSymbol, Collection<Pair<FunctionSymbol,Variable<None>>>> leftToRightPossibilites = new HashMap<FunctionSymbol, Collection<Pair<FunctionSymbol,Variable<None>>>>();
        // and f_1 = g, ..., f_k = g
        Map<FunctionSymbol, Collection<Pair<FunctionSymbol,Variable<None>>>> rightToLeftPossibilites = new HashMap<FunctionSymbol, Collection<Pair<FunctionSymbol,Variable<None>>>>();

        /**
         * delivers (a possibly new) proposition which states that f and g should be related
         * @param f
         * @param g
         * @return
         */
        private Variable<None> getProp(FunctionSymbol f, FunctionSymbol g) {
            Pair<FunctionSymbol,FunctionSymbol> fg = new Pair<FunctionSymbol, FunctionSymbol>(f, g);
            Variable<None> prop = this.fgToProp.get(fg);
            if (prop == null) {
                prop = this.ff.buildVariable();
                this.fgToProp.put(fg, prop);
                Collection<Pair<FunctionSymbol,Variable<None>>> fToGPoss = this.leftToRightPossibilites.get(f);
                if (fToGPoss == null) {
                    fToGPoss = new ArrayList<Pair<FunctionSymbol,Variable<None>>>();
                    this.leftToRightPossibilites.put(f, fToGPoss);
                }
                fToGPoss.add(new Pair<FunctionSymbol, Variable<None>>(g,prop));
                Collection<Pair<FunctionSymbol,Variable<None>>> gToFPoss = this.rightToLeftPossibilites.get(g);
                if (gToFPoss == null) {
                    gToFPoss = new ArrayList<Pair<FunctionSymbol,Variable<None>>>();
                    this.rightToLeftPossibilites.put(g, gToFPoss);
                }
                gToFPoss.add(new Pair<FunctionSymbol, Variable<None>>(f,prop));
            }
            return prop;
        }


        /**
         * Encodes that all constraints are satisfied
         * @param constraints a list of constraints where for
         *   all constraints (eqLeft, eqRight) it is guaranteed that
         *   1) eqLeft and eqRight have the same size
         *   2) the elements of eqLeft and eqRight all have the same size.
         *   Both of these requirements are satisfies by constraints that have
         *   been generated by the {@link EquivalenceMap.relate} method.
         */
        public void encode(List<Pair<Set<List<FunctionSymbol>>, Set<List<FunctionSymbol>>>> constraints) {
            for (Pair<Set<List<FunctionSymbol>>, Set<List<FunctionSymbol>>> eqClasses : constraints) {
                Set<List<FunctionSymbol>> eq1 = eqClasses.x;
                Set<List<FunctionSymbol>> eq2 = eqClasses.y;
                if (Globals.useAssertions) {
                    assert(eq1.size() == eq2.size());
                }
                final int n = eq2.size();
                if (n == 1) {
                    // easy case first
                    Iterator<FunctionSymbol> gIt = eq2.iterator().next().iterator();
                    for (FunctionSymbol f : eq1.iterator().next()) {
                        FunctionSymbol g = gIt.next();
                        this.conditions.add(this.getProp(f, g));
                    }
                } else {
                    List<Formula<None>> eqProps = new ArrayList<Formula<None>>();
                    List<Formula<None>> conjuncts = new ArrayList<Formula<None>>();
                    for (List<FunctionSymbol> left : eq1) {
                        eqProps.clear();
                        for (List<FunctionSymbol> right : eq2) {
                            // encode left = right   ->   f_1 = g_1 /\ ... /\ f_n = g_n
                            conjuncts.clear();
                            Iterator<FunctionSymbol> gIt = right.iterator();
                            for (FunctionSymbol f : left) {
                                FunctionSymbol g = gIt.next();
                                conjuncts.add(this.getProp(f, g));
                            }
                            Formula<None> relateFs = this.ff.buildAnd(conjuncts);
                            Variable<None> relateEqClasses = this.ff.buildVariable();
                            this.conditions.add(this.ff.buildImplication(relateEqClasses, relateFs));
                            // and store left = right
                            eqProps.add(relateEqClasses);
                        }
                        // finally encode that there for each left there must be corresponding right
                        // (note that symmetric encoding is not necessary since will be a conflict later in
                        //  the signature matching. For the same reason we can encode
                        //  "at least one" instead of "exactly one")
                        Formula<None> atLeastOneRight = this.ff.buildOr(eqProps);
                        this.conditions.add(atLeastOneRight);
                    }
                }
            }
        }

        private Formula<None> exactlyOne(Collection<Pair<FunctionSymbol, Variable<None>>> formulas) {
            final Iterator<Pair<FunctionSymbol, Variable<None>>> it = formulas.iterator();
            return this.exactlyOne(new Iterator<Variable<None>>(){
                @Override
                public boolean hasNext() {
                    return it.hasNext();
                }
                @Override
                public Variable<None> next() {
                    return it.next().y;
                }
                @Override
                public void remove() {
                    it.remove();
                }
            }, formulas.size());
        }

        private Formula<None> exactlyOne(Iterator<? extends Formula<None>> formulas, int n) {
            if (n == 0) {
                return this.ff.buildConstant(false);
            }
            if (n == 1) {
                return formulas.next();
            }
            if (n == 2) {
                return this.ff.buildXor(formulas.next(), formulas.next());
            }
            List<Formula<None>> conjuncts = new ArrayList<Formula<None>>();
            Formula<None> R_n = this.ff.buildConstant(true);
            Formula<None> P_n = formulas.next();
            Formula<None> Q_n = P_n;
            while (formulas.hasNext()) {

                Formula<None> R_n1 = this.ff.buildVariable();
                Formula<None> Q_n1 = this.ff.buildVariable();
                conjuncts.add(this.ff.buildIff(R_n1, this.ff.buildAnd(this.ff.buildNot(P_n), R_n)));
                P_n = formulas.next();
                R_n = R_n1;
                conjuncts.add(this.ff.buildIff(Q_n1, this.ff.buildOr(
                        this.ff.buildAnd(this.ff.buildNot(P_n), Q_n),
                        this.ff.buildAnd(P_n,R_n))));
                Q_n = Q_n1;
            }

            conjuncts.add(Q_n);
            return this.ff.buildAnd(conjuncts);
        }

        public Map<FunctionSymbol,FunctionSymbol> getMapping() {
            // encode that for each f there is unique g
            for (Collection<Pair<FunctionSymbol,Variable<None>>> possibilities : this.leftToRightPossibilites.values()) {
                this.conditions.add(this.exactlyOne(possibilities));
            }

            // and vice versa
            for (Collection<Pair<FunctionSymbol,Variable<None>>> possibilities : this.rightToLeftPossibilites.values()) {
                this.conditions.add(this.exactlyOne(possibilities));
            }

            Formula<None> finalFormula = this.ff.buildAnd(this.conditions);
            SATChecker sc = new SAT4JChecker();
            int[] result = null;
            try {
                // XXX - use the real Abortion.
                result = sc.solve(finalFormula, AbortionFactory.create());
            } catch (AbortionException e) {
                // That abortion should have no reason to abort.
                throw new RuntimeException("This has not happened. Really!", e);
            } catch (SolverException e) {
                throw new RuntimeException("Solver died", e);
            }
            if (result == null) {
                // no assignment possible
                return null;
            }

            // otherwise extract mapping
            Map<FunctionSymbol, FunctionSymbol> res = new HashMap<FunctionSymbol, FunctionSymbol>();
            f: for (Map.Entry<FunctionSymbol, Collection<Pair<FunctionSymbol,Variable<None>>>> f_to_gs : this.leftToRightPossibilites.entrySet()) {
                FunctionSymbol f = f_to_gs.getKey();
                for (Pair<FunctionSymbol, Variable<None>> g_and_prop : f_to_gs.getValue()) {
                    int id = g_and_prop.y.getId();
                    if (result[id - 1] == id) {
                        res.put(f, g_and_prop.x);
                        continue f;
                    }
                }
                assert(false);
            }



            return res;
        }
    }

    private static Object getProblem(String fileName) {
        Input input = new FileInput(new File(fileName));
        System.err.println("Processing "+fileName);
        if (input == null) {
            System.err.println("File not found: " + fileName);
            return null;
        }
        TypedInput typedInput;
        try {
            typedInput = new ExtensionTypeAnalyzer().analyze(input);
        } catch (ParserErrorsSourceException e) {
            System.err.println("ERROR\nError while parsing '"+fileName+"'");
            return null;
        }

        return typedInput.getInput();
    }


    public static void main(String[] args) throws IOException {
        BufferedReader br = new BufferedReader(new FileReader(args[0]));
        Map<String,QTRSProblem> trss = new LinkedHashMap<String, QTRSProblem>();
        Map<String,RelTRSProblem> rtrss = new LinkedHashMap<String, RelTRSProblem>();
        Map<FunctionSymbol, FunctionSymbol> mapping;

        String filename;
        file: while ((filename = br.readLine()) != null) {
            Object o = EquivalenceChecker.getProblem(filename);
            if (o instanceof QTRSProblem) {
                QTRSProblem trs = (QTRSProblem) o;
                for (Map.Entry<String, QTRSProblem> fn_trs : trss.entrySet()) {
                    QTRSProblem oldTrs = fn_trs.getValue();
                    mapping = EquivalenceChecker.relate(trs, oldTrs);
                    if (mapping != null) {
                        System.out.println(filename + " is identical to "+fn_trs.getKey()+":\n"+mapping);
                        continue file;
                    }
                }
                // okay, trs is new
                trss.put(filename, trs);
            } else if (o instanceof RelTRSProblem) {
                RelTRSProblem trs = (RelTRSProblem) o;
                for (Map.Entry<String, RelTRSProblem> fn_trs : rtrss.entrySet()) {
                    RelTRSProblem oldTrs = fn_trs.getValue();
                    mapping = EquivalenceChecker.relate(trs, oldTrs);
                    if (mapping != null) {
                        System.out.println(filename + " is identical to "+fn_trs.getKey()+":\n"+mapping);
                        continue file;
                    }
                }
                // okay, trs is new
                rtrss.put(filename, trs);
            } else {
                System.out.println(filename + " has unknown type: "+o.getClass());
            }
        }
        br.close();
        System.out.println("\n\nTRSs\n===================\n");
        for (String s : trss.keySet()) {
            System.out.println(s);
        }
        System.out.println("\n\nRel-TRSs\n===================\n");
        for (String s : rtrss.keySet()) {
            System.out.println(s);
        }
    }
}
