package aprove.verification.complexity.CpxIntTrsProblem.Algorithms;

import java.io.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.input.Programs.cint.Translator;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.TransitionProgram.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class CpxIntTrsNormalizer {

    private static class FNG {
        private final LinkedHashMap<FunctionSymbol, String> symToName = new LinkedHashMap<>();
        private final LinkedHashSet<String> usedNames = new LinkedHashSet<>();

        public static String getSaveStateName(FunctionSymbol fs) {
            String name = fs.getName().replaceAll("[^a-zA-Z0-9]", "");
            if (name.length() == 0 || Character.isDigit(name.charAt(0)) || Character.isUpperCase(name.charAt(0))) {
                name = "l" + name;
            }
            return name;
        }

        String getName(FunctionSymbol sym) {
            assert sym != null;
            String name = this.symToName.get(sym);
            if (name != null) {
                return name;
            }
            String raw = FNG.getSaveStateName(sym);
            name = raw;
            int i = 0;
            while (this.usedNames.contains(name)) {
                name = raw + i;
            }
            this.usedNames.add(name);
            this.symToName.put(sym, name);
            return name;
        }

        FunctionSymbol getFreshSymbol(String preferredName, int arity) {
            assert preferredName != null && preferredName.length() > 0;
            assert arity >= 0;
            String name = preferredName;
            int i = 0;
            while (this.usedNames.contains(name)) {
                name = preferredName + i++;
            }
            FunctionSymbol sym = FunctionSymbol.create(name, arity);
            this.usedNames.add(name);
            this.symToName.put(sym, name);
            return sym;
        }
    }

    public static TransitionProgram toTransitionProgram(CpxIntTrsProblem obl, Abortion aborter) {

        // collect all existing symbols to avoid clashes
        FNG fng = new FNG();
        for (CpxIntTupleRule rule : obl.getK().keySet()) {
            fng.getName(rule.getLeft().getRootSymbol());
            for (TRSFunctionApplication r : rule.getRights()) {
                fng.getName(r.getRootSymbol());
            }
        }
        FunctionSymbol endsym = fng.getFreshSymbol("end", 0);
        TRSFunctionApplication end =
            TRSTerm.createFunctionApplication(CpxIntTermHelper.fCOM1, TRSTerm.createFunctionApplication(endsym));

        // simplify all rules (possibly introducing new states)
        LinkedHashSet<CpxIntTupleRule> rules = new LinkedHashSet<>();
        for (CpxIntTupleRule r_raw : obl.getK().keySet()) {
            LinkedHashSet<CpxIntTupleRule> r;
            try {
                r = CpxIntTrsNormalizer.normalizeRule(r_raw, fng, end);
            } catch (NotRepresentableAsPolynomialException e) {
                throw new RuntimeException(e);
            }
            rules.addAll(r);
        }

        // all start symbols
        LinkedHashSet<FunctionSymbol> g = new LinkedHashSet<>();
        g.addAll(obl.getG());

        // gather some statistics
        int maxArity = 0;
        int maxFreeVariables = 0;
        LinkedHashSet<FunctionSymbol> usedStartSyms = new LinkedHashSet<>();
        boolean transitionToStartSym = false;
        for (CpxIntTupleRule r : rules) {
            FunctionSymbol fs = r.getLeft().getRootSymbol();
            if (g.contains(fs)) {
                usedStartSyms.add(fs);
            }
            int arity = fs.getArity();
            maxArity = Math.max(maxArity, arity);
            int lhsVars = r.getLeft().getVariables().size();
            int allVars = r.getVariables().size();
            assert allVars >= lhsVars;
            maxFreeVariables = Math.max(maxFreeVariables, allVars - lhsVars);
            for (TRSFunctionApplication rhs : r.getRights()) {
                FunctionSymbol rhsfs = rhs.getRootSymbol();
                maxArity = Math.max(maxArity, rhsfs.getArity());
                if (g.contains(rhsfs)) {
                    transitionToStartSym = true;
                }
            }
        }

        ArrayList<TRSVariable> normalVariables = new ArrayList<>();
        for (int i = 0; i < maxArity; ++i) {
            normalVariables.add(TRSTerm.createVariable("X" + i));
        }
        ArrayList<TRSVariable> freshVariables = new ArrayList<>();
        for (int i = 0; i < maxFreeVariables; ++i) {
            freshVariables.add(TRSTerm.createVariable("Y" + i));
        }

        // do we need a separate start symbol?
        if (transitionToStartSym || usedStartSyms.size() > 1) {
            int arity = 0;
            assert usedStartSyms.size() > 0;
            for (FunctionSymbol sym : usedStartSyms) {
                arity = Math.max(arity, sym.getArity());
            }
            FunctionSymbol startsym = fng.getFreshSymbol("start", arity);
            g.clear();
            g.add(startsym);
            TRSFunctionApplication lhs = CpxIntTrsNormalizer.genDefaultVarFunctionApplication(startsym);
            // build start transitions
            for (FunctionSymbol toSym : usedStartSyms) {
                TRSFunctionApplication rhs = CpxIntTrsNormalizer.genDefaultVarFunctionApplication(toSym);
                TRSFunctionApplication rhss = TRSTerm.createFunctionApplication(CpxIntTermHelper.fCOM1, rhs);
                IGeneralizedRule genRule = IGeneralizedRule.create(lhs, rhss, CpxIntTermHelper.TRUE);
                LinkedHashSet<CpxIntTupleRule> rs;
                try {
                    rs = CpxIntTupleRule.createRules(genRule);
                } catch (NoValidCpxIntTupleRuleException e) {
                    throw new RuntimeException(e);
                }
                assert rs.size() == 1;
                rules.addAll(rs);
            }
        }

        assert g.size() == 1;

        LinkedHashSet<Transition> transitions = new LinkedHashSet<>();
        String startState = fng.getName(g.iterator().next());

        // convert rules to transitions
        for (CpxIntTupleRule rule : rules) {
            Map<TRSVariable, TRSVariable> normalizedVarsToOrigVars = new LinkedHashMap<>();
            // use proper variable names in rule
            {
                TRSFunctionApplication lhs = rule.getLeft();
                // build substitution
                LinkedHashMap<TRSVariable, TRSTerm> rawSigma = new LinkedHashMap<>();
                for (int i = 0, l = lhs.getArguments().size(); i < l; ++i) {
                    TRSTerm x = lhs.getArgument(i);
                    assert x.isVariable();
                    TRSVariable normalizedVar = normalVariables.get(i);
                    rawSigma.put((TRSVariable) x, normalizedVar);
                    normalizedVarsToOrigVars.put(normalizedVar, (TRSVariable) x);
                }
                LinkedHashSet<TRSVariable> freeVars = new LinkedHashSet<>(rule.getVariables());
                freeVars.removeAll(lhs.getVariables());
                {
                    int i = 0;
                    for (TRSVariable x : freeVars) {
                        TRSVariable t = freshVariables.get(i++);
                        rawSigma.put(x, t);
                        normalizedVarsToOrigVars.put(t, x);
                    }
                }
                TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(rawSigma));
                try {
                    rule = rule.applySubstitution(sigma);
                } catch (NoConstraintTermException e) {
                    throw new RuntimeException(e);
                }
            }

            // build transition
            TRSFunctionApplication lhs = rule.getLeft();
            String start = fng.getName(lhs.getRootSymbol());

            ArrayList<String> ends = new ArrayList<>();
            for (TRSFunctionApplication rhs : rule.getRights()) {
                ends.add(fng.getName(rhs.getRootSymbol()));
            }

            LinkedHashSet<Pair<SimplePolynomial, Op>> guard = new LinkedHashSet<>();
            ConstraintInformation ci = rule.getConstraintInformation();

            // in the normalized rule, all contraints are guards!
            for (Constraint c : ci.getConstraints()) {
                Pair<SimplePolynomial, Op> polOp;
                try {
                    polOp = c.getPolynomialRepresentation();
                } catch (NotRepresentableAsPolynomialException e) {
                    throw new RuntimeException(e);
                }
                guard.add(polOp);
            }

            // build actions (and check for consistency...)
            LinkedHashMap<String, SimplePolynomial> action = new LinkedHashMap<>();

            LinkedHashSet<String> freshVars = new LinkedHashSet<>();
            Set<TRSVariable> v = rule.getVariables();
            v.removeAll(lhs.getVariables());
            for (TRSVariable x : v) {
                freshVars.add(x.getName());
            }
            for (TRSFunctionApplication rhs : rule.getRights()) {
                ImmutableList<TRSTerm> args = rhs.getArguments();
                for (int i = 0, l = args.size(); i < l; ++i) {
                    TRSVariable x = normalVariables.get(i);
                    assert x != null;
                    TRSTerm t = args.get(i);
                    SimplePolynomial p;
                    try {
                        p = CpxIntTermHelper.toSimplePolynomial(t);
                    } catch (NotRepresentableAsPolynomialException e) {
                        throw new RuntimeException(e);
                    }

                    String name = x.getName();
                    if (action.containsKey(name)) {
                        SimplePolynomial oldP = action.get(name);
                        assert p.equals(oldP);
                    }
                    action.put(name, p);
                }
            }

            {
                // remove noop actions
                Iterator<Entry<String, SimplePolynomial>> it = action.entrySet().iterator();
                while (it.hasNext()) {
                    Entry<String, SimplePolynomial> e = it.next();
                    if (e.getValue().equals(SimplePolynomial.create(e.getKey()))) {
                        it.remove();
                    }
                }
            }

            transitions.add(new TransitionProgram.Transition(start,
                    ImmutableCreator.create(ends),
                    ImmutableCreator.create(guard),
                    ImmutableCreator.create(action),
                    ImmutableCreator.create(freshVars),
                    ImmutableCreator.create(normalizedVarsToOrigVars)));
        }

        TransitionProgram tp = new TransitionProgram(ImmutableCreator.create(transitions), startState);

        return tp;
    }

    private static TRSFunctionApplication genDefaultVarFunctionApplication(FunctionSymbol fs) {
        ArrayList<TRSTerm> args = new ArrayList<>();
        for (int i = 0, l = fs.getArity(); i < l; ++i) {
            args.add(TRSTerm.createVariable("X" + i));
        }
        return TRSTerm.createFunctionApplication(fs, args);
    }

    private static
        LinkedHashSet<CpxIntTupleRule>
        normalizeRule(CpxIntTupleRule r_raw, FNG fng, TRSFunctionApplication end)
            throws NotRepresentableAsPolynomialException
    {
        FreshNameGenerator varfng = new FreshNameGenerator(r_raw.getVariables(), FreshNameGenerator.VARIABLES);
        try {
            r_raw = CpxIntTrsNormalizer.replaceDivAndMod(r_raw, varfng, end);
        } catch (NoValidCpxIntTupleRuleException | NoConstraintTermException e1) {
            throw new RuntimeException(e1);
        }

        TRSSubstitution sigma =
            r_raw.getConstraintInformation().computeSimplifyingSubstitution(r_raw.getLeft().getVariables());
        CpxIntTupleRule r;
        try {
            r = r_raw.applySubstitution(sigma);
        } catch (NoConstraintTermException e) {
            throw new RuntimeException(e);
        }

        boolean intermediateState = false;
        if (r.getRights().size() > 1) {
            Map<Integer, SimplePolynomial> action = new LinkedHashMap<>();
            for (TRSFunctionApplication rhs : r.getRights()) {
                ImmutableList<TRSTerm> args = rhs.getArguments();
                for (int i = 0, l = args.size(); i < l; ++i) {
                    TRSTerm t = args.get(i);
                    SimplePolynomial p = CpxIntTermHelper.toSimplePolynomial(t);

                    if (action.containsKey(i)) {
                        SimplePolynomial oldP = action.get(i);
                        if (!p.equals(oldP)) {
                            intermediateState = true;
                        }
                    }
                    action.put(i, p);
                }
            }
        }

        LinkedHashSet<CpxIntTupleRule> rv = new LinkedHashSet<>();
        if (intermediateState) {
            TRSFunctionApplication lhs = r.getLeft();
            ArrayList<TRSTerm> args = new ArrayList<>();
            args.addAll(r.getRight().getVariables());
            int arity = args.size();
            ArrayList<TRSFunctionApplication> rhss = new ArrayList<>();
            for (TRSFunctionApplication rhs : r.getRights()) {
                TRSFunctionApplication newrhs =
                    TRSTerm.createFunctionApplication(
                        fng.getFreshSymbol(FNG.getSaveStateName(lhs.getRootSymbol()), arity),
                        args);
                rhss.add(newrhs);
                IGeneralizedRule igrule =
                    IGeneralizedRule.create(newrhs, CpxIntTermHelper.createCom(rhs), CpxIntTermHelper.TRUE);
                try {
                    LinkedHashSet<CpxIntTupleRule> interRule = CpxIntTupleRule.createRules(igrule);
                    assert interRule.size() == 1;
                    rv.addAll(interRule);
                } catch (NoValidCpxIntTupleRuleException e) {
                    throw new RuntimeException(e);
                }
            }
            IGeneralizedRule igrule =
                IGeneralizedRule.create(lhs, CpxIntTermHelper.createCom(rhss), r.getConstraintTerm());
            try {
                rv.addAll(CpxIntTupleRule.createRules(igrule));
            } catch (NoValidCpxIntTupleRuleException e) {
                e.printStackTrace();
            }
        } else {
            rv.add(r);
        }
        return rv;
    }

    private static CpxIntTupleRule replaceDivAndMod(CpxIntTupleRule r, FreshNameGenerator fv, TRSFunctionApplication end)
        throws NoValidCpxIntTupleRuleException,
            NoConstraintTermException
    {
        TRSFunctionApplication lhs = r.getLeft();
        LinkedHashSet<Constraint> constraints = new LinkedHashSet<>();
        TRSTerm rhs = r.getRights().size() == 0 ? end : CpxIntTrsNormalizer.replaceDivAndMod(r.getRight(), fv, constraints);

        IGeneralizedRule igrule = IGeneralizedRule.create(lhs, rhs, CpxIntTermHelper.TRUE);

        for (Constraint c : r.getConstraints()) {
            TRSFunctionApplication t = c.getConstraintTerm();
            TRSTerm s = CpxIntTrsNormalizer.replaceDivAndMod(t, fv, constraints);
            try {
                constraints.add(Constraint.create((TRSFunctionApplication) s));
            } catch (NoConstraintTermException e) {
                throw new RuntimeException(e);
            }
        }

        LinkedHashSet<CpxIntTupleRule> rules;
        rules = CpxIntTupleRule.createRules(igrule, ImmutableCreator.create(constraints));

        assert rules.size() == 1;

        return rules.iterator().next();
    }

    private static TRSTerm replaceDivAndMod(TRSTerm t, FreshNameGenerator fv, LinkedHashSet<Constraint> constraints)
        throws NoConstraintTermException
    {
        if (t.isVariable()) {
            return t;
        }
        TRSFunctionApplication fa = (TRSFunctionApplication) t;
        FunctionSymbol fs = fa.getRootSymbol();

        ArrayList<TRSTerm> args = new ArrayList<>();
        for (TRSTerm tsub : fa.getArguments()) {
            args.add(CpxIntTrsNormalizer.replaceDivAndMod(tsub, fv, constraints));
        }

        if (CpxIntTermHelper.fMod.equals(fs)) {
            TRSTerm x = args.get(0);
            TRSTerm y = args.get(1);
            TRSVariable w = TRSTerm.createVariable(fv.getFreshName("w", false));
            TRSVariable z = TRSTerm.createVariable(fv.getFreshName("z", false));
            constraints.add(Constraint.create(TRSTerm.createFunctionApplication(
                CpxIntTermHelper.fGe,
                z,
                CpxIntTermHelper.ZERO)));
            constraints.add(Constraint.create(TRSTerm.createFunctionApplication(CpxIntTermHelper.fLt, z, y)));
            TRSFunctionApplication zPlusWTimesY =
                TRSTerm.createFunctionApplication(
                    CpxIntTermHelper.fAdd,
                    z,
                    TRSTerm.createFunctionApplication(CpxIntTermHelper.fMul, w, y));
            constraints.add(Constraint.create(TRSTerm.createFunctionApplication(CpxIntTermHelper.fEq, zPlusWTimesY, x)));
            return z;
        }

        if (CpxIntTermHelper.fDiv.equals(fs)) {
            TRSTerm x = args.get(0);
            TRSTerm y = args.get(1);
            TRSVariable z = TRSTerm.createVariable(fv.getFreshName("z", false));

            TRSFunctionApplication zTimesY = TRSTerm.createFunctionApplication(CpxIntTermHelper.fMul, z, y);
            constraints.add(Constraint.create(TRSTerm.createFunctionApplication(CpxIntTermHelper.fLe, zTimesY, x)));

            TRSFunctionApplication zTimesYPlusOne =
                TRSTerm.createFunctionApplication(
                    CpxIntTermHelper.fMul,
                    z,
                    TRSTerm.createFunctionApplication(CpxIntTermHelper.fAdd, y, CpxIntTermHelper.ONE));
            constraints.add(Constraint.create(TRSTerm.createFunctionApplication(CpxIntTermHelper.fGt, zTimesYPlusOne, x)));

            return z;
        }

        return TRSTerm.createFunctionApplication(fs, args);
    }

    public static void main(String[] args) {
        for (String filename : args) {
            System.out.println(filename);
            String ext = filename.substring(filename.length() - 5);
            assert ".cint".equals(ext);
            String filenameFST = filename.substring(0, filename.length() - 5) + ".fst";
            String filenameCES = filename.substring(0, filename.length() - 5) + ".ces";
            String filenameKOAT = filename.substring(0, filename.length() - 5) + ".koat";
            String filenameProperties = filename.substring(0, filename.length() - 5) + ".properties";

            Translator t = new Translator();
            try {
                File f = new File(filename);
                t.translate(f);
            } catch (FileNotFoundException | TranslationException e) {
                throw new RuntimeException(e);
            }

            Object obl = t.getState();
            assert obl instanceof CpxIntTrsProblem;
            CpxIntTrsProblem c = (CpxIntTrsProblem) obl;
            TransitionProgram tp = CpxIntTrsNormalizer.toTransitionProgram(c, AbortionFactory.create());
            assert tp != null;

            tp = tp.normalizeVars(); // magic

            System.out.println(filename);
            System.out.println(" --> " + filenameFST);
            CpxIntTrsNormalizer.writeFSTFile(filenameFST, tp);
            System.out.println(" --> " + filenameCES);
            CpxIntTrsNormalizer.writeCESFile(filenameCES, tp);
            System.out.println(" --> " + filenameKOAT);
            CpxIntTrsNormalizer.writeKOATFile(filenameKOAT, tp);
            System.out.println(" --> " + filenameProperties);
            CpxIntTrsNormalizer.writeProperties(filenameProperties, tp);
        }
    }

    private static void writeProperties(String filenameProperties, TransitionProgram tp) {
        StringBuilder sb = new StringBuilder();
        sb.append("'recursive': ");
        if (tp.isRecursive()) {
            sb.append("true, ");
        } else {
            sb.append("false, ");
        }
        sb.append("'nonlinear': ");
        if (tp.isNonlinear()) {
            sb.append("true, ");
        } else {
            sb.append("false, ");
        }
        try {
            FileWriter fw = new FileWriter(new File(filenameProperties));
            fw.write(sb.toString());
            fw.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private static void writeCESFile(String filenameCES, TransitionProgram tp) {
        StringBuilder sb = new StringBuilder();
        tp.toCES(sb);
        try {
            FileWriter fw = new FileWriter(new File(filenameCES));
            fw.write(sb.toString());
            fw.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private static void writeKOATFile(String filenameKOAT, TransitionProgram tp) {
        StringBuilder sb = new StringBuilder();
        tp.toKOAT(sb);
        try {
            FileWriter fw = new FileWriter(new File(filenameKOAT));
            fw.write(sb.toString());
            fw.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    private static void writeFSTFile(String filenameFST, TransitionProgram tp) {
        StringBuilder sb = new StringBuilder();
        try {
            tp.toFST(sb);
        } catch (COMkException e1) {
            System.out.println("Skipping due to Com_k with k > 1.");
            return;
        }
        try {
            FileWriter fw = new FileWriter(new File(filenameFST));
            fw.write(sb.toString());
            fw.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}
