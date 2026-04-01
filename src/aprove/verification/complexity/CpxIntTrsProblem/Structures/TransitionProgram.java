package aprove.verification.complexity.CpxIntTrsProblem.Structures;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Something that should be compatible with SAS10, PUBS/COSTA and CINT.
 * <p>Features hyper transitions, which are not supported by SAS10,
 * and can represent non-linear stuff, which is supported by neither COSTA nor SAS10.
 * <p>
 * No transitions to the start state are allowed.
 *
 */
public class TransitionProgram implements Immutable {
    public static enum Op {
        GreaterEqual, Equal
    };

    public static class Transition implements Immutable {
        private final String start;
        private final ImmutableArrayList<String> end;
        private final ImmutableLinkedHashSet<Pair<SimplePolynomial, Op>> guard;
        private final ImmutableLinkedHashMap<String, SimplePolynomial> action;
        private final ImmutableLinkedHashSet<String> freeVariables; // variables that are to be considered Free
        private final ImmutableMap<TRSVariable, TRSVariable> normalizedVarsToOrigVars;

        public Transition(
            String start,
            ImmutableArrayList<String> end,
            ImmutableLinkedHashSet<Pair<SimplePolynomial, Op>> guard,
            ImmutableLinkedHashMap<String, SimplePolynomial> action,
            ImmutableLinkedHashSet<String> freeVariables,
            ImmutableMap<TRSVariable, TRSVariable> normalizedVarsToOrigVars)
        {
            assert start != null && end != null && guard != null && action != null;
            if (end.size() == 0) {
                throw new RuntimeException("Empty end list in transition");
            }

            // TODO don't allow trivial guards

            // don't allow trivial actions
            for (Entry<String, SimplePolynomial> e : action.entrySet()) {
                String x = e.getKey();
                assert !freeVariables.contains(x); // dont allow updates on Free variables
                SimplePolynomial p = e.getValue();
                SimplePolynomial p2 = SimplePolynomial.create(x);
                if (p2.equals(p)) {
                    throw new RuntimeException("Transition must not contain trivial action.");
                }
            }

            this.start = start;
            this.end = end;
            this.guard = guard;
            this.action = action;
            this.freeVariables = freeVariables;
            this.normalizedVarsToOrigVars = normalizedVarsToOrigVars;
        }

        public ImmutableLinkedHashMap<String, SimplePolynomial> getAction() {
            return this.action;
        }

        public ImmutableArrayList<String> getEnd() {
            return this.end;
        }

        public ImmutableLinkedHashSet<Pair<SimplePolynomial, Op>> getGuard() {
            return this.guard;
        }

        public String getStart() {
            return this.start;
        }

        public LinkedHashSet<String> getAllVariables() {
            LinkedHashSet<String> vars = new LinkedHashSet<>();

            for (Pair<SimplePolynomial, Op> g : this.guard) {
                vars.addAll(g.x.getIndefinites());
            }

            for (Entry<String, SimplePolynomial> e : this.action.entrySet()) {
                vars.add(e.getKey());
                vars.addAll(e.getValue().getIndefinites());
            }

            return vars;
        }

        public LinkedHashSet<String> getNormalVariables() {
            LinkedHashSet<String> vars = this.getAllVariables();
            vars.removeAll(this.freeVariables);
            return vars;
        }

        public Transition renameVariables(Map<String, String> subst) {
            LinkedHashSet<String> range = new LinkedHashSet<>();
            range.addAll(subst.values());
            assert subst.keySet().containsAll(this.getAllVariables());
            assert range.size() == subst.size();

            Map<String, SimplePolynomial> polySubst = new LinkedHashMap<>();
            for (Entry<String, String> e : subst.entrySet()) {
                polySubst.put(e.getKey(), SimplePolynomial.create(e.getValue()));
            }

            LinkedHashSet<Pair<SimplePolynomial, Op>> newGuard = new LinkedHashSet<>();
            for (Pair<SimplePolynomial, Op> g : this.guard) {
                newGuard.add(new Pair<>(g.x.substitute(polySubst), g.y));
            }
            LinkedHashMap<String, SimplePolynomial> newAction = new LinkedHashMap<>();
            for (Entry<String, SimplePolynomial> a : this.action.entrySet()) {
                newAction.put(subst.get(a.getKey()), a.getValue().substitute(polySubst));
            }

            LinkedHashSet<String> newFreeVariables = new LinkedHashSet<>();
            for (String x : this.freeVariables) {
                newFreeVariables.add(subst.get(x));
            }

            Map<TRSVariable, TRSVariable> newNormalizedVarsToOrigVars = new LinkedHashMap<>();
            for (Entry<String, String> e: subst.entrySet()) {
                String oldName = e.getKey();
                String newName = e.getValue();
                TRSVariable origVar = normalizedVarsToOrigVars.get(TRSTerm.createVariable(oldName));
                if (origVar != null) {
                    newNormalizedVarsToOrigVars.put(TRSTerm.createVariable(newName), origVar);
                }
            }

            Transition t =
                new Transition(
                    this.start,
                    this.end,
                    ImmutableCreator.create(newGuard),
                    ImmutableCreator.create(newAction),
                    ImmutableCreator.create(newFreeVariables),
                    ImmutableCreator.create(newNormalizedVarsToOrigVars));

            assert range.containsAll(t.getAllVariables());

            return t;
        }
    }

    private final ImmutableLinkedHashSet<Transition> transitions;
    private final String startState;

    public boolean isRecursive() {
        for (Transition t : this.getTransitions()) {
            if (t.getEnd().size() > 1) {
                return true;
            }
        }
        return false;
    }

    public TransitionProgram(ImmutableLinkedHashSet<Transition> transitions, String startState) {
        for (Transition t : transitions) {
            if (t.getEnd().contains(startState)) {
                throw new RuntimeException("Transitions must not lead to start state.");
            }
        }

        this.transitions = transitions;
        this.startState = startState;
    }

    public ImmutableLinkedHashSet<Transition> getTransitions() {
        return this.transitions;
    }

    public String getStartState() {
        return this.startState;
    }

    public void toFST(StringBuilder sb) throws COMkException {
        int maxFreeVariables = 0;
        for (Transition t : this.transitions) {
            maxFreeVariables = Math.max(maxFreeVariables, t.freeVariables.size());
        }

        LinkedHashSet<String> unorderedNormalVars = this.getNormalVariables();
        ArrayList<String> rvars = new ArrayList<>();
        int varIndex = 0;
        for (int l = unorderedNormalVars.size(); varIndex < l; ++varIndex) {
            String v = this.getVarNo(varIndex);
            assert unorderedNormalVars.contains(v);
            rvars.add(v);
        }

        LinkedHashSet<String> unorderedFreeVariables = this.getFreeVariables();
        LinkedHashSet<String> freeVariables = new LinkedHashSet<>();
        for (int l = varIndex + unorderedFreeVariables.size(); varIndex < l; ++varIndex) {
            String v = this.getVarNo(varIndex);
            assert unorderedFreeVariables.contains(v);
            freeVariables.add(v);
        }

        sb.append("model main {\n");
        boolean first = true;

        sb.append("  var");
        for (String x : this.getNormalVariables()) {
            if (first) {
                sb.append(" ");
                first = false;
            } else {
                sb.append(", ");
            }
            sb.append(x);
        }
        for (String x : freeVariables) {
            if (first) {
                sb.append(" ");
                first = false;
            } else {
                sb.append(", ");
            }
            sb.append(x);
        }
        sb.append(";\n");

        first = true;
        sb.append("  states");
        for (String s : this.getStates()) {
            if (first) {
                sb.append(" ");
                first = false;
            } else {
                sb.append(", ");
            }
            sb.append(s);
        }
        sb.append(";\n");

        int ti = 0;
        for (Transition transition : this.transitions) {
            if (transition.end.size() != 1) {
                //                sb.append("  // More than one endpoint detected..." + transition.end.toString() + "\n");
                //                throw new RuntimeException("FST only allows one endpoint in transitions.");
                throw new COMkException();
            }
            sb.append("  transition t" + ti++ + " := {\n");
            sb.append("    from   := " + transition.start + ";\n");
            sb.append("    to     := " + transition.end.get(0) + ";\n");
            sb.append("    guard  := ");
            if (transition.guard.size() == 0) {
                sb.append("true");
            } else {
                first = true;
                for (Pair<SimplePolynomial, Op> i : transition.guard) {
                    if (first) {
                        first = false;
                    } else {
                        sb.append(" && ");
                    }

                    Pair<SimplePolynomial, SimplePolynomial> posneg = TransitionProgram.splitIntoPosNeg(i.getKey());
                    SimplePolynomial pos = posneg.x;
                    SimplePolynomial neg = posneg.y;

                    TransitionProgram.exportNicePolynomial(sb, pos);
                    switch (i.getValue()) {
                    case Equal:
                        sb.append(" = ");
                        break;
                    case GreaterEqual:
                        BigInteger e = neg.getSimpleMonomials().get(IndefinitePart.ONE);
                        if (e != null && BigInteger.ZERO.compareTo(e) < 0) {
                            neg = neg.minus(SimplePolynomial.ONE);
                            sb.append(" > ");
                        } else {
                            sb.append(" >= ");
                        }
                        break;
                    }
                    TransitionProgram.exportNicePolynomial(sb, neg);
                }
            }
            sb.append(";\n");
            sb.append("    action := ");
            first = true;
            for (Entry<String, SimplePolynomial> i : transition.action.entrySet()) {
                if (first) {
                    first = false;
                } else {
                    sb.append(", ");
                }

                String x = i.getKey();
                assert !freeVariables.contains(x);
                sb.append(x + "' = ");
                SimplePolynomial p = i.getValue();
                TransitionProgram.exportNicePolynomial(sb, p);
            }
            for (String x : freeVariables) {
                if (first) {
                    first = false;
                } else {
                    sb.append(", ");
                }
                sb.append(x + "' = ?");
            }
            sb.append(";\n");
            sb.append("  };\n");
        }
        sb.append("}\n");

        sb.append("strategy dumb {\n");
        sb.append("  Region init := { state = " + this.startState + " };\n");
        sb.append("}\n");
    }

    /**
     * Returns a pair of two polynomials {@code a} and {@code b} with only positive coefficients,
     * such that {@code a - b = p}.
     * @param p
     * @return
     */
    private static Pair<SimplePolynomial, SimplePolynomial> splitIntoPosNeg(SimplePolynomial p) {
        Map<IndefinitePart, BigInteger> posMonomials = new LinkedHashMap<>();
        Map<IndefinitePart, BigInteger> negMonomials = new LinkedHashMap<>();

        for (Entry<IndefinitePart, BigInteger> e : p.getSimpleMonomials().entrySet()) {
            BigInteger coeff = e.getValue();
            if (coeff.compareTo(BigInteger.ZERO) > 0) {
                posMonomials.put(e.getKey(), coeff);
            } else {
                negMonomials.put(e.getKey(), coeff.negate());
            }
        }

        SimplePolynomial pos = SimplePolynomial.create(posMonomials);
        SimplePolynomial neg = SimplePolynomial.create(negMonomials);

        assert p.equals(pos.minus(neg));
        return new Pair<>(pos, neg);
    }

    private static void exportNicePolynomial(StringBuilder sb, SimplePolynomial p) {
        assert p != null;
        BigInteger b = p.getConstantSize();
        if (b != null) {
            sb.append(b.toString());
            return;
        }
        boolean first = true;
        for (Entry<IndefinitePart, BigInteger> e : p.getSimpleMonomials().entrySet()) {
            IndefinitePart indef = e.getKey();
            BigInteger coeff = e.getValue();

            if (first) {
                first = false;
                if (coeff.compareTo(BigInteger.ZERO) < 0) {
                    sb.append("-");
                    coeff = coeff.negate();
                }
            } else {
                if (coeff.compareTo(BigInteger.ZERO) < 0) {
                    sb.append(" - ");
                    coeff = coeff.negate();
                } else {
                    sb.append(" + ");
                }
            }

            boolean firstIndef = false;
            if (coeff.equals(BigInteger.ONE) && !indef.isEmpty()) {
                firstIndef = true;
            } else {
                sb.append(coeff.toString());
            }
            for (Entry<String, Integer> exp : indef.getExponents().entrySet()) {
                String x = exp.getKey();
                for (int i = 0, l = exp.getValue(); i < l; ++i) {
                    if (firstIndef) {
                        firstIndef = false;
                    } else {
                        sb.append('*');
                    }
                    sb.append(x);
                }
            }
        }
    }

    public LinkedHashSet<String> getNormalVariables() {
        LinkedHashSet<String> vars = new LinkedHashSet<>();
        for (Transition t : this.transitions) {
            vars.addAll(t.getNormalVariables());
        }
        return vars;
    }

    public LinkedHashSet<String> getAllVariables() {
        LinkedHashSet<String> vars = new LinkedHashSet<>();
        for (Transition t : this.transitions) {
            vars.addAll(t.getAllVariables());
        }
        return vars;
    }

    private LinkedHashSet<String> getStates() {
        LinkedHashSet<String> states = new LinkedHashSet<>();
        for (Transition t : this.transitions) {
            states.add(t.getStart());
            states.addAll(t.getEnd());
        }
        return states;
    }

    private static String join(Iterable<String> parts, String sep) {
        StringBuilder sb = new StringBuilder();
        boolean first = true;
        for (String part : parts) {
            if (first) {
                first = false;
            } else {
                sb.append(sep);
            }
            sb.append(part);
        }
        return sb.toString();
    }

    // name variables in style of PUBS
    String getVarNo(int no) {
        // yay! eclipse formatter!
        String[] vars =
            {
                "A",
                "B",
                "C",
                "D",
                "E",
                "F",
                "G",
                "H",
                "I",
                "J",
                "K",
                "L",
                "M",
                "N",
                "O",
                "P",
                "Q",
                "R",
                "S",
                "T",
                "U",
                "V",
                "W",
                "X",
                "Y",
                "Z" };
        int index = no % vars.length;
        int i = no / vars.length;
        return i == 0 ? vars[index] : vars[index] + i;
    }

    public TransitionProgram normalizeVars() {
        LinkedHashSet<String> normalVars = this.getNormalVariables();
        LinkedHashSet<String> freeVars = this.getFreeVariables();

        Map<String, String> subst = new LinkedHashMap<>();

        int i = 0;
        for (String x : normalVars) {
            subst.put(x, this.getVarNo(i++));
        }
        for (String x : freeVars) {
            subst.put(x, this.getVarNo(i++));
        }

        LinkedHashSet<Transition> newTransitions = new LinkedHashSet<>();
        for (Transition t : this.transitions) {
            newTransitions.add(t.renameVariables(subst));
        }
        return new TransitionProgram(ImmutableCreator.create(newTransitions), this.startState);
    }

    private LinkedHashSet<String> getFreeVariables() {
        LinkedHashSet<String> rv = this.getAllVariables();
        rv.removeAll(this.getNormalVariables());
        return rv;
    }

    public void toCES(StringBuilder sb) {
        // CES has no start state, but a start transition
        LinkedHashSet<String> st = this.getStates();
        String startName = "pubs_start";
        {
            int i = 0;
            while (st.contains(startName)) {
                startName = "pubs_start" + i++;
            }
        }

        LinkedHashSet<String> unorderedVars = this.getNormalVariables();
        LinkedHashSet<String> vars = new LinkedHashSet<>();
        for (int i = 0, l = unorderedVars.size(); i < l; ++i) {
            vars.add(this.getVarNo(i));
        }

        assert vars.equals(unorderedVars);

        String varsString = TransitionProgram.join(vars, ",");

        // create start transition without costs
        sb.append("eq(" + startName + "(" + varsString + "),0,[" + this.startState + "(" + varsString + ")],[]).\n");

        for (Transition transition : this.transitions) {
            sb.append("eq(" + transition.start + "(" + varsString + "),1,[");
            ArrayList<String> actions = new ArrayList<>();
            for (String var : vars) {
                SimplePolynomial act = transition.action.get(var);
                if (act == null) {
                    actions.add(var);
                } else {
                    StringBuilder s = new StringBuilder();
                    TransitionProgram.exportNicePolynomial(s, act);
                    actions.add(s.toString());
                }
            }
            String allActions = TransitionProgram.join(actions, ",");
            boolean first = true;
            for (String end : transition.end) {
                if (first) {
                    first = false;
                } else {
                    sb.append(",");
                }
                sb.append(end + "(" + allActions + ")");
            }
            sb.append("],[");

            first = true;
            for (Pair<SimplePolynomial, Op> i : transition.guard) {
                if (first) {
                    first = false;
                } else {
                    sb.append(", ");
                }
                Pair<SimplePolynomial, SimplePolynomial> posneg = TransitionProgram.splitIntoPosNeg(i.getKey());
                SimplePolynomial pos = posneg.x;
                SimplePolynomial neg = posneg.y;
                TransitionProgram.exportNicePolynomial(sb, pos);
                switch (i.getValue()) {
                case Equal:
                    sb.append(" = ");
                    break;
                case GreaterEqual:
                    sb.append(" >= ");
                    break;
                }
                TransitionProgram.exportNicePolynomial(sb, neg);
            }

            sb.append("]).\n");

        }
    }

    public void toKOAT(StringBuilder sb) {
        int maxFreeVariables = 0;
        for (Transition t : this.transitions) {
            maxFreeVariables = Math.max(maxFreeVariables, t.freeVariables.size());
        }

        LinkedHashSet<String> unorderedNormalVars = this.getNormalVariables();
        ArrayList<TRSVariable> rvars = new ArrayList<>();
        int varIndex = 0;
        for (int l = unorderedNormalVars.size(); varIndex < l; ++varIndex) {
            String v = this.getVarNo(varIndex);
            assert unorderedNormalVars.contains(v);
            rvars.add(TRSTerm.createVariable(v));
        }
        ImmutableArrayList<TRSVariable> vars = ImmutableCreator.create(rvars);

        LinkedHashSet<String> unorderedFreeVariables = this.getFreeVariables();
        LinkedHashSet<TRSVariable> freeVariables = new LinkedHashSet<>();
        for (int l = varIndex + unorderedFreeVariables.size(); varIndex < l; ++varIndex) {
            String v = this.getVarNo(varIndex);
            assert unorderedFreeVariables.contains(v);
            freeVariables.add(TRSTerm.createVariable(v));
        }

        String varsString = "";
        sb.append("(GOAL COMPLEXITY)\n");
        sb.append("(STARTTERM (FUNCTIONSYMBOLS " + this.startState + "))\n");
        sb.append("(VAR");
        for (TRSVariable x : vars) {
            if (varsString.isEmpty()) {
                varsString = "";
            } else {
                varsString += ",";
            }
            varsString += x.getName();
            sb.append(" ");
            sb.append(x.getName());
        }
        for (TRSVariable x : freeVariables) {
            sb.append(" " + x);
        }
        sb.append(")\n");

        sb.append("(RULES\n");
        for (Transition transition : this.transitions) {

            sb.append("  " + transition.start + "(" + varsString + ") -> ");
            ArrayList<String> actions = new ArrayList<>();
            for (TRSVariable var : vars) {
                SimplePolynomial act = transition.action.get(var.getName());
                if (act == null) {
                    actions.add(var.getName());
                } else {
                    StringBuilder s = new StringBuilder();
                    TransitionProgram.exportNicePolynomial(s, act);
                    actions.add(s.toString());
                }
            }
            String allActions = TransitionProgram.join(actions, ",");
            boolean first = true;
            sb.append("Com_" + transition.end.size() + "(");
            for (String end : transition.end) {
                if (first) {
                    first = false;
                } else {
                    sb.append(",");
                }
                sb.append(end + "(" + allActions + ")");
            }
            sb.append(")");

            first = true;
            for (Pair<SimplePolynomial, Op> i : transition.guard) {
                if (first) {
                    first = false;
                    sb.append(" :|: ");
                } else {
                    sb.append(" && ");
                }
                Pair<SimplePolynomial, SimplePolynomial> posneg = TransitionProgram.splitIntoPosNeg(i.getKey());
                SimplePolynomial pos = posneg.x;
                SimplePolynomial neg = posneg.y;
                TransitionProgram.exportNicePolynomial(sb, pos);
                switch (i.getValue()) {
                case Equal:
                    sb.append(" = ");
                    break;
                case GreaterEqual:
                    sb.append(" >= ");
                    break;
                }
                TransitionProgram.exportNicePolynomial(sb, neg);
            }

            sb.append("\n");

            //
            //
            //
            //            FunctionSymbol start = FunctionSymbol.create(transition.start, arity);
            //            FunctionApplication lhs = Term.createFunctionApplication(start, vars);
            //
            //            ArrayList<FunctionApplication> rhss = new ArrayList<>();
            //
            //            for (String end : transition.end) {
            //                FunctionSymbol fs = FunctionSymbol.create(end, arity);
            //                ArrayList<Term> args = new ArrayList<>();
            //                for (Variable x : vars) {
            //                    String name = x.getName();
            //                    Term t = x;
            //                    SimplePolynomial act = transition.action.get(name);
            //                    if (act != null) {
            //                        t = CpxIntTermHelper.fromSimplePolynomial(act);
            //                    }
            //                    args.add(t);
            //                }
            //                FunctionApplication rhs = Term.createFunctionApplication(fs, args);
            //                rhss.add(rhs);
            //            }
            //            FunctionApplication rhs = CpxIntTermHelper.createCom(rhss);
            //
            //            Term condterm = null;
            //
            //            for (Pair<SimplePolynomial, Op> guard : transition.guard) {
            //
            //                Pair<SimplePolynomial, SimplePolynomial> posneg = splitIntoPosNeg(guard.getKey());
            //                SimplePolynomial pos = posneg.x;
            //                SimplePolynomial neg = posneg.y;
            //
            //                FunctionSymbol fs = null;
            //                switch (guard.getValue()) {
            //                case Equal:
            //                    fs = CpxIntTermHelper.fEq;
            //                    break;
            //                case GreaterEqual:
            //                    BigInteger e = neg.getSimpleMonomials().get(IndefinitePart.ONE);
            //                    if (e != null && BigInteger.ZERO.compareTo(e) < 0) {
            //                        neg = neg.minus(SimplePolynomial.ONE);
            //                        fs = CpxIntTermHelper.fGt;
            //                    } else {
            //                        fs = CpxIntTermHelper.fGe;
            //                    }
            //                    break;
            //                }
            //                assert fs != null;
            //                FunctionApplication cond =
            //                    Term.createFunctionApplication(
            //                        fs,
            //                        CpxIntTermHelper.fromSimplePolynomial(pos),
            //                        CpxIntTermHelper.fromSimplePolynomial(neg));
            //
            //                if (condterm == null) {
            //                    condterm = cond;
            //                } else {
            //                    condterm = Term.createFunctionApplication(CpxIntTermHelper.fLand, condterm, cond);
            //                }
            //            }
            //
            //            sb.append("\n");
        }
        sb.append(")\n");
    }

    public boolean isNonlinear() {
        for (Transition t : this.getTransitions()) {
            for (Pair<SimplePolynomial, Op> g : t.guard) {
                if (!g.x.isLinear()) {
                    return true;
                }
            }
            for (Entry<String, SimplePolynomial> a : t.action.entrySet()) {
                if (!a.getValue().isLinear()) {
                    return true;
                }
            }
        }
        return false;
    }

    public Map<Transition, Map<TRSVariable, TRSVariable>> getNormalizedVarsToOrigVars() {
        Map<Transition, Map<TRSVariable, TRSVariable>> res = new LinkedHashMap<>();
        for (Transition trans: transitions) {
            res.put(trans, trans.normalizedVarsToOrigVars);
        }
        return res;
    }
}
