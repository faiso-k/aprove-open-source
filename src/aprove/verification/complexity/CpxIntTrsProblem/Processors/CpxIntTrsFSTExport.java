package aprove.verification.complexity.CpxIntTrsProblem.Processors;

import java.io.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

public class CpxIntTrsFSTExport extends CpxIntTrsProcessor {

    @Override
    public Result processCpxIntTrs(
        CpxIntTrsProblem obl,
        BasicObligationNode oblNode,
        Abortion aborter,
        RuntimeInformation rti
    ) throws AbortionException {
        LinkedHashMap<String, FunctionSymbol> syms = new LinkedHashMap<>();
        if (obl.getG().size() != 1) {
            return this.error("Not exactly one start symbol.");
        }
        // compute necessary variables
        Set<CpxIntTupleRule> tuples = obl.getK().keySet();
        int maxArity = 0;
        int maxVarCount = 0;
        Set<CpxIntTupleRule> nice_tuples = new LinkedHashSet<>();
        for (CpxIntTupleRule r_raw : tuples) {
            TRSSubstitution sigma =
                r_raw.getConstraintInformation().computeSimplifyingSubstitution(r_raw.getLeft().getVariables());
            CpxIntTupleRule r;
            try {
                r = r_raw.applySubstitution(sigma);
            } catch (NoConstraintTermException e) {
                return this.error(e.toString());
            }
            nice_tuples.add(r);
        }
        tuples = nice_tuples;
        boolean com0 = false;
        int maxFreeVars = 0;
        for (CpxIntTupleRule r : tuples) {
            // guards must only refer to LHS variables
            Set<TRSVariable> guardVarsWOLhsVars = r.getConstraintTerm().getVariables();
            guardVarsWOLhsVars.removeAll(r.getLeft().getVariables());
            maxFreeVars = Math.max(maxFreeVars, guardVarsWOLhsVars.size());
//            if (!guardVarsWOLhsVars.isEmpty()) {
//                return error("Guards referring to variables not on the LHS.");
//            }
            ArrayList<FunctionSymbol> s = new ArrayList<>();
            s.add(r.getRootSymbol());
            if (r.getRights().size() > 1) {
                return this.error("Com_k with k > 1");
            }
            if (r.getRights().size() == 1) {
                s.add(r.getRights().get(0).getRootSymbol());
            }
            LinkedHashMap<TRSVariable, Integer> lhsVars = new LinkedHashMap<>();
            ImmutableList<TRSTerm> lhsArgs = r.getLeft().getArguments();
            for (int i = 0, l = lhsArgs.size(); i < l; ++i) {
                TRSTerm t = lhsArgs.get(i);
                assert t.isVariable();
                TRSVariable v = (TRSVariable) t;
                assert !lhsVars.containsKey(v);
                lhsVars.put(v, i);
            }
            for (FunctionSymbol fs : s) {
                String name = this.getStateName(fs, syms);
                syms.put(name, fs);
                maxArity = Math.max(maxArity, fs.getArity());
            }
            if (r.getRights().size() == 0) {
                com0 = true;
            }
            maxVarCount = Math.max(maxVarCount, r.getVariables().size());
        }
        FunctionSymbol end = FunctionSymbol.create("end_of_program", 0); // hack hack. this assumes that such a symbol is not used in the system.
        TRSFunctionApplication end_st = TRSTerm.createFunctionApplication(end);
        if (com0) {
            String name = this.getStateName(end, syms);
            syms.put(name, end);
        }
        StringBuilder sb = new StringBuilder();
        sb.append("model main {\n");
        sb.append("  var");
        for (int i = 0; i < maxArity; ++i) {
            if (i != 0) {
                sb.append(',');
            }
            sb.append(" x" + i);
        }
        for (int i = 0; i < maxFreeVars; ++i) {
                sb.append(',');
            sb.append(" g" + i);
        }
        sb.append(";\n");
        sb.append("  states");
        boolean first = true;
        for (String symName : syms.keySet()) {
            if (first) {
                first = false;
            } else {
                sb.append(",");
            }
            sb.append(" " + symName);
        }
        sb.append(";\n");
        LinkedHashMap<FunctionSymbol, String> rsyms = new LinkedHashMap<>();
        for (Entry<String, FunctionSymbol> e : syms.entrySet()) {
            rsyms.put(e.getValue(), e.getKey());
        }
        int ti = 0;
        for (CpxIntTupleRule r : tuples) {
            TRSFunctionApplication lhs = r.getLeft();
            TRSFunctionApplication rhs = r.getRights().size() > 0 ? r.getRights().get(0) : end_st;
            LinkedHashSet<TRSVariable> freeRhsVars = new LinkedHashSet<>();
            freeRhsVars.addAll(rhs.getVariables());
            freeRhsVars.removeAll(lhs.getVariables());
            // completely free variables are ok
            // every free variable must only occur once, since it will be translated to a joker
            for (Entry<TRSVariable, Integer> e : r.getRight().getVariableCount().entrySet()) {
                if (freeRhsVars.contains(e.getKey()) && e.getValue() > 1) {
                    return this.error("Free variable used more than once.");
                }
            }
            Map<TRSVariable, TRSTerm> rawSigma = new LinkedHashMap<>();
            int xi = 0;
            for (TRSTerm t : lhs.getArguments()) {
                assert t.isVariable();
                TRSVariable v = (TRSVariable) t;
                assert !rawSigma.containsKey(v);
                String x_i = "x" + xi++;
                rawSigma.put(v, TRSTerm.createVariable(x_i));
            }
            TRSVariable qm = TRSTerm.createVariable("?");
            for (TRSVariable f : freeRhsVars) {
                rawSigma.put(f, qm);
            }
            Set<TRSVariable> guardVarsWOLhsVars = r.getConstraintTerm().getVariables();
            guardVarsWOLhsVars.removeAll(r.getLeft().getVariables());
            int fi = 0;
            for (TRSVariable fv : guardVarsWOLhsVars) {
                rawSigma.put(fv, TRSTerm.createVariable("g" + fi++));
            }
            TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(rawSigma));
            CpxIntTupleRule ren;
            try {
                ren = r.applySubstitution(sigma);
            } catch (NoConstraintTermException e) {
                return this.error(e.toString());
            }
            rhs = ren.getRights().size() > 0 ? ren.getRights().get(0) : end_st;
            sb.append("\n");
            ConstraintInformation ci = ren.getConstraintInformation();
            sb.append("  // " + r.toString() + "\n");
            sb.append("  transition t" + ti++ + " := {\n");
            sb.append("    from     := " + rsyms.get(lhs.getRootSymbol()) + ";\n");
            sb.append("    to       := " + rsyms.get(rhs.getRootSymbol()) + ";\n");
            sb.append("    guard    := ");
            first = true;
            for (Constraint c : ci.getConstraints()) {
                if (first) {
                    first = false;
                } else {
                    sb.append(" && ");
                }
                sb.append("(");
                sb.append(CpxIntTermHelper.exportTerm(c.getConstraintTerm(), new PLAIN_Util()).replace("TRUE", "true"));
                sb.append(")");
            }
            if (first == true) {
                sb.append("true");
            }
            sb.append(";\n");
            sb.append("    action   :=");
            first = true;
            xi = 0;
            for (TRSTerm t : rhs.getArguments()) {
                TRSVariable x_i = TRSTerm.createVariable("x" + xi++);
                if (t.equals(x_i)) {
                    continue;
                }
                if (first) {
                    first = false;
                } else {
                    sb.append(",");
                }
                sb.append(" " + x_i + "' = " + CpxIntTermHelper.exportTerm(t, new PLAIN_Util()));
            }
            for (int i = 0; i < maxFreeVars; ++i) {
                if (first) {
                    first = false;
                } else {
                    sb.append(",");
                }
                sb.append(" g" + i + "' = ?");
            }
            sb.append(";\n");
            sb.append("  };\n");
        }
        sb.append("}\n"); // end model main
        sb.append("strategy dumb {\n");
        sb.append("    Region init := { state = " + rsyms.get(obl.getG().iterator().next()) + " };\n");
        sb.append("}\n");
        String of = System.getenv().get("OUTPUTFILE");
        FileWriter bw = null;
        try {
            bw = new FileWriter(of);
            bw.write(sb.toString());
        } catch (IOException e) {
            return this.error(e.toString());
        } finally {
            if (bw != null) {
                try {
                    bw.close();
                } catch (IOException e) {
                    return this.error(e.toString());
                }
            }
        }
        return ResultFactory.proved(null);
    }

    private Result error(String string) {
        System.err.println(string);
        return ResultFactory.unsuccessful(string);
    }

    private String getStateName(FunctionSymbol fs, LinkedHashMap<String, FunctionSymbol> syms) {
        String name = fs.getName().replaceAll("[^_a-zA-Z0-9]", "");

        if (Character.isDigit(name.charAt(0))) {
            name = "l" + name;
        }

        // create a unique state name for every function symbol
        while (syms.containsKey(name) && !fs.equals(syms.get(name))) {
            name += "_";
        }
        return name;
    }

    @Override
    boolean isCpxIntTrsApplicable(CpxIntTrsProblem obl) {
        return true;
    }

}
