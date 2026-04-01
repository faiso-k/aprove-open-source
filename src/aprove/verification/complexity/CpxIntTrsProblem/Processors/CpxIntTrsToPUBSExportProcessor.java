package aprove.verification.complexity.CpxIntTrsProblem.Processors;

import java.io.*;
import java.math.*;
import java.util.*;

import aprove.verification.complexity.CpxIntTrsProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

public class CpxIntTrsToPUBSExportProcessor extends CpxIntTrsExportProcessor {

    @Override
    protected void export(CpxIntTrsProblem obl, Appendable o) throws IOException {
        CpxIntTrsToPUBSExportWorker worker = new CpxIntTrsToPUBSExportWorker();
        worker.export(obl, o);
    }

    private static class CpxIntTrsToPUBSExportWorker {
        static String makeName(String name) {
            StringBuilder sb = new StringBuilder();
            for (int i = 0, l = name.length(); i < l; ++i) {
                char c = name.charAt(i);
                if ((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c == '_') {
                    sb.append(c);
                }
            }
            if (sb.length() == 0 || !Character.isAlphabetic(sb.charAt(0))) {
                return "H" + sb.toString();
            }
            return sb.toString();
        }

        private final FreshNameGenerator predicateFNG = new FreshNameGenerator(FreshNameGenerator.PROLOG_FUNCS);
        private final FreshNameGenerator varFNG = new FreshNameGenerator(FreshNameGenerator.PROLOG_VARS);

        private final LinkedHashMap<FunctionSymbol, String> predicateNames = new LinkedHashMap<>();
        private final LinkedHashMap<TRSVariable, String> varNames = new LinkedHashMap<>();
        private Appendable o;

        protected void export(CpxIntTrsProblem obl, Appendable o) throws IOException {
            assert this.predicateNames.size() == 0;
            assert this.varNames.size() == 0;
            // We have state, so check that we were not used accidentally
            assert this.o == null;
            this.o = o;

            // the first rule is considered to be the start rule
            this.buildStartEq(obl.getG());

            for (CpxIntTupleRule r : obl.getK().keySet()) {
                this.exportRule(r);
            }
        }

        private void buildStartEq(LinkedHashSet<FunctionSymbol> definedSymbols) throws IOException {
            this.o.append("eq(");
            this.o.append(this.predicateFNG.getFreshName("pubs_start", false));
            this.o.append("(");
            StringBuilder sb = new StringBuilder();
            boolean first = true;
            for (FunctionSymbol fs : definedSymbols) {
                int l = fs.getArity();
                if (sb.length() > 0) {
                    sb.append(",");
                }
                sb.append(this.getPredicateName(fs));
                if (l > 0) {
                    sb.append("(");
                    for (int i = 0; i < l; ++i) {
                        String v = this.varFNG.getFreshName("X", false);
                        if (i > 0) {
                            sb.append(",");
                        }
                        sb.append(v);
                        if (i > 0 || !first) {
                            this.o.append(",");
                        }
                        this.o.append(v);
                    }
                    sb.append(")");
                }
                first = false;
            }
            this.o.append("),0,[");
            this.o.append(sb.toString());
            this.o.append("],[]).\n");
        }

        private void exportRule(CpxIntTupleRule r) throws IOException {
            this.o.append("eq(");
            this.exportCallTerm(r.getLeft());
            this.o.append(",1,[");
            LinkedHashSet<Constraint> constraints = new LinkedHashSet<>();
            assert r.getConstraints() != null;
            constraints.addAll(r.getConstraints());
            boolean first = true;
            for (TRSFunctionApplication rhs : r.getRights()) {
                if (first) {
                    first = false;
                } else {
                    this.o.append(",");
                }
                ArrayList<TRSVariable> varArgs = new ArrayList<>();
                for (TRSTerm callTerm : rhs.getArguments()) {
                    if (callTerm.isVariable()) {
                        varArgs.add((TRSVariable) callTerm);
                        continue;
                    }
                    TRSVariable var = TRSTerm.createVariable(this.varFNG.getFreshName("H", false));
                    try {
                        constraints.add(Constraint.create(TRSTerm.createFunctionApplication(
                            CpxIntTermHelper.fEq,
                            var,
                            callTerm)));
                    } catch (NoConstraintTermException e) {
                        throw new RuntimeException(e);
                    }
                    varArgs.add(var);
                }
                this.exportCallTerm(TRSTerm.createFunctionApplication(rhs.getRootSymbol(), ImmutableCreator.create(varArgs)));
            }
            first = true;
            this.o.append("],[");
            for (Constraint c : constraints) {
                if (first) {
                    first = false;
                } else {
                    this.o.append(",");
                }
                if (c == null) {
                    System.err.println("null constraint?");
                    System.err.println(r);
                }
                this.exportConstraint(c);
            }
            this.o.append("]).\n");
        }

        private String getPredicateName(FunctionSymbol fs) {
            if (!this.predicateNames.containsKey(fs)) {
                this.predicateNames.put(fs, this.predicateFNG.getFreshName(CpxIntTrsToPUBSExportWorker.makeName(fs.getName()).toLowerCase(), false));
            }
            return this.predicateNames.get(fs);
        }

        private void exportCallTerm(TRSFunctionApplication t) throws IOException {
            FunctionSymbol fs = t.getRootSymbol();
            this.o.append(this.getPredicateName(fs));
            if (fs.getArity() == 0) {
                return;
            }
            this.o.append("(");
            boolean first = true;
            for (TRSTerm ti : t.getArguments()) {
                assert ti.isVariable();
                if (first) {
                    first = false;
                } else {
                    this.o.append(",");
                }
                TRSVariable v = (TRSVariable) ti;
                this.exportIntTerm(v);
            }
            this.o.append(")");
        }

        private void exportConstraint(Constraint c) throws IOException {
            assert c != null;
            TRSFunctionApplication t = c.getConstraintTerm();
            FunctionSymbol op = t.getRootSymbol();
            if (CpxIntTermHelper.fEq.equals(op)) {
                this.exportIntTerm(t.getArgument(0));
                this.o.append("=");
                this.exportIntTerm(t.getArgument(1));
                return;
            }
            if (CpxIntTermHelper.fGe.equals(op)) {
                this.exportIntTerm(t.getArgument(0));
                this.o.append(">=");
                this.exportIntTerm(t.getArgument(1));
                return;
            }
            if (CpxIntTermHelper.fLe.equals(op)) {
                this.exportIntTerm(t.getArgument(1));
                this.o.append(">=");
                this.exportIntTerm(t.getArgument(0));
                return;
            }
            if (CpxIntTermHelper.fLt.equals(op)) {
                this.exportIntTerm(t.getArgument(1));
                this.o.append(">=1+(");
                this.exportIntTerm(t.getArgument(0));
                this.o.append(")");
                return;
            }
            if (CpxIntTermHelper.fGt.equals(op)) {
                this.exportIntTerm(t.getArgument(0));
                this.o.append(">=1+(");
                this.exportIntTerm(t.getArgument(1));
                this.o.append(")");
                return;
            }

            throw new RuntimeException("Don't know how to export " + op);
        }

        private void exportIntTerm(TRSTerm t) throws IOException {
            if (t.isVariable()) {
                this.exportIntTerm((TRSVariable) t);
            } else {
                this.exportIntTerm((TRSFunctionApplication) t);
            }
        }

        private void exportIntTerm(TRSVariable v) throws IOException {
            if (!this.varNames.containsKey(v)) {
                this.varNames.put(v, this.varFNG.getFreshName(CpxIntTrsToPUBSExportWorker.makeName(v.getName()).toUpperCase(), false));
            }
            this.o.append(this.varNames.get(v));
        }

        private void exportIntTerm(TRSFunctionApplication t) throws IOException {
            FunctionSymbol op = t.getRootSymbol();
            BigInteger i = CpxIntTermHelper.getIntegerValue(t);
            if (i != null) {
                this.o.append(op.getName());
                return;
            }
            if (CpxIntTermHelper.fAdd.equals(op) || CpxIntTermHelper.fMul.equals(op) || CpxIntTermHelper.fSub.equals(op)) {
                this.o.append("(");
                this.exportIntTerm(t.getArgument(0));
                this.o.append(op.getName());
                this.exportIntTerm(t.getArgument(1));
                this.o.append(")");
                return;
            }
            if (CpxIntTermHelper.fUnaryMinus.equals(op)) {
                this.o.append("(0-");
                this.exportIntTerm(t.getArgument(0));
                this.o.append(")");
                return;
            }
            throw new RuntimeException("Don't know how to export " + op);
        }
    }
}
