package aprove.verification.oldframework.CostEquationSystem;

import java.math.*;
import java.text.*;
import java.util.*;

import aprove.Globals;
import aprove.api.decisions.impl.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.MinMaxExprs.*;
import aprove.verification.oldframework.Algebra.MinMaxExprs.MinMaxExprParser.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.WeightedIntTrs.*;
import immutables.*;

public class CESBackendProcessor extends ProcessorSkeleton {

    public static enum Backend {
        Cofloco, Pubs;
    }

    private Arguments args;

    public static class Arguments {
        public int timeout = Integer.MAX_VALUE;
        public Backend backend = Backend.Cofloco;
        public boolean assumeSequential = false;
        public boolean solveFast = false;
        /*
         * CoFloClo can differentiate input and output variables via input_output_vars.
         * For CES generated from Java, we know during generation which variables are for input and which are for output.
         * However, it is not trivial to keep track of the variable type in the preocessor between generation and here.
         * To improve the strength of the CES Backend, one should consider adding the seperation to CES obligations.
         */
    }

    @ParamsViaArgumentObject
    public CESBackendProcessor(Arguments args) {
        this.args = args;
    }

    class ExportWorker {

        FreshNameGenerator fng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);

        String clear(String in) {
            return in.replace('\'', '_'); //TODO if names end in underscore this could cause collisions
        }

        String getNameForVar(TRSVariable var) {
            String name = var.getName();
            name = Character.toUpperCase(name.charAt(0)) + name.substring(1);
            return fng.getFreshName(clear(name), true);
        }

        String getNameForFS(FunctionSymbol fs) {
            String name = fs.getName();
            name = Character.toLowerCase(name.charAt(0)) + name.substring(1);
            return fng.getFreshName(clear(name), true);
        }

        String getFreshName(String s) {
            return fng.getFreshName(clear(s), false);
        }

        List<String> args = new ArrayList<>();
        CostEquationSystem ces;
        StringBuilder o = new StringBuilder();

        ExportWorker(CostEquationSystem ces) {
            this.ces = ces;
        }

        String work() {
            buildStartEq(ces.getStartTerm());
            for (CostEquation e : ces.getRules()) {
                exportEquation(e);
            }
            buildInputOutputEq(ces.getRules());
            return o.toString();
        }

        private void buildStartEq(TRSFunctionApplication startTerm) {
            this.o.append("eq(");
            this.o.append("start");
            this.o.append("(");
            StringBuilder sb = new StringBuilder();
            FunctionSymbol fs = startTerm.getRootSymbol();
            int arity = fs.getArity();
            if (sb.length() > 0) {
                sb.append(",");
            }
            sb.append(getNameForFS(fs));
            if (arity > 0) {
                sb.append("(");
                for (int i = 0; i < arity; ++i) {
                    TRSTerm arg = startTerm.getArgument(i);
                    String v;
                    if (arg.isVariable()) {
                        v = getNameForVar((TRSVariable)arg);
                    } else {
                        v = getFreshName("Arg");
                    }
                    if (i > 0) {
                        sb.append(",");
                        this.o.append(",");
                    }
                    sb.append(v);
                    this.o.append(v);
                    args.add(v);
                }
                sb.append(")");
            }
            this.o.append("),0,[");
            this.o.append(sb.toString());
            this.o.append("],[]).\n");
        }

        private void exportEquation(CostEquation e) {
            this.o.append("eq(");
            this.exportCallTerm(e.getLeft());
            this.o.append(",");
            exportIntTerm(e.getUpperBound().toTerm());
            this.o.append(",[");
            TRSFunctionApplication cond = e.getCondition();
            cond = this.exportRhs(e.getRight(), cond);
            this.o.append("],[");
            exportConstraints(cond);
            this.o.append("]).\n");
        }

        /**
         * Build rules for input/output variable declaration
         * NOTE: Does not filter duplicates
         * @param rules
         */
        private void buildInputOutputEq(Set<CostEquation> rules) {
            for (CostEquation e : rules) {
                if (e.getLeftOutputVariables() == null) {
                    continue;
                }

                // get input vars
                List<String> inputVars = new ArrayList<>();
                for (TRSTerm arg : e.getLeft().getArguments()) {
                    if (!e.getLeftOutputVariables().contains(arg) && arg instanceof TRSVariable) {
                        inputVars.add(getNameForVar((TRSVariable) arg));
                    }
                }

                // get output vars
                List<String> outputVars = new ArrayList<>();
                for (TRSTerm arg : e.getLeftOutputVariables()) {
                    if (arg instanceof TRSVariable) {
                        outputVars.add(getNameForVar((TRSVariable) arg));
                    }
                }

                this.o.append("input_output_vars(");
                this.exportCallTerm(e.getLeft());
                this.o.append(",");
                this.o.append(inputVars.toString());
                this.o.append(",");
                this.o.append(outputVars.toString());
                this.o.append(").\n");

            }
        }

        private TRSFunctionApplication exportRhs(Collection<TRSFunctionApplication> rhss, TRSFunctionApplication cond) {
            boolean first = true;
            for (TRSFunctionApplication rhs : rhss) {
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
                    TRSVariable var = TRSTerm.createVariable(getFreshName("Term"));
                    cond = ToolBox.buildAnd(cond, ToolBox.buildEq(var, callTerm));
                    varArgs.add(var);
                }
                this.exportCallTerm(TRSTerm.createFunctionApplication(rhs.getRootSymbol(), ImmutableCreator.create(varArgs)));
            }
            return cond;
        }

        private void exportCallTerm(TRSFunctionApplication t) {
            FunctionSymbol fs = t.getRootSymbol();
            this.o.append(getNameForFS(fs));
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

        private void exportConstraints(TRSFunctionApplication c) {
            Stack<TRSFunctionApplication> todo = new Stack<>();
            Set<TRSFunctionApplication> res = new LinkedHashSet<>();
            todo.add(c);
            while (!todo.isEmpty()) {
                TRSFunctionApplication f = todo.pop();
                if (f.getRootSymbol().equals(CpxIntTermHelper.fLand)) {
                    todo.push((TRSFunctionApplication) f.getArgument(0));
                    todo.push((TRSFunctionApplication) f.getArgument(1));
                } else {
                    res.add(f);
                }
            }
            Iterator<TRSFunctionApplication> it = res.iterator();
            while (it.hasNext()) {
                exportConstraint(it.next());
                if (it.hasNext()) {
                    o.append(",");
                }
            }
        }

        private void exportConstraint(TRSFunctionApplication tArg) {
            assert tArg != null;
            TRSFunctionApplication t = tArg;
            if (CESBackendProcessor.this.args.backend == Backend.Pubs && nonLinear(tArg)) {
                this.o.append("0>=0");
                return;
            }
            t = removeMinus(t);
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
            if (CpxIntTermHelper.TRUE.getRootSymbol().equals(op)) {
                this.o.append("0>=0");
                return;
            }

            throw new RuntimeException("Don't know how to export " + op);
        }

        private TRSFunctionApplication removeMinus(TRSFunctionApplication t) {
            Collection<FunctionSymbol> comparators = Arrays.asList(new FunctionSymbol[] {
                CpxIntTermHelper.fEq,
                CpxIntTermHelper.fGe,
                CpxIntTermHelper.fLe,
                CpxIntTermHelper.fLt,
                CpxIntTermHelper.fGt });
            if (!comparators.contains(t.getRootSymbol())) {
                return t;
            }
            Optional<Pair<TRSTerm, TRSTerm>> leftOpt = getNegativeSubterm(t.getArgument(0));
            if (leftOpt.isPresent()) {
                TRSTerm right = TRSTerm.createFunctionApplication(CpxIntTermHelper.fAdd, t.getArgument(1), leftOpt.get().y);
                return removeMinus(TRSTerm.createFunctionApplication(t.getRootSymbol(), leftOpt.get().x, right));
            }
            Optional<Pair<TRSTerm, TRSTerm>> rightOpt = getNegativeSubterm(t.getArgument(1));
            if (rightOpt.isPresent()) {
                TRSTerm left = TRSTerm.createFunctionApplication(CpxIntTermHelper.fAdd, t.getArgument(0), rightOpt.get().y);
                return removeMinus(TRSTerm.createFunctionApplication(t.getRootSymbol(), left, rightOpt.get().x));
            }
            return t;
        }

        private Optional<Pair<TRSTerm, TRSTerm>> getNegativeSubterm(TRSTerm tArg) {
            if (tArg.isVariable()) {
                return Optional.empty();
            }
            TRSFunctionApplication t = (TRSFunctionApplication) tArg;
            if (CpxIntTermHelper.fUnaryMinus.equals(t.getRootSymbol())) {
                return Optional.of(new Pair<>(CpxIntTermHelper.getInteger(BigIntImmutable.ZERO), t.getArgument(0)));
            }
            if (t.isConstant() && CpxIntTermHelper.getIntegerValue(t).compareTo(BigInteger.ZERO) < 0) {
                BigIntImmutable negated = BigIntImmutable.create(CpxIntTermHelper.getIntegerValue(t).negate());
                return Optional.of(new Pair<>(CpxIntTermHelper.getInteger(BigIntImmutable.ZERO), CpxIntTermHelper.getInteger(negated)));
            }
            if (CpxIntTermHelper.fMul.equals(t.getRootSymbol())) {
                return Optional.empty();
            }
            if (CpxIntTermHelper.fSub.equals(t.getRootSymbol())) {
                return Optional.of(new Pair<>(t.getArgument(0), t.getArgument(1)));
            }
            assert(t.isConstant() || CpxIntTermHelper.fAdd.equals(t.getRootSymbol()));
            for (int i = 0; i < t.getArity(); i++) {
                TRSTerm arg = t.getArgument(i);
                Optional<Pair<TRSTerm, TRSTerm>> res = getNegativeSubterm(arg);
                if (res.isPresent()) {
                    List<TRSTerm> newArgs = new ArrayList<>(t.getArguments());
                    newArgs.set(i, res.get().x);
                    TRSFunctionApplication newT = TRSTerm.createFunctionApplication(t.getRootSymbol(), newArgs);
                    return Optional.of(new Pair<>(newT, res.get().y));
                }
            }
            return Optional.empty();
        }

        private boolean nonLinear(TRSTerm tArg) {
            if (tArg.isVariable()) {
                return false;
            }
            TRSFunctionApplication t = (TRSFunctionApplication) tArg;
            if (CpxIntTermHelper.fMul.equals(t.getRootSymbol())) {
                if (!constant(t.getArgument(0)) && !constant(t.getArgument(1))) {
                    return true;
                }
            }
            for (TRSTerm arg: t.getArguments()) {
                if (nonLinear(arg)) {
                    return true;
                }
            }
            return false;
        }

        private boolean constant(TRSTerm argument) {
            return argument.getVariables().isEmpty();
        }

        private void exportIntTerm(TRSTerm t) {
            if (t.isVariable()) {
                this.exportIntTerm((TRSVariable) t);
            } else {
                this.exportIntTerm((TRSFunctionApplication) t);
            }
        }

        private void exportIntTerm(TRSVariable v) {
            this.o.append(getNameForVar(v));
        }

        private void exportIntTerm(TRSFunctionApplication t) {
            FunctionSymbol op = t.getRootSymbol();
            BigInteger i = CpxIntTermHelper.getIntegerValue(t);
            if (i != null) {
                this.o.append(op.getName());
                return;
            }
            if (CpxIntTermHelper.fAdd.equals(op) || CpxIntTermHelper.fMul.equals(op) || CpxIntTermHelper.fSub.equals(op)) {
                this.o.append("(");
                this.exportIntTerm(t.getArgument(0));
                this.o.append(" " + op.getName() + " ");
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

    private class CESProof extends DefaultProof {

        private ComplexityValue res;
        private List<String> output;

        public CESProof(ComplexityValue res, List<String> output) {
            this.res = res;
            this.output = output;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder sb = new StringBuilder();
            sb.append("proved upper bound " + res + " using " + args.backend + ':' + o.newline() + o.newline());
            for (String s : output) {
                sb.append(o.escape(s)).append(o.newline());
            }
            return sb.toString();
        }

    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        CostEquationSystem ces = (CostEquationSystem) obl;
        ExportWorker worker = new ExportWorker(ces);
        String input = worker.work();
        Triple<ComplexityValue, String, List<String>> asymptoticAndConcreteBound = null;
        switch (args.backend) {
            case Cofloco: asymptoticAndConcreteBound = processWithCoFloCo(input, aborter);
            break;
            case Pubs: asymptoticAndConcreteBound = processWithPUBS(input, aborter);
            break;
        }

        if (asymptoticAndConcreteBound != null && asymptoticAndConcreteBound.x != null) {
            if (Globals.DEBUG_THIES) {
                /*
                try {
                    DumpProcessor.dump("/tmp/", "test.ces", input);
                } catch (DumpFailedException e) {
                    e.printStackTrace();
                }
                */
                asymptoticAndConcreteBound.z.add("DEBUG");
                for (String s : input.split("eq\\("))
                {
                    asymptoticAndConcreteBound.z.add("eq(" + s);
                }
            }
            return onCoFloCoSucces(ces, asymptoticAndConcreteBound.x, asymptoticAndConcreteBound.y, worker.args, asymptoticAndConcreteBound.z);
        } else {
            return onCoFloCoFail(ces, new Exception("CoFloCo failed"));
        }
    }

    protected Result onCoFloCoSucces(CostEquationSystem ces, ComplexityValue cv, String poly, List<String> args, List<String> proof) {
        MinMaxExpr res = null;
        if (poly != null) {
            try {
                res = MinMaxExprParser.parse(poly);
                res = Util.renameVariablesAccordingToStartTerm(ces.getStartTerm(), res, args);
            } catch (ParseException e) {
                e.printStackTrace();
            } catch (InfiniteException e) {
                return ResultFactory.unsuccessful();
            }
        }
        if (res != null) {
            cv = cv.withConcreteValue(res);
        }
        return ResultFactory.provedWithValue(ComplexityYNM.createUpper(cv), new CESProof(cv, proof));
    }

    protected Result onCoFloCoFail(CostEquationSystem ces, Exception e) {
        return ResultFactory.unsuccessful();
    }

    private Triple<ComplexityValue, String, List<String>> processWithCoFloCo(String input, Abortion aborter) {
        List<String> output = CESHelper.executeCoFloCo(input, args.timeout, args.solveFast, args.assumeSequential, aborter);
        String asymptoticClass = CESHelper.obtainAsymptoticCoflocoResult(output);
        ComplexityValue cv;
        if (asymptoticClass == null) {
            cv = null;
        } else {
            cv = CESHelper.parseComplexity(asymptoticClass);
        }
        String poly = CESHelper.obtainConcreteCoFloCoResult(output);
        return new Triple<>(cv, poly, output);
    }

    private Triple<ComplexityValue, String, List<String>> processWithPUBS(String input, Abortion aborter) {
        List<String> output = CESHelper.executePUBS(input, args.timeout, aborter);
        String poly = CESHelper.obtainConcretePUBSResult(output);
        ComplexityValue cv;
        if (poly == null) {
            cv = null;
        } else {
            cv = CESHelper.getAsymptoticPUBSResult(poly);
        }
        return new Triple<>(cv, poly, output);
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof CostEquationSystem &&
                LocalToolDetector.cintBackendExists(args.backend.name().toLowerCase());
    }
}
