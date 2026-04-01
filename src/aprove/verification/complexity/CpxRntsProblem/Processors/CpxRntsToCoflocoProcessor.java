package aprove.verification.complexity.CpxRntsProblem.Processors;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.OptionalInt;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.CdtProblem.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Algorithms.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.*;
import aprove.verification.complexity.LowerBounds.Util.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Processor.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @note Prefer CpxRntsCompleteToCoflocoProcessor if possible, as it is much
 * simpler and also produces simpler cost relations.
 *
 *
 * Translates a RNTS into cost relations for CoFloCo and runs CoFloco
 * to obtain an asymptotic bound on the complexity.
 *
 * @note in contrast to CpxRntsCompleteToCoflocoProcessor, this is sound
 * for arbitrary RNTSs (i.e. also when partial derivations are relevant).
 *
 * Translation of nested function calls:
 * f(x) -> g(h(x)) becomes eq(f(X,Ret),1,[h(X,Out_h),g(Out_h,Out_g)],[Ret = Out_g]).
 *
 * Translation of partial derivations: Cofloco only considers *complete* evaluations,
 * so for instance eq(f(X),1,[f(X-1)],[X > 1]). is in O(1), as it cannot terminate.
 * One can simply add rules eq(f(X),1,[],[]). for all functions f to overcome this
 * issue. This is sound, but also over-approximating (sometimes too much).
 *
 * Instead, an "Error"-flag is introduced which is usually 0, but set to 1 for
 * rules that are added to manually complete partial evaluations. One can then
 * try to stop evaluations whenever "Error" is set to 1. Thus, the translation
 * is less over-approximating. Example:
 *
 * RNTS:
 *  f(X) -> f(X-1) [X > 0]  //only partial evaluations, f(0) cannot be evaluated
 *  g(X) -> h(f(X))         //g(x) is in O(n), since h can never be evaluated!
 *  h(X) -> h(X)
 *
 *
 * Cost relations for f (note the "Err" flags):
 *
 *  eq(f(X,Ret,Err),1,[f(X-1,Out_f,Err_f)],[Ret=Out_f,Err=Err_f]). //original rule
 *  eq(f(X,Ret,Err),0,[],[Err=1]).              //completing rule, sets Error flag
 *
 *
 * Cost relations for g: Here we consider the two cases whether f evaluates completely or not.
 * If f evaluates completely, then h is also called (note that in this case, the "Error" of f is 0!)
 * If f does not evaluate completey ("Error" of f is 1), then h should not be called.
 * So we obtain (** for emphasis **):
 *
 *  eq(g(X,Ret,Err),1,[f(X,Out_f,Err_f),h(Out_f,Out_h,Err_h)],[Ret=Out_h,Err=Err_h, ** Err_f = 0 **]
 *  eq(g(X,Ret,Err),1,[f(X,Out_f,Err_f)],[** Err_f=1 **,Err=1] //don't evaluate h if f is not fully evaluated
 *
 *
 * The cost relation for h is trivial. Here, g(X) is still in O(n), as h can only
 * be evaluated if the Error-flag of f is 0 (first rule). If one would omit the
 * Error-flag, then one can evaluate h after using the completing rule for f,
 * yielding INF runtime for g.
 *
 * Note: to fully perform the Error-flag construction has an exponential blowup,
 * thus we only try to avoid execution of the outermost function (here: h)
 * and do not handle rhss with multiple parallel calls. For such cases, one can
 * simply omit the Error-flag (more over-approximation but less exponential blowup).
 *
 * @author mnaaf, original idea by Antonio Flores-Montoya (author of CoFloCo)
 */
public class CpxRntsToCoflocoProcessor extends ProcessorSkeleton {

    //options
    private final int timeout;

    //arguments that can be passed from the strategy file
    public static class Arguments {
        public int timeout = 0;
    }

    @ParamsViaArgumentObject
    public CpxRntsToCoflocoProcessor(final Arguments arguments) {
        this.timeout = arguments.timeout;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (!CoFloCoBackend.isInstalled) {
            return false;
        }
        return (obl instanceof CpxRntsProblem);
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        CpxRntsToCoflocoWorker worker = new CpxRntsToCoflocoWorker();
        Result res = worker.process(obl, oblNode, aborter, rti);
        return res;
    }

    /**
     * Helper class to encapsulate the instance-dependent state of the
     * computation by the processor.
     */
    private class CpxRntsToCoflocoWorker {
        private CpxRntsProblem rnts = null;
        private FreshNameGenerator fng = null;
        private TRSVariable returnVar = null;
        private TRSVariable errorVar = null;
        private Export_Util plainUtil = null;

        private TRSVariable createPositionedVariable(String basename, Position pos) {
            StringBuilder name = new StringBuilder(basename);
            name.append("P");
            for (Integer n : pos) {
                name.append(n);
            }
            String res = this.fng.getFreshName(name.toString(), false);
            return TRSTerm.createVariable(res);
        }

        //use getOuterCallPositions, this is an internal function
        private void addOuterCallPositions(TRSTerm term, Position currpos, Set<Position> res) {
            if (term.isVariable()) return;
            TRSFunctionApplication funapp = (TRSFunctionApplication)term;
            if (this.rnts.isDefinedSymbol(funapp.getRootSymbol())) {
                res.add(currpos);
            } else {
                List<TRSTerm> args = funapp.getArguments();
                for (int i=0; i < args.size(); ++i) {
                    addOuterCallPositions(args.get(i), currpos.append(i), res);
                }
            }
        }

        private Set<Position> getOuterCallPositions(TRSTerm term) {
            Set<Position> res = new LinkedHashSet<>();
            addOuterCallPositions(term, Position.EPSILON, res);
            return res;
        }

        private List<String> exportRhs(RntsRule rule) {
            TRSTerm rhs = rule.getRight();
            Set<Position> parallelCallPos = getOuterCallPositions(rhs);

            //replace all inner calls
            List<Triple<TRSFunctionApplication,TRSVariable,TRSVariable>> calls = new ArrayList<>();
            Set<Position> positions = new TreeSet<>(new InnerMostPositionComparator());
            positions.addAll(rhs.getPositions());
            for (Position pos : positions) {
                TRSTerm subterm = rhs.getSubterm(pos);
                if (subterm.isVariable()) continue;

                TRSFunctionApplication funapp = (TRSFunctionApplication)subterm;
                if (!rnts.isDefinedSymbol(funapp.getRootSymbol())) continue;

                //remember information for this call
                TRSVariable ret = createPositionedVariable("Ret", pos);
                TRSVariable err = createPositionedVariable("Err", pos);
                calls.add(new Triple<>(funapp,err,ret));

                //replace the local call by its return value in the outermost call
                rhs = rhs.replaceAt(pos,ret);
            }

            //calls for full evaluation
            String callsFull = calls.stream().map(triple -> CoflocoHelper.exportFunapp(triple.x,Optional.of(triple.y),triple.z)).collect(Collectors.joining(","));

            //export return value in the guard
            TRSTerm returnGuard = TRSTerm.createFunctionApplication(CpxIntTermHelper.fEq, this.returnVar, rhs);
            StringBuilder guard = new StringBuilder();
            guard.append(CoflocoHelper.exportConstraint(returnGuard));

            //export guard
            for (Constraint cond : rule.getConstraints()) {
                guard.append(",");
                guard.append(CoflocoHelper.exportConstraint(cond.getConstraintTerm()));
            }

            //if multiple parallel positions occur, the Err-encoding would be complicated (and exponential in the number of parallel calls) and is skipped
            if (parallelCallPos.size() > 1) {
                //encode constraint for the returned Err-flag
                guard.append("," + this.errorVar.getName() + "=0");
                guard.append(calls.stream().map(triple -> "+" + triple.y.getName()).collect(Collectors.joining())); //return sum of all Err-flags
                guard.append("," + this.errorVar.getName() + ">=0");

                //just do a full evaluation with no restrictions on the Err-flags
                return Collections.singletonList("[" + callsFull + "],[" + guard.toString() + "]");
            }

            //if there are no calls, no Err-flags need to be checked
            if (calls.isEmpty()) {
                return Collections.singletonList("[],[" + guard.toString() + "," + this.errorVar.getName()+"=0" + "]");
            }

            List<String> res = new ArrayList<>();
            TRSVariable outermostErr = calls.remove(calls.size()-1).y; //drop outermost call

            //full evaluations with restrictions
            String guardFull = calls.stream().map(triple -> triple.y.getName() + "=0,").collect(Collectors.joining());
            guardFull += this.errorVar.getName() + "=" + outermostErr.getName();
            res.add("[" + callsFull + "],[" + guard.toString() + "," + guardFull + "]");

            //construct rule for partial evaluation (all but the outermost call)
            if (!calls.isEmpty()) {
                String callsPartial = calls.stream().map(triple -> CoflocoHelper.exportFunapp(triple.x,Optional.of(triple.y),triple.z)).collect(Collectors.joining(","));
                String guardPartial = calls.stream().map(triple -> triple.y.getName()).collect(Collectors.joining("+")) + ">=1"; //sum of all Err-flags is >= 1 (some flag is not 0)
                guardPartial += "," + this.errorVar.getName() + "=1";
                res.add("[" + callsPartial + "],[" + guard.toString() + "," + guardPartial + "]");
            }

            return res;
        }

        private String exportRule(RntsRule rule) {
            String left = "eq(";
            left += CoflocoHelper.exportFunapp(rule.getLeft(), Optional.of(this.errorVar), this.returnVar) + ",";
            left += CoflocoHelper.exportCost(rule.getCost()) + ",";

            StringBuilder res = new StringBuilder();
            for (String rhs : exportRhs(rule)) {
                res.append(left);
                res.append(rhs);
                res.append(")." + this.plainUtil.linebreak());
            }
            return res.toString();
        }

        private List<String> makeTerminatingRules() {
            List<String> res = new ArrayList<>();
            for (FunctionSymbol fun : this.rnts.getDefinedSymbols()) {
                //lhs
                List<TRSVariable> args = new ArrayList<>();
                for (int i=0; i < fun.getArity(); ++i) {
                    args.add(TRSTerm.createVariable(this.rnts.getArgumentName(i)));
                }
                TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(fun, args);

                //no rhs (abort evaulation here), but set Err flag
                String s = "eq(";
                s += CoflocoHelper.exportFunapp(lhs, Optional.of(this.errorVar), this.returnVar);
                s += ",0,[],[" + errorVar.getName() + "=1," + returnVar.getName() + "=0]).";
                res.add(s);
            }
            return res;
        }

        private List<String> makeStartRules() {
            List<String> res = new ArrayList<>();

            //find number of arguments needed
            OptionalInt maxArity = this.rnts.getInitialSymbols().stream().mapToInt(fun -> fun.getArity()).max();
            if (!maxArity.isPresent()) return res;

            //create lhs
            FunctionSymbol startFun = FunctionSymbol.create(this.fng.getFreshName("start", false), maxArity.getAsInt());
            List<TRSVariable> args = new ArrayList<>();
            for (int i=0; i < maxArity.getAsInt(); ++i) {
                args.add(TRSTerm.createVariable(this.rnts.getArgumentName(i)));
            }
            TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(startFun, args);

            //create all rules
            for (FunctionSymbol fun : rnts.getInitialSymbols()) {
                StringBuilder s = new StringBuilder();
                s.append("eq(");
                s.append(IDPExport.exportTerm(lhs, this.plainUtil, IDPPredefinedMap.DEFAULT_MAP));
                s.append(",0,[");

                TRSFunctionApplication rhs = TRSTerm.createFunctionApplication(fun, args.subList(0, fun.getArity()));
                s.append(CoflocoHelper.exportFunapp(rhs, Optional.of(this.errorVar), this.returnVar));
                s.append("],[");

                for (int i=0; i < fun.getArity(); ++i) {
                    if (i > 0) s.append(",");
                    s.append(args.get(i).getName() + " >= 0");
                }
                s.append("]).");
                res.add(s.toString());
            }
            return res;
        }

        private List<String> makeInputOutputAnnotations() {
            List<String> res = new ArrayList<>();

            List<TRSVariable> args = new ArrayList<>();
            for (int i=0; i < this.rnts.getMaxArity(); ++i) {
                args.add(TRSTerm.createVariable(this.rnts.getArgumentName(i)));
            }
            List<TRSVariable> out = new ArrayList<>();
            out.add(this.returnVar);
            out.add(this.errorVar);

            for (FunctionSymbol fun : this.rnts.getDefinedSymbols()) {
                res.add(CoflocoHelper.exportInputOutput(fun, args.subList(0, fun.getArity()), out));
            }
            return res;
        }

        private String toCoFloCoString() {
            //generate CoFloCo input
            StringBuilder str = new StringBuilder();
            for (String eq : makeStartRules()) {
                str.append(eq + this.plainUtil.linebreak());
            }
            for (RntsRule rule : rnts.getRules()) {
                str.append(exportRule(rule));
            }
            for (String eq : makeTerminatingRules()) {
                str.append(eq + this.plainUtil.linebreak());
            }
            for (String eq : makeInputOutputAnnotations()) {
                str.append(eq + this.plainUtil.linebreak());
            }
            return str.toString();
        }

        public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
                throws AbortionException {
            //rename variables to friendly names
            this.rnts = (CpxRntsProblem)obl;
            this.rnts = RenamingHelper.normalize(this.rnts, true, true, null);
            this.fng = new FreshNameGenerator(rnts.getVariables(), FreshNameGenerator.APPEND_NUMBERS);
            this.returnVar = TRSTerm.createVariable(fng.getFreshName("Out", false));
            this.errorVar = TRSTerm.createVariable(fng.getFreshName("Err", false));
            this.plainUtil = new PLAIN_Util();

            //run CoFloCo
            String input = toCoFloCoString();
            List<String> output = CoflocoHelper.executeCoFloCo(input, CpxRntsToCoflocoProcessor.this.timeout, true, aborter);
            if (output == null) {
                return ResultFactory.unsuccessful("no cofloco output");
            }

            //parse result
            String result = CoflocoHelper.obtainAsymptoticResult(output);
            if (result == null) {
                return ResultFactory.unsuccessful("no cofloco result");
            }
            ComplexityValue res = CoflocoHelper.parseComplexity(result);
            if (res.equals(ComplexityValue.infinite())) {
                return ResultFactory.unsuccessful();
            } else {
                return ResultFactory.provedWithValue(ComplexityYNM.createUpper(res), new CoflocoProof(input,output));
            }
        }
    }


    private static class CoflocoProof extends CpxProof {
        private final String input;
        private final List<String> output;

        public CoflocoProof(final String i, final List<String> o) {
            input = i;
            output = o;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder s = new StringBuilder();
            s.append("Transformed the RNTS into cost relations for CoFloCo:" + o.paragraph());

            //iterate over newlines to use proper HTML linebreaks
            StringBuilder inputStr = new StringBuilder();
            for (String line : input.split("\\r?\\n")) {
                inputStr.append(o.escape(line) + o.linebreak());
            }
            s.append(o.indent(inputStr.toString()));

            s.append(o.paragraph());
            s.append(o.bold(o.escape("CoFloCo proof output:")));
            for (String line : output) {
                s.append(o.export(line) + o.linebreak());
            }
            return s.toString();
        }

    }
}
