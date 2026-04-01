package aprove.verification.complexity.CpxRntsProblem.Processors;

import java.util.ArrayList;
import java.util.Collections;
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
 * Translates a RNTS which considers only *complete* derivations into cost
 * relations (CES) which are then analyzed for their complexity class by CoFloCo.
 *
 *
 * The translation is straight-forward, as cost relations allow to express
 * nested function calls. Example:
 *
 * RNTS: f(x) -> 42 [constraints]
 * CES: eq(f(X,OutF), 1, [], [OutF = 42, constraints]).
 *
 * RNTS: f(x,y) -> g(h(x),y) [constraints]
 * CES: eq(f(X,Y,OutF), 1, [h(X,OutH),g(OutH,y,OutG)], [OutF=OutG, constraints]).
 *
 * Here, a new argument is introduced that is used as return value. This can
 * be used to model nested function calls like h and g above.
 *
 * @note only applicable if `allowsPartialDerivations` is false
 *
 * @author mnaaf
 *
 */
public class CpxRntsCompleteToCoflocoProcessor extends ProcessorSkeleton {

    //options
    private final int timeout;

    //arguments that can be passed from the strategy file
    public static class Arguments {
        public int timeout = 0;
    }

    @ParamsViaArgumentObject
    public CpxRntsCompleteToCoflocoProcessor(final Arguments arguments) {
        this.timeout = arguments.timeout;
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if (!CoFloCoBackend.isInstalled) {
            return false;
        }
        return (obl instanceof CpxRntsProblem &&
                !((CpxRntsProblem)obl).allowsPartialDerivations());
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
            throws AbortionException {
        CpxRntsCompleteToCoflocoWorker worker = new CpxRntsCompleteToCoflocoWorker();
        Result res = worker.process(obl, oblNode, aborter, rti);
        return res;
    }

    /**
     * Helper class to encapsulate the instance-dependent state of the
     * computation by the processor.
     */
    private class CpxRntsCompleteToCoflocoWorker {
        private CpxRntsProblem rnts = null;
        private FreshNameGenerator fng = null;
        private TRSVariable returnVar = null;
        private Export_Util plainUtil = null;

        private TRSVariable createResultVariable(Position pos) {
            StringBuilder name = new StringBuilder("Ret");
            for (Integer n : pos) {
                name.append(n);
            }
            String res = this.fng.getFreshName(name.toString(), false);
            return TRSTerm.createVariable(res);
        }

        private String exportRhs(RntsRule rule) {
            TRSTerm term = rule.getRight();
            Set<Position> positions = new TreeSet<>(new InnerMostPositionComparator());
            positions.addAll(term.getPositions());

            //replace all inner calls
            List<Pair<TRSFunctionApplication,TRSVariable>> calls = new ArrayList<>();
            for (Position pos : positions) {
                TRSTerm subterm = term.getSubterm(pos);
                if (subterm.isVariable()) continue;

                TRSFunctionApplication funapp = (TRSFunctionApplication)subterm;
                if (!rnts.isDefinedSymbol(funapp.getRootSymbol())) continue;

                TRSVariable var = createResultVariable(pos);
                calls.add(new Pair<>(funapp,var));
                term = term.replaceAt(pos,var);
            }

            //export calls to string
            List<String> callsStr = calls.stream().map(pair -> CoflocoHelper.exportFunapp(pair.x,Optional.empty(),pair.y)).collect(Collectors.toList());
            StringBuilder res = new StringBuilder();
            res.append("[");
            res.append(String.join(",", callsStr));
            res.append("],[");

            //add constraint for the return value
            TRSTerm returnGuard = TRSTerm.createFunctionApplication(CpxIntTermHelper.fEq, this.returnVar, term);

            //export constraints to string
            res.append(CoflocoHelper.exportConstraint(returnGuard));
            for (Constraint cond : rule.getConstraints()) {
                res.append(",");
                res.append(CoflocoHelper.exportConstraint(cond.getConstraintTerm()));
            }
            res.append("]");
            return res.toString();
        }

        private String exportRule(RntsRule rule) {
            String res = "eq(";
            res += CoflocoHelper.exportFunapp(rule.getLeft(), Optional.empty(), this.returnVar) + ",";
            res += CoflocoHelper.exportCost(rule.getCost()) + ",";
            return res + exportRhs(rule) + ").";
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
                s.append(CoflocoHelper.exportFunapp(rhs, Optional.empty(), this.returnVar));
                s.append("],[");

                for (int i=0; i < fun.getArity(); ++i) {
                    if (i > 0) s.append(",");
                    s.append(args.get(i).getName());
                    s.append(" >= 0");
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
            List<TRSVariable> out = Collections.singletonList(this.returnVar);

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
                str.append(exportRule(rule) + this.plainUtil.linebreak());
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
            this.plainUtil = new PLAIN_Util();

            //run CoFloCo
            String input = toCoFloCoString();
            List<String> output = CoflocoHelper.executeCoFloCo(input, CpxRntsCompleteToCoflocoProcessor.this.timeout, true, aborter);
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
                return ResultFactory.provedWithValue(ComplexityYNM.createUpper(res), new CompleteCoflocoProof(input,output));
            }
        }
    }

    private static class CompleteCoflocoProof extends CpxProof {
        private final String input;
        private final List<String> output;

        public CompleteCoflocoProof(final String i, final List<String> o) {
            input = i;
            output = o;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder s = new StringBuilder();
            s.append("Transformed the RNTS (where only complete derivations are relevant) into cost relations for CoFloCo:" + o.paragraph());

            //iterate over newlines to use proper HTML linebreaks
            StringBuilder inputStr = new StringBuilder();
            for (String line : input.split("\\r?\\n")) {
                inputStr.append(o.escape(line) + o.linebreak());
            }
            s.append(o.indent(inputStr.toString()));

            s.append(o.paragraph());
            s.append(o.bold(o.escape("CoFloCo proof output:")));
            for (String line : output) {
                s.append(o.escape(line) + o.linebreak());
            }
            return s.toString();
        }

    }


}
