package aprove.verification.complexity.CpxRntsProblem.Processors;

import static aprove.verification.complexity.CpxIntTrsProblem.Structures.CpxIntTermHelper.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Optional;
import java.util.OptionalInt;
import java.util.Set;
import java.util.stream.Collectors;

import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Algorithms.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

/**
 * CoFloCo backend using an external cofloco binary for ITS analysis
 * (the ITS is first translated to cost relations for CoFloCo).
 *
 * @author mnaaf
 */
public class CoFloCoBackend implements IntTrsBackend {

    public static final boolean isInstalled = ProcessHelper.isInstalled("cofloco");


    private final int timeout;
    private final Abortion aborter;
    private final CpxRntsProblem rntsOriginal; //before renaming
    private final CpxRntsProblem rnts;

    //state (store results from CoFloCo run)
    private String input = null;
    private String result = null;
    private List<String> output = null;
    private Map<String,String> renamingMap;

    //caching to avoid parsing multiple times
    private ComplexityValue cachedCpx = null;
    private Optional<SimplePolynomial> cachedPoly = null;

    private FreshNameGenerator funFng = null;
    private StringBuilder o;


    public CoFloCoBackend(CpxRntsProblem r, Abortion a, int timeout) {
        this.timeout = timeout;
        this.aborter = a;
        this.rntsOriginal = r;
        this.renamingMap = new LinkedHashMap<>();
        this.rnts = RenamingHelper.normalize(r,true,false,renamingMap);
        this.funFng = new FreshNameGenerator(this.rnts.getDefinedSymbols(),FreshNameGenerator.APPEND_NUMBERS);
    }

    @Override
    public String getName() {
        return "CoFloCo";
    }

    //CoFloCo is not always applicable
    public static boolean isApplicable(CpxRntsProblem rnts) {
        return rnts.getRules().stream().allMatch(r -> r.getCost().isLinear());
    }

    //returns the single rhs or parses the COM-symbol and returns the COM-rhss
    private List<TRSFunctionApplication> getRhss(RntsRule rule) {
        TRSFunctionApplication rhs = (TRSFunctionApplication)rule.getRight();
        List<TRSFunctionApplication> res = new ArrayList<>();
        if (isComSymbol(rhs.getRootSymbol())) {
            for (TRSTerm arg : rhs.getArguments()) {
                res.add((TRSFunctionApplication)arg);
            }
        } else {
            res.add(rhs);
        }
        return res;
    }

    private String toCoFloCoString() {
        this.o = new StringBuilder();

        // the first rule is considered to be the start rule
        makeStartRules(this.rnts.getInitialSymbols());

        // export all rules
        for (RntsRule r : this.rnts.getRules()) {
            exportRule(r);
        }

        // add terminating rules to allow partial derivations
        makeTerminatingRules(this.rnts.getDefinedSymbols());

        return o.toString();
    }

    private void makeStartRules(Set<FunctionSymbol> startSymbols) {
        //find number of arguments needed
        OptionalInt maxArity = startSymbols.stream().mapToInt(fun -> fun.getArity()).max();
        if (!maxArity.isPresent()) return;

        //create lhs
        FunctionSymbol startFun = FunctionSymbol.create(this.funFng.getFreshName("start", false), maxArity.getAsInt());
        List<TRSVariable> args = new ArrayList<>();
        for (int i=0; i < maxArity.getAsInt(); ++i) {
            args.add(TRSTerm.createVariable(this.rnts.getArgumentName(i)));
        }
        TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(startFun, args);

        //create all rules
        for (FunctionSymbol fun : startSymbols) {
            o.append("eq(");
            o.append(CoflocoHelper.exportTermSimple(lhs));
            o.append(",0,[");

            TRSFunctionApplication rhs = TRSTerm.createFunctionApplication(fun, args.subList(0, fun.getArity()));
            o.append(CoflocoHelper.exportTermSimple(rhs));
            o.append("],[");

            for (int i=0; i < fun.getArity(); ++i) {
                if (i > 0) o.append(",");
                o.append(args.get(i).getName() + " >= 0");
            }
            o.append("]).\n");
        }
    }

    private void makeTerminatingRules(Set<FunctionSymbol> symbols) {
        for (FunctionSymbol fun : symbols) {
            //lhs
            List<TRSVariable> args = new ArrayList<>();
            for (int i=0; i < fun.getArity(); ++i) {
                args.add(TRSTerm.createVariable(this.rnts.getArgumentName(i)));
            }
            TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(fun, args);

            //no rhs (abort evaulation here)
            o.append("eq(");
            o.append(CoflocoHelper.exportTermSimple(lhs));
            o.append(",0,[],[]).\n");
        }
    }

    private void exportRule(RntsRule r) {
        o.append("eq(");
        o.append(CoflocoHelper.exportTermSimple(r.getLeft()));
        o.append(",");
        o.append(CoflocoHelper.exportCost(r.getCost()));
        o.append(",[");
        o.append(getRhss(r).stream().map(rhs -> CoflocoHelper.exportTermSimple(rhs)).collect(Collectors.joining(",")));
        o.append("],[");
        o.append(r.getConstraints().stream().map(c -> CoflocoHelper.exportConstraint(c.getConstraintTerm())).collect(Collectors.joining(",")));
        o.append("]).\n");
    }

    //undo the renaming performed by RenamingHelper
    private SimplePolynomial renameVariables(SimplePolynomial bound) {
        Map<String,SimplePolynomial> submap = new HashMap<>();
        for (Entry<String,String> entry : this.renamingMap.entrySet()) {
            submap.put(entry.getKey(), SimplePolynomial.create(entry.getValue()));
        }
        bound = bound.substitute(submap);

        //sanity check
        for (String var : bound.getVariables()) {
            assert rntsOriginal.hasVariable(TRSTerm.createVariable(var));
        }
        return bound;
    }

    @Override
    public boolean run() {
        this.cachedCpx = null;
        this.cachedPoly = null;
        if (!isApplicable(this.rnts)) {
            return false;
        }
        this.input = toCoFloCoString();
        this.output = CoflocoHelper.executeCoFloCo(this.input, this.timeout, false, this.aborter);
        if (this.output == null) {
            return false;
        }
        this.result = CoflocoHelper.obtainConcreteResult(this.output);
        return true;
    }

    @Override
    public String getInput() {
        return this.input;
    }

    @Override
    public List<String> getOutput() {
        return this.output;
    }

    @Override
    public ComplexityValue getComplexity() {
        if (this.cachedCpx != null) {
            return this.cachedCpx;
        }
        if (this.result == null) {
            return ComplexityValue.infinite();
        }
        if (this.result.trim().equals("inf")) {
            return ComplexityValue.infinite();
        }
        this.cachedCpx = PUBSParser.parse(this.result);
        return this.cachedCpx;
    }

    @Override
    public Optional<SimplePolynomial> getPolynomialBound() {
        if (this.cachedPoly != null) {
            return this.cachedPoly;
        }
        if (this.result == null) {
            return Optional.empty();
        }
        if (this.result.trim().equals("inf")) {
            return Optional.empty();
        }
        try {
            SimplePolynomial res = PUBSParser.parseAsPolynomial(this.result);
            res = renameVariables(res);
            this.cachedPoly = Optional.of(res);
        } catch (NotRepresentableAsPolynomialException e) {
            this.cachedPoly = Optional.empty();
        }
        return this.cachedPoly;
    }

    public static String toCoFloCo(CpxRntsProblem rnts) {
        CoFloCoBackend cofloco = new CoFloCoBackend(rnts, null, 0);
        return cofloco.toCoFloCoString();
    }
}
