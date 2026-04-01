package aprove.verification.complexity.CpxRntsProblem.Processors;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Processors.*;
import aprove.verification.complexity.CpxIntTrsProblem.Processors.KoATParser.*;
import aprove.verification.complexity.CpxIntTrsProblem.Structures.*;
import aprove.verification.complexity.CpxRntsProblem.*;
import aprove.verification.complexity.CpxRntsProblem.Algorithms.*;
import aprove.verification.complexity.CpxRntsProblem.Structures.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import immutables.*;

/**
 * KoAT backend using an external koat binary for ITS analysis.
 * This allows to obtain the actual polynomial bound found by KoAT.
 *
 * @author mnaaf
 */
public class KoATBackend implements IntTrsBackend {

    public static final boolean isInstalled = ProcessHelper.isInstalled("koat");


    private final int timeout; //in ms
    private final Abortion aborter;
    private final CpxRntsProblem rntsOriginal; //before renaming
    private CpxRntsProblem rnts;
    private String input = null;
    private String result = null;
    private List<String> output = null;

    //caching to avoid parsing multiple times
    private ComplexityValue cachedCpx = null;
    private Optional<SimplePolynomial> cachedPoly = null;

    public KoATBackend(final CpxRntsProblem r, Abortion a, int timeout) {
        this.timeout = timeout;
        this.aborter = a;
        this.rntsOriginal = r;
        this.rnts = RenamingHelper.normalize(r,false,false,null);
        ensureValidStart();
    }

    @Override
    public String getName() {
        return "KoAT";
    }

    private TRSFunctionApplication buildStandardFunapp(FunctionSymbol fun) {
        ArrayList<TRSTerm> args = new ArrayList<>();
        for (int i=0; i < fun.getArity(); ++i) {
            args.add(TRSTerm.createVariable(this.rnts.getArgumentName(i)));
        }
        return TRSTerm.createFunctionApplication(fun, args);
    }

    private void ensureValidStart() {
        Set<FunctionSymbol> initial = this.rnts.getInitialSymbols();
        Set<FunctionSymbol> rhsFuns = this.rnts.getFunctionSymbolsOnRhs();
        if (initial.size() == 1 && !rhsFuns.contains(initial.iterator().next())) {
            return; //initial symbol is already valid
        }
        //generate start symbol
        FreshNameGenerator fng = new FreshNameGenerator(rnts.getFunctionSymbols(),FreshNameGenerator.VARIABLES);
        String startName = fng.getFreshName("start", false);
        int startArity = 0;
        for (FunctionSymbol fun : initial) {
            startArity = Math.max(startArity,fun.getArity());
        }
        FunctionSymbol startFun = FunctionSymbol.create(startName, startArity);
        //generate start rules
        Set<RntsRule> rules = new LinkedHashSet<>();
        TRSFunctionApplication lhs = buildStandardFunapp(startFun);
        for (FunctionSymbol fun : initial) {
            rules.add(RntsRule.createUnsafe(lhs, buildStandardFunapp(fun), SimplePolynomial.ZERO, ImmutableCreator.create(new LinkedHashSet<>())));
        }
        rules.addAll(this.rnts.getRules());
        this.rnts = this.rnts.cloneWithNewRules(ImmutableCreator.create(rules),ImmutableCreator.create(Collections.singleton(startFun)));
    }

    private String toPolyString(Export_Util eu, TRSTerm term) {
        try {
            return CpxIntTermHelper.toSimplePolynomial(term).export(eu);
        } catch (NotRepresentableAsPolynomialException e) {
            System.err.println("WARNING: Koat export of polynomial term " + term + " failed");
            return IDPExport.exportTerm(term, eu, IDPPredefinedMap.DEFAULT_MAP);
        }
    }

    private String toKoATRhs(Export_Util eu, TRSFunctionApplication funapp) {
        StringBuilder s = new StringBuilder();
        s.append(funapp.getName() + "(");
        for (int i=0; i < funapp.getRootSymbol().getArity(); ++i) {
            if (i > 0) s.append(",");
            s.append(toPolyString(eu, funapp.getArgument(i)));
        }
        s.append(")");
        return s.toString();
    }

    private String toKoATConstraint(Export_Util eu, TRSTerm term) {
        if (term.equals(CpxIntTermHelper.TRUE)) {
            return "0 >= 0";
        } else if (term.equals(CpxIntTermHelper.FALSE)) {
            return "0 >= 1";
        }

        TRSFunctionApplication fun = (TRSFunctionApplication)term;
        FunctionSymbol f = fun.getRootSymbol();
        if (f.getArity() == 2) {
            String lhsString = toPolyString(eu, fun.getArgument(0));
            String rhsString = toPolyString(eu, fun.getArgument(1));
            if (f.equals(CpxIntTermHelper.fLe)) {
                return lhsString + " <= " + rhsString;
            } else if (f.equals(CpxIntTermHelper.fLt)) {
                return lhsString + " < " + rhsString;
            } else if (f.equals(CpxIntTermHelper.fGe)) {
                return lhsString + " >= " + rhsString;
            } else if (f.equals(CpxIntTermHelper.fGt)) {
                return lhsString + " > " + rhsString;
            } else if (f.equals(CpxIntTermHelper.fEq)) {
                return lhsString + " = " + rhsString;
            } else if (f.equals(CpxIntTermHelper.fNeq)) {
                return lhsString + " != " + rhsString;
            }
        }
        System.err.println("Export of constraint symbol " + f + " to KoAT not yet implemented!");
        System.err.println("For the (renamed) Rnts:");
        System.err.println(this.rnts);
        throw new RuntimeException("Export of constraint symbol " + f + " to KoAT not yet implemented!");
    }

    private String toKoATString(RntsRule rule) {
        Export_Util eu = new PLAIN_Util();
        StringBuilder s = new StringBuilder();
        //lhs
        s.append(IDPExport.exportTerm(rule.getLeft(), eu, IDPPredefinedMap.DEFAULT_MAP));
        if (rule.getLeft().getArguments().isEmpty()) {
            s.append("()");
        }
        //cost
        s.append(" -{0,");
        s.append(rule.getCost().export(eu));
        s.append("}> ");
        //rhs (including COM_n)
        assert !rule.getRight().isVariable();
        TRSFunctionApplication rhs = (TRSFunctionApplication)rule.getRight();
        if (CpxIntTermHelper.isComSymbol(rhs.getRootSymbol())) {
            s.append(rhs.getRootSymbol().getName() + "(");
            for (int i=0; i < rhs.getRootSymbol().getArity(); ++i) {
                if (i > 0) s.append(",");
                assert !rhs.getArgument(i).isVariable();
                s.append(toKoATRhs(eu, (TRSFunctionApplication)rhs.getArgument(i)));
            }
            s.append(")");
        } else {
            s.append(toKoATRhs(eu,rhs));
        }
        //guard
        if (!rule.getConstraints().isEmpty()) {
            s.append(" :|: ");
            Iterator<Constraint> iter = rule.getConstraints().iterator();
            while (iter.hasNext()) {
                s.append(toKoATConstraint(eu, iter.next().getConstraintTerm()));
                if (iter.hasNext()) s.append(eu.escape(" && "));
            }
        }
        return s.toString();
    }

    private String toKoAT() {
        assert this.rnts.getInitialSymbols().size() == 1;
        String startFun = rnts.getInitialSymbols().iterator().next().getName();
        String newline = System.lineSeparator();
        //output in koat format
        StringBuilder sb = new StringBuilder();
        sb.append("(GOAL COMPLEXITY)" + newline);
        sb.append("(STARTTERM (FUNCTIONSYMBOLS ");
        sb.append(startFun);
        sb.append("))" + newline);
        sb.append("(VAR");
        for (TRSVariable x: this.rnts.getVariables()) {
            sb.append(" " + x.getName());
        }
        sb.append(")" + newline);
        sb.append("(RULES" + newline);
        for (RntsRule rule: this.rnts.getRules()) {
            sb.append(toKoATString(rule) + newline);
        }
        sb.append(")" + newline);
        return sb.toString();
    }

    //koat names the variables ar_0 .. ar_k, rename to original names
    private SimplePolynomial renameVariables(SimplePolynomial bound) {
        Map<String,SimplePolynomial> submap = new HashMap<>();
        for (int i=0; i < rnts.getMaxArity(); ++i) {
            String originalName = rntsOriginal.getArgumentName(i);
            submap.put("ar_"+i, SimplePolynomial.create(originalName));
            submap.put("Ar_"+i, SimplePolynomial.create(originalName));
        }
        bound = bound.substitute(submap);

        //sanity check
        for (String var : bound.getVariables()) {
            if (!rntsOriginal.hasVariable(TRSTerm.createVariable(var))) {
                System.err.println("ERROR: Unknown variable in KoAT bound: " + var + " (in " + bound + ")");
                System.err.println("Input was:");
                System.err.println(this.input);
            }
            assert rntsOriginal.hasVariable(TRSTerm.createVariable(var)) : "Unknown variable in KoAT bound: " + var + " (in " + bound + ")";
        }
        return bound;
    }

    @Override
    public boolean run() {
        this.cachedCpx = null;
        this.cachedPoly = null;
        this.input = toKoAT();

        //run with reasonable timeout
        CpxIntTrsToKoATProcessor.Arguments args = new CpxIntTrsToKoATProcessor.Arguments();
        args.timeout = this.timeout;
        CpxIntTrsToKoATProcessor proc = new CpxIntTrsToKoATProcessor(args);

        List<String> proof = proc.obtainProof(this.input, this.aborter);
        if (proof != null) {
            this.result = proc.obtainResult(proof);
        }
        this.output = proof;
        return proof != null;
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
        this.cachedCpx = KoATParser.parse(this.result);
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
        try {
            SimplePolynomial res = KoATParser.parseAsPolynomial(this.result);
            res = renameVariables(res);
            this.cachedPoly = Optional.of(res);
        } catch (NonConstantExponentException e) {
            this.cachedPoly = Optional.empty();
        }
        return this.cachedPoly;
    }

}
