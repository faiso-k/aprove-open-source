package aprove.verification.complexity.CpxRntsProblem.Processors;

import static aprove.verification.complexity.CpxIntTrsProblem.Structures.CpxIntTermHelper.*;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.CpxIntTrsProblem.Exceptions.*;
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
 * PUBS backend using an external pubs binary for ITS analysis
 * (the ITS is first translated to cost relations for PUBS).
 *
 * @note as PUBS is not publicly available, this is currently not used.
 *
 * @author mnaaf
 */
public class PUBSBackend implements IntTrsBackend {

//    public static final boolean isInstalled = ProcessHelper.isInstalled("pubs_static");

    private final int timeout; //in ms
    private final Abortion aborter;
    private final CpxRntsProblem rntsOriginal; //before renaming
    private final CpxRntsProblem rnts;
    private String input = null;
    private String result = null;
    private List<String> output = null;

    //caching to avoid parsing multiple times
    private ComplexityValue cachedCpx = null;
    private Optional<SimplePolynomial> cachedPoly = null;

    private FreshNameGenerator funFng = null;
    private StringBuilder o;

    public PUBSBackend(CpxRntsProblem r, Abortion a, int timeout) {
        this.timeout = timeout;
        this.aborter = a;
        this.rntsOriginal = r;
        this.rnts = RenamingHelper.normalize(r,true,false,null);
        this.funFng = new FreshNameGenerator(this.rnts.getDefinedSymbols(),FreshNameGenerator.APPEND_NUMBERS);
    }

    @Override
    public String getName() {
        return "PUBS";
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

    private String toPUBSString() {
        this.o = new StringBuilder();

        // the first rule is considered to be the start rule
        buildStartEq(this.rnts.getInitialSymbols());

        // export all rules
        for (RntsRule r : this.rnts.getRules()) {
            exportRule(r);
        }

        return o.toString();
    }

    private void buildStartEq(Set<FunctionSymbol> startSymbols) {
        o.append("eq(");
        o.append(this.funFng.getFreshName("pubs_start", false));
        o.append("(");
        StringBuilder sb = new StringBuilder();
        boolean first = true;
        for (FunctionSymbol fs : startSymbols) {
            int l = fs.getArity();
            if (sb.length() > 0) {
                sb.append(",");
            }
            sb.append(fs.getName());
            if (l > 0) {
                sb.append("(");
                for (int i = 0; i < l; ++i) {
                    String v = this.rnts.getArgumentName(i);
                    if (i > 0) {
                        sb.append(",");
                    }
                    sb.append(v);
                    if (i > 0 || !first) {
                        o.append(",");
                    }
                    o.append(v);
                }
                sb.append(")");
            }
            first = false;
        }
        o.append("),0,[");
        o.append(sb.toString());
        o.append("],[]).\n");
    }

    private void exportRule(RntsRule r) {
        o.append("eq(");
        exportCallTerm(r.getLeft());
        o.append(",");
        exportCost(r.getCost());
        o.append(",[");
        LinkedHashSet<Constraint> constraints = new LinkedHashSet<>();
        assert r.getConstraints() != null;
        constraints.addAll(r.getConstraints());
        boolean first = true;
        for (TRSFunctionApplication rhs : getRhss(r)) {
            if (first) {
                first = false;
            } else {
                o.append(",");
            }
            exportCallTerm(rhs);
        }
        first = true;
        o.append("],[");
        for (Constraint c : constraints) {
            if (first) {
                first = false;
            } else {
                o.append(",");
            }
            exportConstraint(c);
        }
        o.append("]).\n");
    }

    private void exportCost(SimplePolynomial poly) {
        FunctionSymbol nat = FunctionSymbol.create("nat", 1);
        TRSTerm cost = poly.toTerm();
        Map<TRSVariable,TRSTerm> subs = new LinkedHashMap<>();
        for (TRSVariable v : cost.getVariables()) {
            subs.put(v, TRSTerm.createFunctionApplication(nat, v));
        }
        cost = cost.applySubstitution(TRSSubstitution.create(ImmutableCreator.create(subs)));
        o.append(IDPExport.exportTerm(cost, new PLAIN_Util(), IDPPredefinedMap.DEFAULT_MAP));
    }

    private void exportCallTerm(TRSFunctionApplication t) {
        FunctionSymbol fs = t.getRootSymbol();
        o.append(fs.getName());
        if (fs.getArity() == 0) {
            return;
        }
        o.append("(");
        boolean first = true;
        for (TRSTerm arg : t.getArguments()) {
            if (first) {
                first = false;
            } else {
                o.append(",");
            }
            exportIntTerm(arg);
        }
        o.append(")");
    }

    private void exportConstraint(Constraint c) {
        assert c != null;
        TRSFunctionApplication t = c.getConstraintTerm();
        FunctionSymbol op = t.getRootSymbol();
        if (fEq.equals(op)) {
            exportIntTerm(t.getArgument(0));
            o.append("=");
            exportIntTerm(t.getArgument(1));
            return;
        }
        if (fGe.equals(op)) {
            exportIntTerm(t.getArgument(0));
            o.append(">=");
            exportIntTerm(t.getArgument(1));
            return;
        }
        if (fLe.equals(op)) {
            exportIntTerm(t.getArgument(1));
            o.append(">=");
            exportIntTerm(t.getArgument(0));
            return;
        }
        if (fLt.equals(op)) {
            exportIntTerm(t.getArgument(1));
            o.append(">=1+(");
            exportIntTerm(t.getArgument(0));
            o.append(")");
            return;
        }
        if (fGt.equals(op)) {
            exportIntTerm(t.getArgument(0));
            o.append(">=1+(");
            exportIntTerm(t.getArgument(1));
            o.append(")");
            return;
        }
        System.err.println("Don't know how to export " + op);
        System.err.println("For the (renamed) Rnts:");
        System.err.println(this.rnts);
        throw new RuntimeException("Don't know how to export " + op);
    }

    private void exportIntTerm(TRSTerm t) {
        if (t.isVariable()) {
            o.append(((TRSVariable)t).getName());
        } else {
            exportIntFunapp((TRSFunctionApplication)t);
        }
    }

    private void exportIntFunapp(TRSFunctionApplication t) {
        FunctionSymbol op = t.getRootSymbol();
        BigInteger i = getIntegerValue(t);
        if (i != null) {
            o.append("(" + op.getName() + ")");
            return;
        }
        if (fAdd.equals(op) || fMul.equals(op) || fSub.equals(op)) {
            o.append("(");
            exportIntTerm(t.getArgument(0));
            o.append(op.getName());
            exportIntTerm(t.getArgument(1));
            o.append(")");
            return;
        }
        if (fUnaryMinus.equals(op)) {
            o.append("(0-");
            exportIntTerm(t.getArgument(0));
            o.append(")");
            return;
        }
        System.err.println("Don't know how to export " + op);
        System.err.println("For the (renamed) Rnts:");
        System.err.println(this.rnts);
        throw new RuntimeException("Don't know how to export " + op);
    }

    //PUBS names the variables A,B,... rename to original names
    private SimplePolynomial renameVariables(SimplePolynomial bound) {
        //FIXME: handle more than 26 variables (how does PUBS handle them?)
        char ord = 'A';
        Map<String,SimplePolynomial> submap = new HashMap<>();
        for (int i=0; i < rnts.getMaxArity(); ++i) {
            String originalName = rntsOriginal.getArgumentName(i);
            submap.put(String.valueOf((char)(ord+i)), SimplePolynomial.create(originalName));
        }
        bound = bound.substitute(submap);

        //sanity check
        for (String var : bound.getVariables()) {
            assert rntsOriginal.hasVariable(TRSTerm.createVariable(var));
        }
        return bound;
    }

    private boolean executePUBS() {
        try {
            // create input file
            File file = File.createTempFile("aprove", ".pubs");
            file.deleteOnExit();
            // write ITS to input file
            Writer inputWriter = new OutputStreamWriter(new FileOutputStream(file));
            inputWriter.write(this.input);
            inputWriter.close();
            // construct the invocation
            List<String> parameters = new ArrayList<String>();
            parameters.add("pubs_static");
            parameters.add("-file");
            parameters.add(file.getCanonicalPath());
            // start the process
            ProcessBuilder processBuilder = new ProcessBuilder(parameters.toArray(new String[parameters.size()]));
            processBuilder.redirectErrorStream(true);
            Process process = processBuilder.start();
            TrackerFactory.process(aborter, process);
            // wait with timeout (and possibly kill process)
            if (timeout == 0) {
                process.waitFor();
            } else if (!process.waitFor(this.timeout, TimeUnit.MILLISECONDS)) {
                process.destroyForcibly();
                return false;
            }
            // read the output
            List<String> proofText = new LinkedList<>();
            try (BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()))) {
                for (String line = reader.readLine(); line != null; line = reader.readLine()) {
                    proofText.add(line);
                }
            } catch (IOException e) {
                //ignore (most probably we got killed by a timeout)
            }
            // done
            this.output = proofText;
            return true;
        } catch (IOException | InterruptedException ex) {
            ex.printStackTrace();
            return false;
        }
    }

    private void obtainResult() {
        for (String line : this.output) {
            if (line.contains("Non Asymptotic Upper Bound:")) {
                Pattern p = Pattern.compile("Upper Bound:(.*)$");
                Matcher m = p.matcher(line);
                if (m.find()) {
                    this.result = m.group(1);
                    break;
                }
            }
        }
        //check for PUBS failures
        if (this.result != null && (this.result.contains("c(maximize_failed)")
                || this.result.contains("c(failed("))) {
            this.result = null;
        }
    }

    @Override
    public boolean run() {
        this.cachedCpx = null;
        this.cachedPoly = null;
        this.input = toPUBSString();
        if (!executePUBS()) {
            return false;
        }
        obtainResult();
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
        try {
            SimplePolynomial res = PUBSParser.parseAsPolynomial(this.result);
            res = renameVariables(res);
            this.cachedPoly = Optional.of(res);
        } catch (NotRepresentableAsPolynomialException e) {
            this.cachedPoly = Optional.empty();
        }
        return this.cachedPoly;
    }

    public static String toPUBS(CpxRntsProblem rnts) {
        PUBSBackend pubs = new PUBSBackend(rnts, null, 0);
        return pubs.toPUBSString();
    }
}
