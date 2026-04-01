package aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers;

import java.io.*;
import java.math.*;
import java.util.*;
import java.util.logging.*;
import java.util.regex.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.SMTSearch.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.ExternalProcess.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

@NoParams
public class ExternalOPCSolver implements OPCSolver<MbyN>, StdoutChecker<Map<GPolyVar, MbyN>> {
    private static final Logger log = Logger.getLogger(ExternalOPCSolver.class.getName());
    private final static Pattern solutionMatcher =
        Pattern.compile("^\\+\\s+([^\\s=]+)\\s*=\\s*([0-9]+)(?:/([0-9]+))?\\s*$");


    private Ring<GPoly<MbyN, GPolyVar>> polyRing;
    private FlatteningVisitor<MbyN, GPolyVar> fvInner;
    private FlatteningVisitor<GPoly<MbyN, GPolyVar>, GPolyVar> fvOuter;

    @Override
    public void setPolyRing(Ring<GPoly<MbyN, GPolyVar>> polyRing) {
        this.polyRing = polyRing;
    }

    @Override
    public void setFvInner(FlatteningVisitor<MbyN, GPolyVar> fvInner) {
        this.fvInner = fvInner;
    }

    @Override
    public void setFvOuter(FlatteningVisitor<GPoly<MbyN, GPolyVar>, GPolyVar> fvOuter) {
        this.fvOuter = fvOuter;
    }

    /*
     * Our interpretation of the range:
     * We expect a single pair of integer MbyN values,
     * denoting the upper bound on numerator and denominator, respectively.
     * So a variable with bound (3, 2) can take the values
     * 0, 1/2, 1, 3/2
     *
     * We assume non-negativity constraints on all variables.
     */
    @Override
    public Map<GPolyVar, MbyN> solve(OrderPolyConstraint<MbyN> constraint,
            Map<GPolyVar, OPCRange<MbyN>> ranges, OPCRange<MbyN> defaultRange,
            Abortion aborter) throws AbortionException {
        AbsolutePositivenessQuantorKiller<MbyN> cv = new AbsolutePositivenessQuantorKiller<MbyN>(
                this.polyRing, this.fvInner.getMonoid(),
                this.fvOuter);
        OrderPolyConstraint<MbyN> newConstraint = constraint.visit(cv);

        StringBuilder buf = new StringBuilder();
        for(Map.Entry<GPolyVar, OPCRange<MbyN>> e: ranges.entrySet()) {
            GPolyVar var = e.getKey();
            List<Pair<MbyN, MbyN>> range = e.getValue().getList();
            Pair<MbyN, MbyN> rangeTuple = range.get(0);
            if (Globals.useAssertions) {
                assert range.size() == 1 : "uhh - what does that range mean?";
                assert rangeTuple.y.equals(MbyN.ONE) : "We only support bool per-variable ranges";
                assert rangeTuple.x.equals(MbyN.ONE) : "We only support bool per-variable ranges";
            }
            // x^2-x = 0 forces x to be 1 or 0
            buf.append(var.getName()).append("^2 + -1.").append(var.getName()).append("=0;\n");
        }
        buf.append(OPCStringifier.OPCtoString(newConstraint,
                PolyFormatter.MULTISOLVER, this.fvInner));

        ExternalOPCSolver.log.finest("Input to opcsolver: " + buf.toString());
        // Once we seriously use this in strategies, we should pass the range somehow
        // For now we don't, so the barcelona folks can set those themselves.
        return FileCheckerHelper.checkWithStdout(buf.toString(), aborter, this, "barcelonaRat");
    }

    @Override
    public String getInputTempSuffix() {
        return "rat";
    }

    @Override
    public String getTempPrefix() {
        return "opcsolver";
    }

    @Override
    public Map<GPolyVar, MbyN> readResult(BufferedReader result)
            throws IOException {
        String line;
        line = result.readLine();
        if (ExternalOPCSolver.log.isLoggable(Level.FINEST)) {
            ExternalOPCSolver.log.finest("result from OPCSolver: " + line);
        }
        if (line == null || !"+SOLUTION:".equals(line.trim())) {
            return null;
        }

        Map<GPolyVar, MbyN> solution = new LinkedHashMap<GPolyVar, MbyN>();
        while( (line=result.readLine()) != null) {
            if (ExternalOPCSolver.log.isLoggable(Level.FINEST)) {
                ExternalOPCSolver.log.finest("opcsolver sez: " + line);
            }
            if (line.equals("-")) {
                break; // End of output
            }
            Matcher match = ExternalOPCSolver.solutionMatcher.matcher(line);
            if (! match.matches()) {
                ExternalOPCSolver.log.warning("Unexpected line from OPCSolver: " + line);
                continue;
            }
            BigInteger numerator = new BigInteger(match.group(2));
            BigInteger denominator = BigInteger.ONE;
            if (match.group(3) != null) {
                denominator = new BigInteger(match.group(3));
            }
            GPolyVar key = new GAtomicVar(match.group(1));
            MbyN value = MbyN.create(numerator, denominator);
            solution.put(key, value);
        }
        return solution;
    }

    @Override
    public OPCSolver<MbyN> getCopy() {
        ExternalOPCSolver copy = new ExternalOPCSolver();
        copy.polyRing = this.polyRing;
        return copy;
    }

    @Override
    public Map<GPolyVar, MbyN> solve(OrderPolyConstraint<MbyN> constraint,
            Domain domain, Abortion aborter) throws AbortionException {
        throw new UnsupportedOperationException();
    }

}
