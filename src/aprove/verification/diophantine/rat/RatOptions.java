package aprove.verification.diophantine.rat;

import java.io.*;
import java.math.*;

import aprove.cli.Generic.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;

/**
 *
 * @author bearperson
 * @version $Id$
 */
public class RatOptions extends CommandLineOptions {

    static enum Method {
        POT, MBYNVAR, MBYNFIX
    }

    private Method method = Method.MBYNVAR;   // -m MbyNfix
    private int rangeM=25, rangeN=5;          // -r 16:4
    private String satBackend = "SAT4J";      // -S MINISAT[Version=1]

    public RatOptions() {
        super();
    }

    @Override
    protected void setOne(char opt, String value) {
        switch(opt) {
        case 'm':
            try {
                this.method = Method.valueOf(value.toUpperCase());
            } catch (IllegalArgumentException noSuchValue) {
                // Make the message look a little nicer for the user
                throw new IllegalArgumentException("Error: method " + value + " not supported (yet?); aborting");
            }
            break;
        case 'r':
            String[] parts = value.split(":", 2);
            this.rangeM = Integer.parseInt(parts[0]);
            this.rangeN = Integer.parseInt(parts[1]);
            break;
        case 'S':
            this.satBackend = value;
            break;
        default:
            super.setOne(opt, value);
        }
    }

    @Override
    protected String getAppName() {
        return "AProVE Rational Solver";
    }

    @Override
    protected String getOptsSpec() {
        return super.getOptsSpec() + "m:r:S:";
    }

    @Override
    protected void printHelp() {
        super.printHelp();
        // char count:      12345678901234567890123456789012345678901234567890123456789012345678901234567890
        System.out.println("Rat-specific options:");
        System.out.println("  -S <backend>    SAT backend to use (e.g. MINISAT[Version=1])");
        System.out.println("  -m <method>     Specify method to use (PoT, MbyNvar, MbyNfix)");
        System.out.println("  -r <m>:<n>      Range over which to search for solutions");
        System.out.println("                    for PoT, solutions are searched from 2^m to 2^n");
        System.out.println("                    MbyNvar searches in {0..m}/{1..n}");
        System.out.println("                    MbyNfix searches in {0..m}/n");
    }

    @Override
    public ProblemExecutor getExecutor(Reader problemReader) {
        ProblemExecutor result;
        switch(this.method) {
        case POT:
            OPCSolver<PoT> potSolver = RatSolvHack.getPoTSolver(this.satBackend);
            OPCRange<PoT> potRange = new OPCRange<PoT>(PoT.create(BigInteger.ONE, BigInteger.valueOf(this.rangeM)),
                                                       PoT.create(BigInteger.ONE, BigInteger.valueOf(this.rangeN)));
            GPolyCoeffFactory<PoT> potCreator = new GPolyCoeffFactory<PoT>() {
                @Override
                public PoT fromInteger(BigInteger from) {
                    return PoT.create(from);
                }
            };
            result = new RatExecutor<PoT>(problemReader, potSolver, potRange, potCreator, this);
            break;
        case MBYNFIX: // FALLTHROUGH
        case MBYNVAR:
            OPCSolver<MbyN> mbynSolver = RatSolvHack.getMbyNSolver(this.satBackend, this.method == Method.MBYNFIX);
            OPCRange<MbyN> mbynRange = new OPCRange<MbyN>(MbyN.create(BigInteger.valueOf(this.rangeM)),
                                                          MbyN.create(BigInteger.valueOf(this.rangeN)));
            GPolyCoeffFactory<MbyN> mbynCreator = new GPolyCoeffFactory<MbyN>() {
                @Override
                public MbyN fromInteger(BigInteger from) {
                    return MbyN.create(from);
                }
            };
            result = new RatExecutor<MbyN>(problemReader, mbynSolver, mbynRange, mbynCreator, this);
            break;
         default:
             throw new IllegalArgumentException("Illegal Method!");
        }
        return result;
    }

}
