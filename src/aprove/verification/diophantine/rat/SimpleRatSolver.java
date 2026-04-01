package aprove.verification.diophantine.rat;

import java.io.*;
import java.util.*;

import aprove.input.Generated.diophantine.lexer.*;
import aprove.input.Generated.diophantine.node.*;
import aprove.input.Generated.diophantine.parser.*;
import aprove.input.Diophantine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.OPCSolvers.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;

/**
 *
 * @author bearperson
 * @version $Id$
 */
public class SimpleRatSolver {
    public static <C extends GPolyCoeff> Map<String, String> solve(
            Reader input, OPCSolver<C> solver, OPCRange<C> range, GPolyCoeffFactory<C> creator,
            boolean verbose, Abortion aborter)
            throws AbortionException {
        GPolyPass<C> pass;

        try {
            PushbackReader reader = new PushbackReader(input);
            Parser parser = new Parser(new Lexer(reader));
            Start tree = parser.parse();
            pass = new GPolyPass<C>(creator);
            tree.apply(pass);
        } catch (IOException e) {
            System.err.println(e.toString());
            System.err.println("ERROR: Could not open input file; aborting\n-");
            return null;
        } catch (ParserException e) {
            System.err.println(e.toString());
            System.err.println("ERROR: Could not parse input file; aborting\n-");
            return null;
        } catch (LexerException e) {
            System.err.println(e.toString());
            System.err.println("ERROR: Could not lex input file; aborting\n-");
            return null;
        } catch (RuntimeException e) {
            e.printStackTrace();
            System.err.println("ERROR: Unknown exception trying to parse input file; aborting\n-");
            return null;
        }

        OrderPolyConstraint<C> constraints = pass.getConstraints();

        if (verbose) {
            System.out.println("Constraints:");
            System.out.println(constraints.toString());
        }

        Map<GPolyVar, OPCRange<C>> nothingSpecific = new LinkedHashMap<GPolyVar, OPCRange<C>>();

        Map<GPolyVar, C> retMap = solver.solve(constraints, nothingSpecific, range, aborter);
        if (retMap == null) {
            return null;
        }

        Map<String, String> result = new LinkedHashMap<String, String>();
        for(Map.Entry<GPolyVar, C> e: retMap.entrySet()) {
            GPolyVar var = e.getKey();
            C value = e.getValue();
            result.put(var.toString(), value.toString());
        }
        return result;

    }
}
