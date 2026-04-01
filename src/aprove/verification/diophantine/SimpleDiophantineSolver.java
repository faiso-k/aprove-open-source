package aprove.verification.diophantine;


import java.io.*;
import java.math.*;
import java.util.*;

import aprove.input.Generated.diophantine.lexer.*;
import aprove.input.Generated.diophantine.node.*;
import aprove.input.Generated.diophantine.parser.*;
import aprove.input.Diophantine.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;


/**
 * This Diophantine solver solves a set of diophantine inequations,
 * but not a diophantine formula. It can therefore use any diophantine solver
 * including Sicstus, FD Search, and CiME.
 *
 * @author Patrick Kabasci
 * @version $Id$
 */
public class SimpleDiophantineSolver {

    public static Map<String, BigInteger> solve(Reader input, SearchAlgorithm searchAlg, boolean verbose, Abortion aborter)
            throws AbortionException {
        Pass p = new Pass();
        try {
            PushbackReader reader = new PushbackReader(input);
            Parser parser = new Parser(new Lexer(reader));
            Start tree = parser.parse();

            tree.apply(p);

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
        } catch (Exception e) {
            e.printStackTrace();
            System.err.println("ERROR: Unknown exception trying to parse input file; aborting\n-");
            return null;
        }

        List<SimplePolyConstraint> retList = p.getContraints();
        if (verbose) {
            System.out.println("Constraints:");
            for (SimplePolyConstraint spc : retList) {
                System.out.println("  " + spc);
            }
        }

        Map<String, BigInteger> retMap = null;

        Set<SimplePolyConstraint> constraintSet = new LinkedHashSet<SimplePolyConstraint>(retList);
        retMap = searchAlg.search(constraintSet, new LinkedHashSet<SimplePolyConstraint> (), aborter);
        if (retMap != null && searchAlg.introducesFreshVariables()) {
            Set<String> inputIndefs = SimplePolyConstraint.getIndefinites(constraintSet);
            retMap.keySet().retainAll(inputIndefs);
        }
        return retMap;
    }
}

