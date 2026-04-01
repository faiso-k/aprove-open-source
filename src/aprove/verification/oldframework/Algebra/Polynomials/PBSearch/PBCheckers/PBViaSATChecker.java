package aprove.verification.oldframework.Algebra.Polynomials.PBSearch.PBCheckers;

import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Polynomials.PBSearch.*;
import aprove.verification.oldframework.Algebra.Polynomials.SatSearch.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/**
 * Check Pseudo Boolean constraints using SatSearch.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class PBViaSATChecker implements PBChecker {

    @Override
    public int[] check(Collection<SimplePolyConstraint> linSpcs, SimplePolynomial maximizeMe, int maxVar, Abortion aborter)
            throws AbortionException {
        Set<SimplePolyConstraint> linSpcsForSearch;
        if (linSpcs instanceof Set) {
            linSpcsForSearch = (Set<SimplePolyConstraint>) linSpcs;
        }
        else {
            linSpcsForSearch = new LinkedHashSet<SimplePolyConstraint>(linSpcs);
        }
        MINISATEngine.Arguments args = new MINISATEngine.Arguments();
        args.version = 2;
        MINISATEngine e = new MINISATEngine(args);
        FormulaFactory<None> factory = new FullSharingFlatteningFactory<None>();
        PoloSatConverter conv = PlainSPCToCircuitConverter.create(factory,
                Collections.<String, BigInteger>emptyMap(), BigInteger.ONE, new PoloSatConfigInfo());
        SatSearch satSearch = SatSearch.create(e, conv);
        Map<String, BigInteger> sol = satSearch.search(linSpcsForSearch, Collections.<SimplePolyConstraint>emptySet(), null, aborter);
        int[] result = new int[sol.size() + 1];
        for (Entry<String, BigInteger> et : sol.entrySet()) {
            String x = et.getKey().substring(1);
            int index = Integer.parseInt(x);
            BigInteger value = et.getValue();
            result[index] = (value.signum() > 0) ? index : -index;
        }
        return result;
    }

}
