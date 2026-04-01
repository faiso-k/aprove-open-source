package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.math.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Works like SimplePolyConstraintsToCircuitConverter, but caches
 * some intermediate results such that we can get smaller circuits
 * even without using sharing formula factories.
 *
 * TODO check which way is faster
 *
 * TODO caching for Formula<Diophantine> as well
 *
 * Note: This case was previously known as
 * CachingSimplePolyConstraintsToCircuitConverter. Search for this
 * name if you are interested in the corresponding CVS history.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class CachingSPCToCircuitConverter extends
        PlainSPCToCircuitConverter {

    private static final Logger log = Logger.getLogger("aprove.verification.oldframework.Algebra.Polynomials.SatSearch.CachingSPCToCircuitConverter");

    // for logging
    private int polyHits = 0;
    private int polyMisses = 0;
    private int ipHits = 0;
    private int ipMisses = 0;

    // caches
    private final Map<SimplePolynomial, List<Formula<None>>> polynomialCircuits;
    private final Map<IndefinitePart, PolyCircuit> indefinitePartCircuits;

    private CachingSPCToCircuitConverter(FormulaFactory<None> formulaFactory,
            Map<String, BigInteger> ranges, BigInteger defaultRange, PoloSatConfigInfo config) {
        super(formulaFactory, ranges, defaultRange, config);
        this.polynomialCircuits = new HashMap<SimplePolynomial, List<Formula<None>>>();
        this.indefinitePartCircuits = new HashMap<IndefinitePart, PolyCircuit>();
    }

    public static CachingSPCToCircuitConverter create(FormulaFactory<None> formulaFactory,
            Map<String, BigInteger> ranges, BigInteger defaultRange, PoloSatConfigInfo config) {
        return new CachingSPCToCircuitConverter(formulaFactory,
                ranges, defaultRange, config);
    }

    @Override
    public Pair<Formula<None>, Map<String, PolyCircuit>> convert(Set<SimplePolyConstraint> spcs,
            Set<SimplePolyConstraint> searchStrictSpcs, Abortion aborter) throws AbortionException {
        Pair<Formula<None>, Map<String, PolyCircuit>> result = super.convert(spcs, searchStrictSpcs, aborter);

        // Actually, we have just extended this method for the sake of logging.
        if (Globals.DEBUG_FUHS) {
            CachingSPCToCircuitConverter.log.log(Level.FINE, "CachingSimplePolyConstraintsToCircuitConverter information:\n");
            CachingSPCToCircuitConverter.log.log(Level.FINE, "    polyHits    : " + this.polyHits + "\n");
            CachingSPCToCircuitConverter.log.log(Level.FINE, "    polyMisses  : " + this.polyMisses + "\n");
            CachingSPCToCircuitConverter.log.log(Level.FINE, "    ipHits      : " + this.ipHits + "\n");
            CachingSPCToCircuitConverter.log.log(Level.FINE, "    ipMisses    : " + this.ipMisses + "\n");
        }
        return result;
    }

    @Override
    protected List<Formula<None>> convertPolynomial(SimplePolynomial poly) {
        List<Formula<None>> result = this.polynomialCircuits.get(poly);
        if (Globals.DEBUG_FUHS) {
            if (result == null) {
                ++this.polyMisses;
            }
            else {
                ++this.polyHits;
            }
        }
        if (result == null) {
            result = super.convertPolynomial(poly);
            this.polynomialCircuits.put(poly, result);
        }
        return result;
    }

    @Override
    protected PolyCircuit convertIndefinitePart(IndefinitePart ip) {
        PolyCircuit result = this.indefinitePartCircuits.get(ip);
        if (Globals.DEBUG_FUHS) {
            if (result == null) {
                ++this.ipMisses;
            }
            else {
                ++this.ipHits;
            }
        }
        if (result == null) {
            result = super.convertIndefinitePart(ip);
            this.indefinitePartCircuits.put(ip, result);
        }
        return result;
    }
}
