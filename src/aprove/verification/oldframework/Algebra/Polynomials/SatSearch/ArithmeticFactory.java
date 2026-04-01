package aprove.verification.oldframework.Algebra.Polynomials.SatSearch;

import java.util.*;

import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * @author Carsten Fuhs
 * @version $Id$
 */
public interface ArithmeticFactory {
    Formula<None> buildEQCircuit(List<? extends Formula<None>> xs, List<? extends Formula<None>> ys);
    Pair<Formula<None>, Formula<None>> buildGECircuit(List<? extends Formula<None>> xs, List<? extends Formula<None>> ys);
    Formula<None> buildGTCircuit(List<? extends Formula<None>> xs, List<? extends Formula<None>> ys);

    //public List<Formula<None>> buildPlusCircuit(List<? extends Formula<None>> xs, List<? extends Formula<None>> ys);
    //public List<Formula<None>> buildTimesCircuit(List<? extends Formula<None>> xs, List<? extends Formula<None>> ys);

    PolyCircuit buildPlusCircuit(PolyCircuit xs, PolyCircuit ys);
    PolyCircuit buildTimesCircuit(PolyCircuit xs, PolyCircuit ys);

    PolyCircuit buildMixedDualAdder(PolyCircuit xs, PolyCircuit bs);

    /**
     * Represent 2^xs.
     * @param xs The circuit of the exponent.
     * @return 2^xs.
     */
    PolyCircuit buildPowerOfTwo(PolyCircuit xs);

    // Shifts:
    // We use two shifters:
    // One Unary one, which expects a unary input. This one is also capable of filtering, by the assumption that log2(0) = -infty -> xs << log2(0) = 0
    // One Barrel filter, capable of shifting by an arbitrary amount of bits, represented in binary.
    // The Barrel filter is not capable of filtering. If this is desired, a special flag is to be used.
    // Furthermore some invariants hold:
    // buildShiftRightUnary(buldPowerOfTwo(shiftBy), xs) = buildShiftRightBinary(shiftBy, xs)
    // buildShiftRightUnary(shiftBy, xs) = buildTimesCircuit(shiftBy, xs) iff. shiftBy is unary (but the former produces a better suited circuit for DPLL search)
    //   in fact, when coding we only need to replace the pluses by bitwise ors. This is a lot cheaper in DPLL terms, as plusses involve bad XOrs

    /**
     * Represent xs << log2(shiftBy), asserting that shiftBy has exactly one digit set, or none (we regard xs << log(0) = xs << -infty = 0)
     * If shiftBy does not fulfil this assertion, the output is undefined.
     *
     */
    PolyCircuit buildShiftRightUnary(PolyCircuit shiftBy, PolyCircuit xs);

    /**
     * Represent xs << shiftBy
     * Done by barrell shifting in a good implementation.
     *
     */
    PolyCircuit buildShiftRightBinary(PolyCircuit shiftBy, PolyCircuit xs);



}
