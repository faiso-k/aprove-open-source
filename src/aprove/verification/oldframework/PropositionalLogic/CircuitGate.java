package aprove.verification.oldframework.PropositionalLogic;

import java.io.*;
import java.util.*;

import aprove.*;

/**
 * Encodes a boolean circuit gate in a quasi Extended Dimacs format
 * style via a gate type, an output, zero or more inputs, and a
 * (possibly unused) parameter.
 *
 * Note that you can combine boolean circuit gates b1 and b2
 * e.g. by making the output of b1 equal to one of the inputs
 * of b2. Inputs which are not outputs of other circuits will be
 * treated as variables. Note further that the Extended Dimacs
 * format requires that the output of the resulting circuit
 * has the highest input/output number that occurs in the
 * entire circuit. For more details, see the corresponding
 * paper by Bacchus and Walsh.
 *
 * @author Carsten Fuhs
 * @version $Id$
 */
public class CircuitGate implements Serializable {

    // values taken from the Extended Dimacs format specifications
    public static final int FALSE = 1;
    public static final int TRUE = 2;
    public static final int NOT = 3;
    public static final int AND = 4;
    public static final int OR = 6;
    public static final int XOR = 8;
    public static final int IFF = 11;
    public static final int IFTHENELSE = 12;
    public static final int ATLEAST = 13;
    public static final int ATMOST = 14;
    public static final int COUNT = 15;

    public final int gateType; // one of the above constants
    public final int output; // output IO number of the gate
    public final int[] inputs; // input IO numbers of the gate
    public final int param; // parameter of the gate; only makes sense
                            // for certain gate types

    public static final int[] NO_INPUTS = new int[0];
    // do not create empty arrays all the time, use this one
    // if you have no inputs

    public static final CircuitGate[] NO_GATES = new CircuitGate[0];
    // ditto for empty lists of CircuitGates

    private CircuitGate(int gateType, int output, int[] inputs, int param) {
        this.gateType = gateType;
        this.output = output;
        this.inputs = inputs;
        this.param = param;
    }

    /**
     * @param gateType
     * @param output
     * @param inputs will be incorporated in this, so do not mess with it
     *  after calling create!
     * @return a new CircuitGate with the parameters as attributes
     */
    public static CircuitGate create(int gateType, int output, int[] inputs) {
        return new CircuitGate(gateType, output, inputs, -1);
    }

    /**
     * @param gateType
     * @param output
     * @param inputs will be incorporated in this, so do not mess with it
     *  after calling create!
     * @param param relevant for certain types of gates only (e.g.,
     *  cardinality gates); use {@see create(int,int,int[])} if you do not
     *  need a parameter
     * @return a new CircuitGate with the parameters as attributes
     */
    public static CircuitGate create(int gateType, int output, int[] inputs,
            int param) {
        if (Globals.useAssertions) {
            // change this assertion once you define own gates with parameters
            assert param >= 0 &&
                (gateType == CircuitGate.ATLEAST ||
                gateType == CircuitGate.ATMOST ||
                gateType == CircuitGate.COUNT);
        }
        return new CircuitGate(gateType, output, inputs, param);
    }

    /**
     * Converts a list of CircuitGates and the maximum IO number to
     * Extended Dimacs format.
     *
     * @param gates
     * @param maxIO
     * @return the corresponding Extended Dimacs format problem
     */
    public static String toExtendedDimacs(List<CircuitGate> gates, int maxIO) {
        // TODO check initial size, might have high performance implications
        // due to implicit arraycopy operations
        StringBuilder sb = new StringBuilder(20*gates.size());
        sb.append("p noncnf ");
        sb.append(maxIO);
        sb.append('\n');
        for (CircuitGate gate : gates) {
            sb.append(gate.toExtendedDimacsLine());
        }
        return sb.toString();
    }

    /**
     * @return this as an Extended Dimacs problem line
     */
    public String toExtendedDimacsLine() {
        // TODO maybe vary init capacity of result
        StringBuilder result = new StringBuilder(4*this.inputs.length);
        final int type = this.gateType;
        result.append(type);
        switch (type) {
        // only cardinality gates (ATLEAST, ATMOST, COUNT) have a parameter,
        // same treatment for these types is intended here
        case ATLEAST:
        case ATMOST:
        case COUNT:
            result.append(" 1 ");
            result.append(this.param);
            result.append(' ');
            break;
        default:
            result.append(" -1 ");
        }
        result.append(this.output);
        result.append(' ');
        for (int i = 0; i < this.inputs.length; ++i) {
            result.append(this.inputs[i]);
            result.append(' ');
        }
        result.append("0\n");
        return result.toString();
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder(4*(this.inputs.length + 4));
        sb.append(this.output);
        sb.append(" = ");
        switch (this.gateType) {
        case FALSE:
            sb.append('F');
            break;
        case TRUE:
            sb.append('T');
            break;
        case NOT:
            sb.append("NOT");
            break;
        case AND:
            sb.append("AND");
            break;
        case OR:
            sb.append("OR");
            break;
        case XOR:
            sb.append("XOR");
            break;
        case IFF:
            sb.append("IFF");
            break;
        case IFTHENELSE:
            sb.append("ITE");
            break;
        case ATLEAST:
            sb.append("ATLEAST_");
            sb.append(this.param);
            break;
        case ATMOST:
            sb.append("ATMOST_");
            sb.append(this.param);
            break;
        case COUNT:
            sb.append("COUNT_");
            sb.append(this.param);
            break;
        default:
            if (Globals.useAssertions) {
                assert false; // gate type (still) unknown! fix it.
            }
            sb.append("### UNKNOWN GATE TYPE ");
            sb.append(this.gateType);
            sb.append(" ###");
        }
        sb.append(' ');
        sb.append(Arrays.toString(this.inputs));
        return sb.toString();
    }
}
