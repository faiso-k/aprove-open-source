package aprove.verification.dpframework.IDPProblem.itpf;

import java.util.*;

import aprove.verification.dpframework.IDPProblem.Processors.algorithms.cap.*;

/**
 * Docu-guess (fuhs):
 * Information token to state what rules have already been
 * applied to an Itpf.
 *
 * @author mpluecke
 */
public class ItpfMark<T extends Object> {

    protected static final List<ItpfMark<? extends Object>> values = new ArrayList<ItpfMark<? extends Object>>();

    public static final ItpfMark<Set<IECap>> ItpfCap = new ItpfMark<Set<IECap>>(true);
    public static final ItpfMark<Object> ItpfUnify = new ItpfMark<Object>(false);
    public static final ItpfMark<Object> RootConstr = new ItpfMark<Object>(true);
    public static final ItpfMark<Object> ItpfStepDetect = new ItpfMark<Object>(true);
    public static final ItpfMark<Object> ItpfBoolOp = new ItpfMark<Object>(true);
    public static final ItpfMark<Object> ItpfVarReduct = new ItpfMark<Object>(true);
    public static final ItpfMark<Integer> ItpfRewriting = new ItpfMark<Integer>(true);
    public static final ItpfMark<Object> CCRelOp = new ItpfMark<Object>(true);

    // extract relations for MCNPs
    public static final ItpfMark<Object> MCNPRelExtract = new ItpfMark<Object>(true);


    protected static Map<ItpfMark<? extends Object>, Set<ItpfMark<? extends Object>>> compatibility;
    static {
        ItpfMark.compatibility = new LinkedHashMap<ItpfMark<? extends Object>, Set<ItpfMark<? extends Object>>>();
        for (ItpfMark<? extends Object> mark : ItpfMark.values) {
            ItpfMark.compatibility.put(mark, new LinkedHashSet<ItpfMark<? extends Object>>());
        }

        // compatibility map

    }

    /**
     * @param mark1 remains active,
     * @param mark2 if mark2 is set
     * @param symmetric true for symmetric cases
     */
    protected static void setCompatible(ItpfMark<? extends Object> mark1, ItpfMark<? extends Object> mark2, boolean symmetric) {
        ItpfMark.compatibility.get(mark1).add(mark2);
        if (symmetric) {
            ItpfMark.compatibility.get(mark2).add(mark1);
        }
    }

    public static boolean isCompatible(ItpfMark<? extends Object> mark1, ItpfMark<? extends Object> mark2) {
        return ItpfMark.compatibility.get(mark1).contains(mark2);
    }

    private boolean leafMark;

    ItpfMark(boolean leafMark) {
        ItpfMark.values.add(this);
        this.leafMark = leafMark;
    }

    public boolean isLeafMark() {
        return this.leafMark;
    }

}
