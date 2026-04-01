package aprove.verification.idpframework.Core.IDPGraph;

import java.util.*;
import java.util.Map.Entry;

import aprove.verification.idpframework.Core.Itpf.*;

/**
 * @author MP
 */
public abstract class EdgeComparator {

    public static final Comparator<Map.Entry<IEdge, Itpf>> EDGE_ENTRY_COMPARATOR = new Comparator<Entry<IEdge,Itpf>>() {
        @Override
        public int compare(final Map.Entry<IEdge, Itpf> arg0,
            final Map.Entry<IEdge, Itpf> arg1) {
            final IEdge e0 = arg0.getKey();
            final IEdge e1 = arg1.getKey();
            return EdgeComparator.compareEdges(e0, e1);
        }
    };

    public static Comparator<IEdge> EDGE_COMPARATOR = new Comparator<IEdge>() {

        @Override
        public int compare(final IEdge e0, final IEdge e1) {
            return EdgeComparator.compareEdges(e0, e1);
        }

    };

    public static int compareEdges(final IEdge e0,
        final IEdge e1) {
        if (e0.type.ordinal() < e1.type.ordinal()) {
            return -1;
        } else if (e0.type.ordinal() > e1.type.ordinal()) {
            return 1;
        } else if (e0.from.id < e1.from.id) {
            return -1;
        } else if (e0.from.id > e1.from.id) {
            return 1;
        } else if (e0.to.id < e1.to.id) {
            return -1;
        } else if (e0.to.id > e1.to.id) {
            return 1;
        }
        return 0;
    }
}
