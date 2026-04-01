package aprove.verification.complexity.LowerBounds.Util;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;

/**
 * Orders the positions of a term from innermost to outermost. Can be used for innermost rewriting.
 */
public class InnerMostPositionComparator implements Comparator<Position> {

    @Override
    public int compare(Position o1, Position o2) {
        Iterator<Integer> it1 = o1.iterator();
        Iterator<Integer> it2 = o2.iterator();
        while (it1.hasNext() && it2.hasNext()) {
            int i1 = it1.next();
            int i2 = it2.next();
            if (i1 < i2) {
                return -1;
            }
            if (i2 < i1) {
                return 1;
            }
        }
        if (it1.hasNext()) {
            return -1;
        }
        if (it2.hasNext()) {
            return 1;
        }
        return 0;
    }

}
