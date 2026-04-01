package aprove.verification.complexity.LowerBounds.Util;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;

public class OuterMostPositionComparator implements Comparator<Position> {

    private InnerMostPositionComparator innermostCmp = new InnerMostPositionComparator();

    @Override
    public int compare(final Position o1, final Position o2) {
        return -this.innermostCmp.compare(o1, o2);
    }

}
