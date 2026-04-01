package aprove.verification.oldframework.Haskell.Visitors;

import java.util.*;

import aprove.verification.oldframework.Haskell.Modules.*;

 /**
 * @author Stephan Swiderski
 * @version $Id$
 * compares two entities by thier names
 * if they have the same names by thier hashCodes
 * its only for sorting entities by thier names
 */

public class EntityComparator implements Comparator<HaskellEntity>{
    @Override
    public int compare(HaskellEntity a,HaskellEntity b) {
        if (a==b) {
            return 0;
        }
    int i=(a.getName().compareTo(b.getName()));
    if (i == 0) {
        i = a.hashCode() - b.hashCode();
        }
    return i;
    }

    public boolean equals(HaskellEntity a,HaskellEntity b){
        return a == b;
    }


}
