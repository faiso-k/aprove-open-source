package aprove.verification.oldframework.Unification.Utility;

import java.util.*;

/**
 *  Set of IntVectors with additional functionality.
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public class IntVectors extends HashSet<IntVector> {

    /** Extracts the IntVectors that have value 0. */
    public IntVectors getSolutions() {
    IntVectors res = new IntVectors();

    Iterator i = this.iterator();
    while(i.hasNext()) {
        IntVector vec = (IntVector)i.next();
        if(vec.getValue()==0) {
        res.add(vec);
        }
    }

        return res;
    }

    /** Extracts the IntVectors that have valVec 0. */
    public IntVectors getSolutionsVec() {
    IntVectors res = new IntVectors();

    Iterator i = this.iterator();
    while(i.hasNext()) {
        IntVector vec = (IntVector)i.next();
        if(vec.getVecValue().isTrivial()) {
        res.add(vec);
        }
    }

        return res;
    }

    /** Extracts the IntVectors that are not bigger than any member of cand. */
    public IntVectors notBiggerThanAny(Collection<IntVector> cand) {
    IntVectors res = new IntVectors();

    Iterator i = this.iterator();
    while(i.hasNext()) {
        IntVector vec = (IntVector)i.next();
        Iterator j = cand.iterator();
        boolean isBigger = false;
        while(j.hasNext() && !isBigger) {
        IntVector cmp = (IntVector)j.next();
        isBigger = vec.isBigger(cmp);
        }
        if(!isBigger) {
        res.add(vec);
        }
    }

    return res;
    }

    /** Increases components according the the restrictions that the values of
     * the IntVector and the unit vector have a different sign.
     */
    public IntVectors expandAll(IntVectors neg, IntVectors pos) {
    IntVectors res = new IntVectors();

    Iterator i = this.iterator();
    while(i.hasNext()) {
        IntVector vec = (IntVector)i.next();
        Iterator j;
        if(vec.getValue() > 0) {
        j = neg.iterator();
        }
        else {
        j = pos.iterator();
        }
        while(j.hasNext()) {
        IntVector unit = (IntVector)j.next();
        res.add(vec.add(unit));
        }
    }

    return res;
    }

    /** Like expandAll, but the last component is not increased if it's 1.
     * @see #expandAll(IntVectors, IntVectors)
     */
    public IntVectors expandAllWithFrozenLast(IntVectors neg, IntVectors pos) {
    IntVectors res = new IntVectors();

    Iterator i = this.iterator();
    while(i.hasNext()) {
        IntVector vec = (IntVector)i.next();
        Iterator j;
        if(vec.getValue() > 0) {
        j = neg.iterator();
        }
        else {
        j = pos.iterator();
        }
        while(j.hasNext()) {
        IntVector unit = (IntVector)j.next();
        if(unit.getLast()!=1 || vec.getLast()!=1) {
            res.add(vec.add(unit));
        }
        }
    }

    return res;
    }

    /** Increases components according the the restrictions that the product of the valVecs of
     * the IntVector and the unit vector is negative.
     */
    public IntVectors expandAllVec(IntVectors units) {
    IntVectors res = new IntVectors();

    Iterator i = this.iterator();
    while(i.hasNext()) {
        IntVector vec = (IntVector)i.next();
        Iterator j = units.iterator();
        while(j.hasNext()) {
        IntVector unit = (IntVector)j.next();
        if(vec.getVecValue().mult(unit.getVecValue()) < 0) {
            res.add(vec.add(unit));
        }
        }
    }

    return res;
    }

    /** Increases components according the the restrictions that the product of the valVecs of
     * the IntVector and the unit vector is negative and the constraint components are at most 1.
     */
    public IntVectors expandAllVec(IntVectors units, BoolVector con) {
    IntVectors res = new IntVectors();

    Iterator i = this.iterator();
    while(i.hasNext()) {
        IntVector vec = (IntVector)i.next();
        Iterator j = units.iterator();
        while(j.hasNext()) {
        IntVector unit = (IntVector)j.next();
        int count = -1;
        for(int k=0; k<unit.size(); k++) {
            if(unit.get(k)!=0) {
            count = k;
            }
        }
        if((!con.get(count) || vec.get(count) < 1) && vec.getVecValue().mult(unit.getVecValue()) < 0) {
            res.add(vec.add(unit));
        }
        }
    }

    return res;
    }

}
