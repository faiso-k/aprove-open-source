package aprove.verification.oldframework.Unification.Utility;

import java.util.*;

/**
 *  Solver for a system of homogeneous linear diophantine equations.
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public class DioHomSystem {

    private List<IntVector> a;
    private int m;   // no rows
    private int n;   // no columns
    private IntVectors units;
    private BoolVector con;

    private DioHomSystem(List<IntVector> a, BoolVector con) {
    this.a = a;
    this.con = con;
    this.n = this.a.size();
    if(this.n==0) {
        this.m = 0;
    }
    else {
        this.m = ((IntVector)this.a.get(0)).size();
    }
    }

    /** Creates a new DioHomSystem a * x = 0 */
    public static DioHomSystem create(List<IntVector> a) {
    return new DioHomSystem(a, null);
    }

    /** Creates a new DioHomSystem a * x = 0 */
    public static DioHomSystem create(List<IntVector> a, BoolVector con) {
    return new DioHomSystem(a, con);
    }

    /** Returns the set of minimal solutions of a * x = 0,
     * returns an empty set if there is only the trivial solution.
     */
    public List<IntVector> solutions() {
    this.units = new IntVectors();
    IntVectors B = new IntVectors();
    IntVectors P = new IntVectors();

    /* generate units */
    for(int i=0; i<this.m; i++) {
        int[] vec = new int[this.m];
        int[] val = new int[this.n];
        for(int j=0; j<this.n; j++) {
        vec[j] = 0;
        }
        vec[i] = 1;
        for(int j=0; j<this.n; j++) {
        val[j] = ((IntVector)this.a.get(j)).get(i);
        }
        IntVector value = IntVector.create(val, 0);
        IntVector unit = IntVector.create(vec, value);
        if(value.isTrivial()) {
        /* solution */
        B.add(unit);
        }
        else {
        this.units.add(unit);
        /* to be expanded */
        P.add(unit.deepcopy());
        }
    }

    while(!P.isEmpty()) {
        /* still some expansions to be done */

        /* extract solutions from P */
        B.addAll(P.getSolutionsVec());

        /* remove solutions from P */
        P.removeAll(B);

        /* remove vectors that are bigger than some solution */
        IntVectors Q = P.notBiggerThanAny(B);

        /* increase components */
        if(this.con==null) {
            P = Q.expandAllVec(this.units);
        }
        else {
            P = Q.expandAllVec(this.units, this.con);
        }

    }

    return new Vector<IntVector>(B);
    }

}
