package aprove.verification.oldframework.Unification.Utility;

import java.util.*;

/**
 *  Solver for a homogeneous linear diophantine equation.
 *
 *  @author Stephan Falke
 *  @version $Id$
 */

public class DioHom {

    private IntVector a;
    private int n;
    private IntVectors positiveUnits;
    private IntVectors negativeUnits;

    private DioHom(IntVector a) {
    this.a = a;
    this.n = this.a.size();
    }

    /** Creates a new DioHom a * x = 0 */
    public static DioHom create(IntVector a) {
    return new DioHom(a);
    }

    /** Returns the set of minimal solutions of a * x = 0,
     * returns a set containing only the zero vector if there is
     * only the trivial solution.
     */
    public List<IntVector> solutions() {
    this.positiveUnits = new IntVectors();
    this.negativeUnits = new IntVectors();
    IntVectors B = new IntVectors();
    IntVectors P = new IntVectors();

    /* generate units */
    for(int i=0; i<this.n; i++) {
        int[] vec = new int[this.n];
        for(int j=0; j<this.n; j++) {
        vec[j] = 0;
        }
        vec[i] = 1;
        int value = this.a.get(i);
        IntVector unit = IntVector.create(vec, value);
        if(value == 0) {
        /* solution */
        B.add(unit);
        }
        else {
        if(value > 0) {
            this.positiveUnits.add(unit);
            }
            else {
            this.negativeUnits.add(unit);
        }
        /* to be expanded */
        P.add(unit.deepcopy());
        }
    }

    while(!P.isEmpty()) {
        /* still some expansions to be done */

        /* extract solutions from P */
        B.addAll(P.getSolutions());

        /* remove solutions from P */
        P.removeAll(B);

        /* remove vectors that are bigger than some solution */
        IntVectors Q = P.notBiggerThanAny(B);

        /* increase components */
        P = Q.expandAll(this.negativeUnits, this.positiveUnits);
    }

    if(B.isEmpty()) {
        /* add trivial solution */
        int[] vec = new int[this.n];
        for(int j=0; j<this.n; j++) {
        vec[j] = 0;
        }
        IntVector trivial = IntVector.create(vec, 0);
        B.add(trivial);
    }

    return new Vector<IntVector>(B);
    }

}
