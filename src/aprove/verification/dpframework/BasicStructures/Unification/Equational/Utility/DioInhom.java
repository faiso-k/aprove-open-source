/*
 * Created on Feb 24, 2006
 */
package aprove.verification.dpframework.BasicStructures.Unification.Equational.Utility;

import java.util.*;

/**
 * Solver for an ihomogeneous linear diophantine equation.
 *
 * @author Stephan Falke
 * @version $Id$
 */

public class DioInhom {

    private IntVector a;

    private IntVector newA;

    private int b;

    private int newB;

    private int n;

    private int newN;

    private IntVectors positiveUnits;

    private IntVectors negativeUnits;

    private DioInhom(IntVector a, int b) {
        this.a = a;
        this.b = b;
        this.n = this.a.size();
    }

    /**
     * Creates a new DioInhom a * x = b.
     */
    public static DioInhom create(IntVector a, int b) {
        return new DioInhom(a, b);
    }

    /* solutions to homogeneous newA * x = 0 as in DioHom */
    private List<IntVector> solutions() {
        this.newB = -this.b;

        int[] newVec = new int[this.n + 1];

        for (int i = 0; i < this.n; i++) {
            newVec[i] = this.a.get(i);
        }
        newVec[this.n] = this.newB;

        this.newA = IntVector.create(newVec, 0);
        this.newN = this.n + 1;

        this.positiveUnits = new IntVectors();
        this.negativeUnits = new IntVectors();
        IntVectors B = new IntVectors();
        IntVectors P = new IntVectors();

        for (int i = 0; i < this.newN; i++) {
            int[] vec = new int[this.newN];
            for (int j = 0; j < this.newN; j++) {
                vec[j] = 0;
            }
            vec[i] = 1;
            int value = this.newA.get(i);
            IntVector unit = IntVector.create(vec, value);
            if (value == 0) {
                B.add(unit);
            } else {
                if (value > 0) {
                    this.positiveUnits.add(unit);
                } else {
                    this.negativeUnits.add(unit);
                }
                P.add(unit.deepcopy());
            }
        }

        while (!P.isEmpty()) {
            B.addAll(P.getSolutions());
            P.removeAll(B);
            IntVectors Q = P.notBiggerThanAny(B);
            /* last component is not allowed to exceed 1 */
            P = Q.expandAllWithFrozenLast(this.negativeUnits,
                    this.positiveUnits);
        }

        return new ArrayList<IntVector>(B);
    }

    /** Returns the set of minimal special solutions of a * x = b */
    public List<IntVector> specialSolutions() {
        List<IntVector> res = new ArrayList<IntVector>();

        for (IntVector vec : this.solutions()) {
            if (vec.get(this.n) == 1) {
                /* it's a special solutions */
                int[] newVec = new int[this.n];
                for (int j = 0; j < this.n; j++) {
                    newVec[j] = vec.get(j);
                }
                res.add(IntVector.create(newVec, 0));
            }
        }

        return res;
    }

}
