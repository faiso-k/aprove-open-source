package aprove.verification.dpframework.Orders.Utility.KBO;

import java.math.*;
import java.util.*;

/**
 * This class represents a linear diophantine homogenous inequality system
 *   a_11*x_11+...+a_n1*x_n1 >= 0
 *   ...
 *   a_1m*x_1m+...+a_nm*x_nm >= 0
 * including a solver for getting minimal non-trivial solutions
 * of the system. The solver works with an incremental construction
 * of solutions.
 * @author  Achim Luecking, R. Thiemann
 * @version $Id$
 */
public final class HomogenousInequalitySystem {

    private static final BigInteger ZERO = BigInteger.ZERO;
    private static final BigInteger ONE = BigInteger.ONE;

    // vector of column vectors, used for intermediate results
    private IntMatrix last_S;
    private IntMatrix last_P;

    // number of unknowns of the system
    private final int vars;

    // set of homogenous inequalities of the system
    private final Set<HomogenousInequality> ineqs;

    /**
     * Constructor.
     * @param ineq the set of inequalities, the system should be build of, must be non-empty!
     * Moreover, the set must not be modified afterwards from the outside, but it will be
     * modified by this class.
     */
    public HomogenousInequalitySystem(Set<HomogenousInequality> ineq) {
        this.ineqs = ineq;
        this.vars = this.ineqs.iterator().next().size();
        List<List<BigInteger>> lastS = new ArrayList<List<BigInteger>>(this.vars);
        List<List<BigInteger>> lastP = new ArrayList<List<BigInteger>>(this.vars);

        List<BigInteger> nullVector = new ArrayList<BigInteger>(this.vars);
        for (int i=0; i<this.vars; i++){
            nullVector.add(HomogenousInequalitySystem.ZERO);
        }
        for (int i=0; i<this.vars; i++){
            List<BigInteger> neu = new ArrayList<BigInteger>(nullVector);
            neu.set(i, HomogenousInequalitySystem.ONE);
            lastP.add(neu);
            lastS.add(neu);
        }

        this.last_S = new IntMatrix(lastS, this.vars);
        this.last_P = new IntMatrix(lastP, this.vars);

        this.solve();
    }

    /**
     * copy constructor
     * @param v
     * @param ieq
     * @param P
     * @param S
     */
    private HomogenousInequalitySystem(HomogenousInequalitySystem other) {
        this.vars = other.vars;
        this.last_S = other.last_S;
        this.last_P = other.last_P;
        this.ineqs = new LinkedHashSet<HomogenousInequality>(other.ineqs);
    }


    /**
     * Computes a solution of the actual system.
     */
    private void solve() {
        for (HomogenousInequality ineq : this.ineqs) {
            HomogenousInequality newIneq = HomogenousInequality.create(this.last_S.multiplyRow(ineq.getCoefficients()));
            this.last_P = newIneq.getKappaMatrix();
            this.last_S = this.last_S.multiply(this.last_P);
        }
    }

    /**
     * Adds a new homogenous inequality to the system. While adding
     * the solution of the new resulting system is computed.
     * @param ineq the inequality
     */
    public void add(HomogenousInequality ineq) {
        if (this.ineqs.add(ineq)) {
            HomogenousInequality newIneq = HomogenousInequality.create(this.last_S.multiplyRow(ineq.getCoefficients()));
            this.last_P = newIneq.getKappaMatrix();
            this.last_S = this.last_S.multiply(this.last_P);
        }
    }

    /**
     * Returns whether this system has a non trivial solution or not.
     * @return true, if it has a non-trivial solution, false otherwise
     */
    public boolean hasSolution(){
        return !this.last_S.toVectors().isEmpty();
    }

    /**
     * Returns the degenerate subsystem of this system. This means all
     * inequalities of this system, which determine the equality with 0
     * for every solution.
     * @return the degenerate subsystem
     */
    public Set<HomogenousInequality> getDegenerateSubSystem(){
        LinkedHashSet<HomogenousInequality> sub = new LinkedHashSet<HomogenousInequality>();
        List<List<BigInteger>> sols = this.last_S.toVectors();
        if (sols.isEmpty()) {
            return sub;
        }
        for (HomogenousInequality hi : this.ineqs) {
            boolean add = true;
            for (List<BigInteger> posSol : sols) {
                if (!hi.isEqualitySolution(posSol)) {
                    add = false;
                    break;
                }
            }
            if (add) {
                sub.add(hi);
            }
        }
        return sub;
    }

    /**
     * Returns a minimal solution vector.
     * @return a minimal solution vector
     */
    public List<BigInteger> getMinimalSolution(){
        if (this.hasSolution()){
            List<BigInteger> solution = new ArrayList<BigInteger>();
            for (int i=0; i<this.vars; i++){
                BigInteger added = HomogenousInequalitySystem.ZERO;
                Set<List<BigInteger>> sols = this.last_S.toSet();
                for (List<BigInteger> element : sols) {
                    BigInteger x = element.get(i);
                    added = added.add(x);
                }
                solution.add(added);
            }
            return solution;
        } else {
            return new ArrayList<BigInteger>();
        }
    }

    public HomogenousInequalitySystem deepcopy(){
        return new HomogenousInequalitySystem(this);
    }


    /**
     * Returns a string representing the object.
     * @return the string representation
     */
    @Override
    public String toString() {
        StringBuffer temp = new StringBuffer("{");
        for (HomogenousInequality ineq : this.ineqs) {
            temp.append(ineq+"\n");
        }
        return temp.toString()+"}";
    }

}
