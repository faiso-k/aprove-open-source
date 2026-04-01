package aprove.verification.dpframework.Orders.Utility.KBO;

import java.math.*;
import java.util.*;

/**
 *  This class represents a linear diophantine homogenous inequality
 *    a_1*x_1+...+a_n*x_n >= 0
 *  including a solver for minimal non-trivial solutions of the inequality.
 *  @author  Achim Luecking, Rene Thiemann
 *  @version $Id$
 */

public final class HomogenousInequality {

    private final static BigInteger ZERO = BigInteger.ZERO;
    private final static BigInteger ONE = BigInteger.ONE;

    // List for coefficiants (a_1,..,a_n) of this inequality
    private final List<BigInteger> coeff;
    private final int n; // the nr of coefficients

    // zero vector, needed for internal constructions
    private final List<BigInteger> zeroVector;

    // sets
    private final Set<Integer> n_lower;
    private final Set<Integer> n_equal;
    private final Set<Integer> n_greater;

    // solution
    private final List<List<BigInteger>> solution;

    // solved?
    private boolean solved;

    /**
     * Constructor.
     * @param coeff the coefficiant vector of the inequality
     */
    private HomogenousInequality(List<BigInteger> coeff) {
        this.coeff = coeff;
        this.n = this.coeff.size();
        this.zeroVector = new ArrayList<BigInteger>(this.n);
        for (int i=1; i<=this.coeff.size(); i++){
            this.zeroVector.add(HomogenousInequality.ZERO);
        }
        this.n_lower = new LinkedHashSet<Integer>();
        this.n_equal = new LinkedHashSet<Integer>();
        this.n_greater = new LinkedHashSet<Integer>();
        this.solution = new ArrayList<List<BigInteger>>();
        this.solved = false;
        int indexcount = 0;
        for (BigInteger element : this.coeff) {
            int comp = element.compareTo(HomogenousInequality.ZERO);
            if (comp < 0) {
                this.n_lower.add(indexcount);
            } else if (comp == 0){
                this.n_equal.add(indexcount);
            } else {
                this.n_greater.add(indexcount);
            }
            indexcount++;
        }
    }

    /**
     * Constructor.
     * @param coeff the coefficiant vector of the inequality
     */
    private HomogenousInequality(BigInteger[] coeff) {
        this.n = coeff.length;
        this.coeff = new ArrayList<BigInteger>(this.n);
        for (int i=0; i<this.n; i++){
            this.coeff.add(coeff[i]);
        }
        this.solved = false;
        this.solution = new ArrayList<List<BigInteger>>();
        this.zeroVector = new ArrayList<BigInteger>(this.n);
        for (int i=0; i<this.n; i++){
            this.zeroVector.add(HomogenousInequality.ZERO);
        }
        this.n_lower = new LinkedHashSet<Integer>();
        this.n_equal = new LinkedHashSet<Integer>();
        this.n_greater = new LinkedHashSet<Integer>();
        int indexcount = 0;
        for (BigInteger element : this.coeff) {
            int compare = element.compareTo(HomogenousInequality.ZERO);
            if (compare == -1) {
                this.n_lower.add(indexcount);
            } else if (compare == 0){
                this.n_equal.add(indexcount);
            } else {
                this.n_greater.add(indexcount);
            }
            indexcount++;
        }
    }

    /**
     * Returns an instance of a ineqality.
     * @param coeff the coefficiant vector of the inequality
     */
    public static HomogenousInequality create(List<BigInteger> coeff){
        return new HomogenousInequality(coeff);
    }

    /**
     * Returns an instance of a ineqality.
     * @param coeff array of coefficiants of the inequality
     */
    public static HomogenousInequality create(BigInteger[] coeff){
        return new HomogenousInequality(coeff);
    }

    private void build_e_equal(){
        for (Integer element : this.n_equal) {
            List<BigInteger> neu = new ArrayList<BigInteger>(this.zeroVector);
            neu.set(element.intValue(), HomogenousInequality.ONE);
            this.solution.add(neu);
        }
    }

    private void build_e_greater(){
        for (Integer element : this.n_greater) {
            List<BigInteger> neu = new ArrayList<BigInteger>(this.zeroVector);
            neu.set(element.intValue(), HomogenousInequality.ONE);
            this.solution.add(neu);
        }
    }

    private void build_e_combined(){
        for (Integer low : this.n_lower) {
            for (Integer great : this.n_greater) {
                List<BigInteger> neu = new ArrayList<BigInteger>(this.zeroVector);
                neu.set(low.intValue(), this.coeff.get(great.intValue()));
                BigInteger value = this.coeff.get(low.intValue());
                neu.set(great.intValue(), value.negate()); // negativer coeff !!!!! FIXEN !!!!! RT: ???
                this.solution.add(neu);
            }
        }
    }

    /**
     * Solves the inequality and returns a minimal solution different
     * from the trivial solution 0.
     * @return the minimal solution of the inequality, empty List if there exists only the trivial solution.
     */
    public void solve(){
        if (!this.solved) {
            this.build_e_equal();
            this.build_e_greater();
            this.build_e_combined();
            this.solved = true;
        }
    }

    private BigInteger calculateLeft(List<BigInteger> sol){
        BigInteger left = HomogenousInequality.ZERO;
        for (int i=0; i<sol.size(); i++){
            BigInteger x = sol.get(i);
            BigInteger y = this.coeff.get(i);
            left = left.add(x.multiply(y));
        }
        return left;
    }

    /**
     * Returns ths kappa matrix of the coefficiant vector.
     * @return the kappa matrix
     */
    public IntMatrix getKappaMatrix(){
        if (!this.solved) {
            this.solve();
        }
        return new IntMatrix(this.solution, this.n);
    }

    /**
     * Proves whether a given solution vector is a solution of this inequality.
     * @param sol a possible solution vector
     * @return true, if sol is a solution
     */
    public boolean isSolution(List<BigInteger> sol){
        BigInteger left=this.calculateLeft(sol);
        return left.compareTo(HomogenousInequality.ZERO) > 0;
    }

    public boolean isEqualitySolution(List<BigInteger> sol){
        BigInteger left = this.calculateLeft(sol);
        return left.equals(HomogenousInequality.ZERO);
    }

    /**
     * Returns the coefficients of the inequality.
     * @return the coefficients
     */
    public List<BigInteger> getCoefficients(){
        return this.coeff;
    }

    /**
     * Returns the size of the inequality (number of coefficiants).
     * @return the number of coefficiants
     */
    public int size(){
        return this.coeff.size();
    }

    /**
     * Returns a string representation of the inequality.
     * @return the string representation
     */
    @Override
    public String toString() {
        int varcount = 0;
        StringBuffer temp = new StringBuffer("\n");
        boolean first = true;
        for (BigInteger i : this.coeff) {
            varcount ++;
            if (!i.equals(HomogenousInequality.ZERO)) {
                if (first) {
                    first = false;
                } else {
                    temp.append(" + ");
                }
                temp.append(i+"*x"+varcount);
            }
        }
        temp.append(" >= 0 ");
        return temp.toString();
    }

    /**
     * Returns, whether another object o equals this inequality.
     */
    @Override
    public boolean equals(Object o){
        HomogenousInequality ie = (HomogenousInequality) o;
        return this.coeff.equals(ie.coeff);
    }

    /**
     * Returns the hash code of this inequality.
     */
    @Override
    public int hashCode() {
        return this.coeff.hashCode();
    }

}
