package aprove.verification.oldframework.Unification.Utility;


/**
 * @author Stephan Falke
 * @version $Id$
 */
public class PairOfACnCTerms {

  private ACnCTerm left;
  private ACnCTerm right;

  private PairOfACnCTerms(ACnCTerm someLeftSide, ACnCTerm someRightSide) {
    this.left = someLeftSide;
    this.right = someRightSide;
  }

  public static PairOfACnCTerms create(ACnCTerm someLeftSide, ACnCTerm someRightSide) {
    return new PairOfACnCTerms(someLeftSide, someRightSide);
  }

  public MultisetOfACnCTerms getVars() {
    MultisetOfACnCTerms res = this.left.getVars();
    res = res.union(this.right.getVars());
    return res;
  }

  @Override
public boolean equals(Object o) {
    PairOfACnCTerms p = (PairOfACnCTerms) o;
    return this.left.equals(p.getLeft()) && this.right.equals(p.getRight()) || this.left.equals(p.getRight()) && this.right.equals(p.getLeft());
  }

  public ACnCTerm getLeft() {
    return this.left;
  }

  public ACnCTerm getRight() {
    return this.right;
  }

  public boolean isTrivial() {
    return this.left.equals(this.right);
  }

  @Override
public int hashCode() {
    return this.toString().hashCode() + this.toSwapString().hashCode();
  }

  @Override
public String toString() {
    StringBuffer res = new StringBuffer(this.left.toString());
    res.append("==");
    res.append(this.right.toString());
    return res.toString();
  }

  public String toSwapString() {
    StringBuffer res = new StringBuffer(this.right.toString());
    res.append("==");
    res.append(this.left.toString());
    return res.toString();
  }


  public PairOfACTerms toPairOfACTerms() {
    return PairOfACTerms.create(this.left.toACTerm(), this.right.toACTerm());
  }
}
