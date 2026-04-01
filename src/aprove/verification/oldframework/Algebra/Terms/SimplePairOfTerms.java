package aprove.verification.oldframework.Algebra.Terms;

/**
 * @author Andreas Capellmann
 * @version $Id$
 */
public class SimplePairOfTerms implements PairOfTerms {

  private AlgebraTerm left;
  private AlgebraTerm right;

  public SimplePairOfTerms(AlgebraTerm someLeftSide, AlgebraTerm someRightSide) {
    this.left = someLeftSide;
    this.right = someRightSide;
  }

  @Override
public boolean equals(Object o) {
    PairOfTerms p = (PairOfTerms) o;
    return this.left.equals(p.getLeft()) && this.right.equals(p.getRight());
  }

  @Override
public AlgebraTerm getLeft() {
    return this.left;
  }

  @Override
public AlgebraTerm getRight() {
    return this.right;
  }

  public void setLeft(AlgebraTerm left) {
    this.left = left;
  }

  public void setRight(AlgebraTerm right) {
    this.right = right;
  }

  @Override
public int hashCode() {
    return (this.left.toString() + this.right.toString()).hashCode();
  }

  @Override
public String toString(){
    return ("(" + this.left.toString() + "|" + this.right.toString()+")");
  }

}
