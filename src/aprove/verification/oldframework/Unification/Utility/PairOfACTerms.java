package aprove.verification.oldframework.Unification.Utility;

import java.util.*;

import aprove.verification.oldframework.Syntax.*;

/**
 * @author Stephan Falke
 * @version $Id$
 */
public class PairOfACTerms {

  private ACTerm left;
  private ACTerm right;

  private PairOfACTerms(ACTerm someLeftSide, ACTerm someRightSide) {
    this.left = someLeftSide;
    this.right = someRightSide;
  }

  public static PairOfACTerms create(ACTerm someLeftSide, ACTerm someRightSide) {
    return new PairOfACTerms(someLeftSide, someRightSide);
  }

  public MultisetOfACTerms getVars() {
    MultisetOfACTerms res = this.left.getVars();
    res = res.union(this.right.getVars());
    return res;
  }

  @Override
public boolean equals(Object o) {
    PairOfACTerms p = (PairOfACTerms) o;
    return this.left.equals(p.getLeft()) && this.right.equals(p.getRight()) || this.left.equals(p.getRight()) && this.right.equals(p.getLeft());
  }

  public ACTerm getLeft() {
    return this.left;
  }

  public ACTerm getRight() {
    return this.right;
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

  public PairOfACnCTerms toPairOfACnCTerms(Set<SyntacticFunctionSymbol> cs) {
    return PairOfACnCTerms.create(this.left.toACnCTerm(cs), this.right.toACnCTerm(cs));
  }
}
