package aprove.verification.oldframework.Verifier;

import aprove.prooftree.Export.Utility.*;

/**
 * @author Andreas Capellmann
 * @version $Id$
 */
public abstract class AbstractConstraint implements Exportable, HTML_Able,
        LaTeX_Able, java.io.Serializable  {

  private final static int MIN = 0;

  public final static int EQ = AbstractConstraint.MIN;
  public final static int GE = AbstractConstraint.EQ + 1;
  public final static int GR = AbstractConstraint.GE + 1;
  public final static int DK = AbstractConstraint.GR + 1;

  private final static int MAX = AbstractConstraint.DK;

  protected Object left;
  protected Object right;

  protected int type;

  /** only for serialize
   */
  public AbstractConstraint(){
  }

  protected AbstractConstraint(Object someLeftSide, Object someRightSide, int someType) {
    this.left = someLeftSide;
    this.right = someRightSide;
    this.setType(someType);
  }

  @Override
public boolean equals(Object o) {
    if (o == null || !(o instanceof AbstractConstraint)) {
        return false;
    }

    AbstractConstraint other = (AbstractConstraint) o;

    return this.type == other.type && this.left.equals(other.left) && this.right.equals(other.right);
  }

  public int getType() {
    return this.type;
  }

  @Override
public int hashCode() {
    return this.left.hashCode() + this.right.hashCode();
  }

  public void setType(int someType) {
    if (someType < AbstractConstraint.MIN || someType > AbstractConstraint.MAX) {
        throw new IllegalArgumentException(
            "Method setType(int someType) in class AbstractConstraint requires some value between "
              + AbstractConstraint.MIN
              + " and "
              + AbstractConstraint.MAX
              + "for argument someType.");
    }

    this.type = someType;
  }

  @Override
public String export(Export_Util eu) {
      StringBuffer buffer = new StringBuffer();

      buffer.append(eu.export(this.left));

      switch (this.type) {
          case EQ :
              buffer.append(" = ");
              break;
          case GE :
              buffer.append(eu.geSign());
              break;
          case GR :
              buffer.append(eu.gtSign());
              break;
          default :
              buffer.append(" don't know ");
      }

      buffer.append(eu.export(this.right));

      return buffer.toString();
  }

  @Override
public String toHTML() {
      return this.export(new HTML_Util());
  }

  @Override
public String toLaTeX() {
      return this.export(new LaTeX_Util());
  }

  @Override
  public String toString() {
      return this.export(new PLAIN_Util());
  }

}
