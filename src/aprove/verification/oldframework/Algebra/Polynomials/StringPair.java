package aprove.verification.oldframework.Algebra.Polynomials;

import immutables.*;

/**
 * An ordered pair of String.
 *
 * @author Andreas Capellmann
 * @version $Id$
 */
public class StringPair implements Comparable<StringPair>, Immutable {

  public final String one;
  public final String two;

  public StringPair(String one, String two) {
    if (one.compareTo(two) <= 0) {
      this.one = one;
      this.two = two;
    } else {
      this.one = two;
      this.two = one;
    }
  }

  @Override
public int compareTo(StringPair pair) {
    int c = this.one.compareTo(pair.one);
    if (c != 0) {
        return c;
    }

    return this.two.compareTo(pair.two);
  }

  @Override
public boolean equals(Object o) {
    if ((o == null) || (!(o instanceof StringPair))) {
        return false;
    }

    StringPair pair = (StringPair) o;

    return ((this.one.equals(pair.one)) && (this.two.equals(pair.two)));
  }

  @Override
public int hashCode() {
    return this.one.hashCode() + this.two.hashCode();
  }

  @Override
public String toString() {
    StringBuffer b = new StringBuffer("(");
    b.append(this.one);
    b.append(",");
    b.append(this.two);
    b.append(")");

    return b.toString();
  }

}
