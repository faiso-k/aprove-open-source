package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Syntax.*;

/**
 * @author Andreas Capellmann, thiemann
 * @version $Id$
 */
public class GeneratePolynomialVisitor extends CoarseGrainedDepthFirstTermVisitor {

  private final Interpretation interpretation;
  private final LinkedList<Polynomial> polynomials; // used as a stack
  private final Set<String> variables;

  private static final String POLY_VAR_ENDING = "v";
  // needed for assuring that term-poly variables and functionSymbol-poly vars
  // do not collide; anything but [0-9]* is allowed

  private GeneratePolynomialVisitor(Interpretation interpretation, Set<String> variables) {
    super();
    this.interpretation = interpretation;
    this.polynomials = new LinkedList<Polynomial>();
    this.variables = variables;
  }

  public static Polynomial apply(AlgebraTerm term, Interpretation interpretation) {
    return GeneratePolynomialVisitor.apply(term, interpretation, new LinkedHashSet<String>());
  }

  public static Polynomial apply(AlgebraTerm term, Interpretation interpretation, Set<String> variables) {
    GeneratePolynomialVisitor visitor = new GeneratePolynomialVisitor(interpretation, variables);
    term.apply(visitor);

    return visitor.polynomials.poll();
  }

  @Override
public void outFunctionApp(AlgebraFunctionApplication f) {
    SyntacticFunctionSymbol function = (SyntacticFunctionSymbol) f.getSymbol();
    int arity = function.getArity();

    Polynomial polynomial = this.interpretation.get(function);
    for (int i = arity - 1; i >= 0; --i) {
        polynomial =
            polynomial.substituteVariable(
              Interpretation.VARIABLE_PREFIX + (i + 1),
              this.polynomials.poll());
    }

    this.polynomials.addFirst(polynomial);
  }

  @Override
public void outVariable(AlgebraVariable v) {
    // the ending is needed to avoid collisions between variables
    // of terms and those of functions symbols, which could cause
    // nasty problems for the way the (single!) substitution of
    // outFunctionApp() is implemented.
    String varName = v.getName() + GeneratePolynomialVisitor.POLY_VAR_ENDING;
    this.variables.add(varName);
    this.polynomials.addFirst(Polynomial.createVariable(varName));
  }
}
