package aprove.verification.oldframework.Algebra.Terms.Visitors;

import java.util.*;

import aprove.verification.oldframework.Algebra.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;

/**
 * Calculates the active afs conditions for a polynomial interpretation of some term.
 *
 * @author Andreas Capellmann
 * @version $Id$
 */
public class GetConditionsVisitor implements CoarseGrainedTermVisitor {

  private final Map<SyntacticFunctionSymbol,Set<Polynomial>> conditions;
  private final Interpretation interpretation;
  private Polynomial prefix;
  private final Program program;
  private final Set<SyntacticFunctionSymbol> visitedSymbols;

  private GetConditionsVisitor(Program program, Interpretation interpretation, Map<SyntacticFunctionSymbol,Set<Polynomial>> conditions) {
    this.conditions = conditions;
    this.interpretation = interpretation;
    this.program = program;
    this.prefix = Polynomial.ONE;
    this.visitedSymbols = new HashSet<SyntacticFunctionSymbol>();
  }

  /**
   * Entry point for calculation of conditions.
   *
   * @param term the term to perform on
   * @param program some program
   * @param interpretation polynomial interpretation of terms over the program's signature
   * @param conditions map with initial conditions that may have been collected on another term
   *
   * @return map with conditions (function symbols mapped to conditions)
   */
  public static Map apply(
    AlgebraTerm term,
    Program program,
    Interpretation interpretation,
    Map<SyntacticFunctionSymbol,Set<Polynomial>> conditions) {
    GetConditionsVisitor visitor = new GetConditionsVisitor(program, interpretation, conditions);
    term.apply(visitor);

    return visitor.conditions;
  }

  @Override
public Object caseFunctionApp(AlgebraFunctionApplication f) {
    if (f instanceof DefFunctionApp) {
      // investigate useable rules
      if (!(this.visitedSymbols.contains(f.getFunctionSymbol()))) {
        this.visitedSymbols.add(f.getFunctionSymbol());

        // store condition so far
        this.storeCondition(f.getFunctionSymbol(), this.prefix);

        Set rules = this.program.getRules(f.getFunctionSymbol());
        for (Iterator iter = rules.iterator(); iter.hasNext();) {
          Rule rule = (Rule) iter.next();
          // right sides only!! rule.getLeft().apply(this);
          rule.getRight().apply(this);
        }

        this.visitedSymbols.remove(f.getFunctionSymbol());
      }
    }

    // backup prefix
    Polynomial prefix = this.prefix;

    int i = 0;
    for (Iterator iter = f.getArguments().iterator(); iter.hasNext(); ++i) {
      // get fresh prefix
      this.prefix = prefix;
      Polynomial[] conditions =
        (Polynomial[]) this.interpretation.coefficients.get(f.getFunctionSymbol());

      if (conditions[i] != null) {
        this.prefix = this.prefix.times(conditions[i]);
    }

      ((AlgebraTerm) iter.next()).apply(this);
    }

    // restore prefix
    this.prefix = prefix;

    return null;
  }

  @Override
public Object caseVariable(AlgebraVariable v) {
    return null;
  }

  private void storeCondition(SyntacticFunctionSymbol f, Polynomial condition) {
    Set<Polynomial> conditions = this.conditions.get(f);
    if (conditions == null) {
      conditions = new LinkedHashSet<Polynomial>();
      conditions.add(condition);
      this.conditions.put(f, conditions);
    } else {
        conditions.add(condition);
    }
  }

}
