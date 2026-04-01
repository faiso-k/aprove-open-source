package aprove.input.Polynomials;

import java.util.*;

import aprove.input.Generated.polynomial.analysis.*;
import aprove.input.Generated.polynomial.node.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 * @author Andreas Capellmann
 * @version $Id$
 */
public class Pass extends DepthFirstAdapter {

  public Polynomial polynomial;
  private Stack stack;

  @Override
public void inStart(Start node) {
    this.stack = new Stack();
  }

  @Override
public void outAAddend(AAddend node) {
    if (node.getProduct() instanceof AProductProduct) {
      Polynomial factor = (Polynomial) this.stack.pop();
      this.stack.push(((Polynomial) this.stack.pop()).times(factor));
    }
  }

  //  public void outABracketsBase(ABracketsBase node) {
  //  }

  //  public void outAEpsilonPowerof(AEpsilonPowerof node) {
  //  }

  //  public void outAEpsilonProduct(AEpsilonProduct node) {
  //  }

  //  public void outAEpsilonSum(AEpsilonSum node) {
  //  }

  @Override
public void outAFactor(AFactor node) {
    if (node.getPowerof() instanceof APowerPowerof) {
      int exponent = ((Integer) this.stack.pop()).intValue();
      this.stack.push(((Polynomial) this.stack.pop()).power(exponent));
    }
  }

  @Override
public void outAIntegerBase(AIntegerBase node) {
    int number = Integer.valueOf(node.getInt().getText()).intValue();
    if (node.getMinus() != null) {
        number *= -1;
    }
    this.stack.push(Polynomial.createConstant(number));
  }

  @Override
public void outAPolynomial(APolynomial node) {
    if (node.getSum() instanceof ASumSum) {
      Polynomial addend = (Polynomial) this.stack.pop();
      this.stack.push(((Polynomial) this.stack.pop()).plus(addend));
    }
  }

  @Override
public void outAPowerPowerof(APowerPowerof node) {
    this.stack.push(Integer.valueOf(node.getInt().getText()));
  }

  @Override
public void outAProductProduct(AProductProduct node) {
    if (node.getProduct() instanceof AProductProduct) {
      Polynomial factor = (Polynomial) this.stack.pop();
      this.stack.push(((Polynomial) this.stack.pop()).times(factor));
    }
  }

  @Override
public void outASumSum(ASumSum node) {
    if (node.getSum() instanceof ASumSum) {
      Polynomial addend = (Polynomial) this.stack.pop();
      this.stack.push(((Polynomial) this.stack.pop()).plus(addend));
    }
  }

  @Override
public void outAVariableBase(AVariableBase node) {
    this.stack.push(Polynomial.createVariable(node.getVar().getText()));
  }

  @Override
public void outStart(Start node) {
    this.polynomial = (Polynomial) this.stack.pop();
  }

}