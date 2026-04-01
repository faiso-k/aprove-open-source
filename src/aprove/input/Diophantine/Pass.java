package aprove.input.Diophantine;

import java.util.*;

import aprove.input.Generated.diophantine.analysis.*;
import aprove.input.Generated.diophantine.node.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;

/**
 *
 * @author Patrick Kabasci
 * @version $Id$
 */
public class Pass extends DepthFirstAdapter {

    private enum Relation {
        GT,
        GTE,
        LT,
        LTE,
        EQ
    }


    private Stack stack;
    private List<SimplePolyConstraint> resList;


    @Override
    public void inStart(Start node)
    {
        this.defaultIn(node);
        this.stack = new Stack();
    }


    @Override
    public void defaultIn(@SuppressWarnings("unused") Node node)
    {
        // Do nothing
    }

    @Override
    public void defaultOut(@SuppressWarnings("unused") Node node)
    {
        // Do nothing
    }

    @Override
    public void caseStart(Start node)
    {
        this.inStart(node);
        node.getPDiophantines().apply(this);
        node.getEOF().apply(this);
        this.outStart(node);
    }

    @Override
    public void inADiophantines(ADiophantines node)
    {
        this.defaultIn(node);
    }

    @Override
    public void outADiophantines(ADiophantines node)
    {
        this.defaultOut(node);
    }

    @Override
    public void caseADiophantines(ADiophantines node)
    {
        this.inADiophantines(node);
        if(node.getDiophantine() != null)
        {
            node.getDiophantine().apply(this);
        }
        if(node.getConstraints() != null)
        {
            node.getConstraints().apply(this);
        }
        this.outADiophantines(node);
    }

    @Override
    public void inAConstraintsConstraints(AConstraintsConstraints node)
    {
        this.defaultIn(node);
    }

    @Override
    public void outAConstraintsConstraints(AConstraintsConstraints node)
    {
        this.defaultOut(node);
    }

    @Override
    public void caseAConstraintsConstraints(AConstraintsConstraints node)
    {
        this.inAConstraintsConstraints(node);
        if(node.getSemicolon() != null)
        {
            node.getSemicolon().apply(this);
        }
        if(node.getDiophantine() != null) {
            node.getDiophantine().apply(this);
        }
        if(node.getConstraints() != null)
        {
            node.getConstraints().apply(this);
        }
        this.outAConstraintsConstraints(node);
    }

    @Override
    public void inAEpsilonConstraints(AEpsilonConstraints node)
    {
        this.defaultIn(node);
    }

    @Override
    public void outAEpsilonConstraints(AEpsilonConstraints node)
    {
        this.defaultOut(node);
    }

    @Override
    public void caseAEpsilonConstraints(AEpsilonConstraints node)
    {
        this.inAEpsilonConstraints(node);
        this.outAEpsilonConstraints(node);
    }

    @Override
    public void inADiophantine(ADiophantine node)
    {
        this.defaultIn(node);
    }

    @Override
    public void outADiophantine(ADiophantine node)
    {
        SimplePolynomial right = ((SimplePolynomial) this.stack.pop());
        Relation relation = (Relation) this.stack.pop();
        SimplePolynomial left = ((SimplePolynomial) this.stack.pop());
        SimplePolyConstraint spc;

        switch (relation) {
        case EQ:
            spc = new SimplePolyConstraint(left.minus(right), ConstraintType.EQ);
            break;
        case GTE:
            spc = new SimplePolyConstraint(left.minus(right), ConstraintType.GE);
            break;
        case LTE:
            spc = new SimplePolyConstraint(right.minus(left), ConstraintType.GE);
            break;
        case GT:
            spc = new SimplePolyConstraint(left.minus(right), ConstraintType.GT);
            break;
        case LT:
        default:
            spc = new SimplePolyConstraint(right.minus(left), ConstraintType.GT);
            break;
        }
        this.stack.push (spc);

    }

    @Override
    public void caseADiophantine(ADiophantine node)
    {
        this.inADiophantine(node);
        if(node.getPolynomial() != null)
        {
            node.getPolynomial().apply(this);
        }
        if(node.getRelpoly() != null)
        {
            node.getRelpoly().apply(this);
        }
        this.outADiophantine(node);
    }

    @Override
    public void inARelpoly(ARelpoly node)
    {
        this.defaultIn(node);
    }

    @Override
    public void outARelpoly(ARelpoly node)
    {
        this.defaultOut(node);
    }

    @Override
    public void caseARelpoly(ARelpoly node)
    {
        this.inARelpoly(node);
        if(node.getRelation() != null)
        {
            node.getRelation().apply(this);
        }
        if(node.getPolynomial() != null)
        {
            node.getPolynomial().apply(this);
        }
        this.outARelpoly(node);
    }

    @Override
    public void inAGtRelation(AGtRelation node)
    {
        this.defaultIn(node);
    }

    @Override
    public void outAGtRelation(AGtRelation node)
    {
        this.stack.push(Relation.GT);
    }

    @Override
    public void caseAGtRelation(AGtRelation node)
    {
        this.inAGtRelation(node);
        if(node.getGt() != null)
        {
            node.getGt().apply(this);
        }
        this.outAGtRelation(node);
    }

    @Override
    public void inAEqRelation(AEqRelation node)
    {
        this.defaultIn(node);
    }

    @Override
    public void outAEqRelation(AEqRelation node)
    {
        this.stack.push(Relation.EQ);
    }

    @Override
    public void caseAEqRelation(AEqRelation node)
    {
        this.inAEqRelation(node);
        if(node.getEq() != null)
        {
            node.getEq().apply(this);
        }
        this.outAEqRelation(node);
    }

    @Override
    public void inALtRelation(ALtRelation node)
    {
        this.defaultIn(node);
    }

    @Override
    public void outALtRelation(ALtRelation node)
    {
        this.stack.push(Relation.LT);
    }

    @Override
    public void caseALtRelation(ALtRelation node)
    {
        this.inALtRelation(node);
        if(node.getLt() != null)
        {
            node.getLt().apply(this);
        }
        this.outALtRelation(node);
    }

    @Override
    public void inAGteRelation(AGteRelation node)
    {
        this.defaultIn(node);
    }

    @Override
    public void outAGteRelation(AGteRelation node)
    {
        this.stack.push(Relation.GTE);
    }

    @Override
    public void caseAGteRelation(AGteRelation node)
    {
        this.inAGteRelation(node);
        if(node.getGte() != null)
        {
            node.getGte().apply(this);
        }
        this.outAGteRelation(node);
    }

    @Override
    public void inALteRelation(ALteRelation node)
    {
        this.defaultIn(node);
    }

    @Override
    public void outALteRelation(ALteRelation node)
    {
        this.stack.push(Relation.LTE);
    }

    @Override
    public void caseALteRelation(ALteRelation node)
    {
        this.inALteRelation(node);
        if(node.getLte() != null)
        {
            node.getLte().apply(this);
        }
        this.outALteRelation(node);
    }

    @Override
    public void inAPolynomial(APolynomial node)
    {
        this.defaultIn(node);
    }


    @Override
    public void caseAPolynomial(APolynomial node)
    {
        this.inAPolynomial(node);
        if(node.getAddend() != null)
        {
            node.getAddend().apply(this);
        }
        if(node.getSum() != null)
        {
            node.getSum().apply(this);
        }
        this.outAPolynomial(node);
    }

    @Override
    public void inAAddend(AAddend node)
    {
        this.defaultIn(node);
    }


    @Override
    public void caseAAddend(AAddend node)
    {
        this.inAAddend(node);
        if(node.getFactor() != null)
        {
            node.getFactor().apply(this);
        }
        if(node.getProduct() != null)
        {
            node.getProduct().apply(this);
        }
        this.outAAddend(node);
    }

    @Override
    public void inAPosfactorFactor(APosfactorFactor node)
    {
        this.defaultIn(node);
    }

    @Override
    public void caseAPosfactorFactor(APosfactorFactor node)
    {
        this.inAPosfactorFactor(node);

        if(node.getBase() != null)
        {
            node.getBase().apply(this);
        }
        if(node.getPowerof() != null)
        {
            node.getPowerof().apply(this);
        }
        this.outAPosfactorFactor(node);
    }

    @Override
    public void inANegfactorFactor(ANegfactorFactor node)
    {
        this.defaultIn(node);
    }

    @Override
    public void caseANegfactorFactor(ANegfactorFactor node)
    {
        this.inANegfactorFactor(node);

        if(node.getMinus() != null)
        {
            node.getMinus().apply(this);
        }
        if(node.getFactor() != null)
        {
            node.getFactor().apply(this);
        }
        this.outANegfactorFactor(node);
    }


    @Override
    public void inABracketsBase(ABracketsBase node)
    {
        this.defaultIn(node);
    }



    @Override
    public void outABracketsBase(ABracketsBase node)
    {
        this.defaultOut(node);
    }

    @Override
    public void caseABracketsBase(ABracketsBase node)
    {
        this.inABracketsBase(node);
        if(node.getOpen() != null)
        {
            node.getOpen().apply(this);
        }
        if(node.getPolynomial() != null)
        {
            node.getPolynomial().apply(this);
        }
        if(node.getClose() != null)
        {
            node.getClose().apply(this);
        }
        this.outABracketsBase(node);
    }

    @Override
    public void inAIntegerBase(AIntegerBase node)
    {
        this.defaultIn(node);
    }

    @Override
    public void caseAIntegerBase(AIntegerBase node)
    {
        this.inAIntegerBase(node);
        if(node.getInt() != null)
        {
            node.getInt().apply(this);
        }
        this.outAIntegerBase(node);
    }

    @Override
    public void inAVariableBase(AVariableBase node)
    {
        this.defaultIn(node);
    }


    @Override
    public void caseAVariableBase(AVariableBase node)
    {
        this.inAVariableBase(node);
        if(node.getVar() != null)
        {
            node.getVar().apply(this);
        }
        this.outAVariableBase(node);
    }

    @Override
    public void inASumSum(ASumSum node)
    {
        this.defaultIn(node);
    }


    @Override
    public void caseASumSum(ASumSum node)
    {
        this.inASumSum(node);
        if(node.getPlus() != null)
        {
            node.getPlus().apply(this);
        }
        if(node.getAddend() != null)
        {
            node.getAddend().apply(this);
        }
        if(node.getSum() != null)
        {
            node.getSum().apply(this);
        }
        this.outASumSum(node);
    }

    @Override
    public void inAEpsilonSum(AEpsilonSum node)
    {
        this.defaultIn(node);
    }

    @Override
    public void outAEpsilonSum(AEpsilonSum node)
    {
        this.defaultOut(node);
    }

    @Override
    public void caseAEpsilonSum(AEpsilonSum node)
    {
        this.inAEpsilonSum(node);
        this.outAEpsilonSum(node);
    }

    @Override
    public void inAProductProduct(AProductProduct node)
    {
        this.defaultIn(node);
    }


    @Override
    public void caseAProductProduct(AProductProduct node)
    {
        this.inAProductProduct(node);
        if(node.getTimes() != null)
        {
            node.getTimes().apply(this);
        }
        if(node.getFactor() != null)
        {
            node.getFactor().apply(this);
        }
        if(node.getProduct() != null)
        {
            node.getProduct().apply(this);
        }
        this.outAProductProduct(node);
    }

    @Override
    public void inAEpsilonProduct(AEpsilonProduct node)
    {
        this.defaultIn(node);
    }

    @Override
    public void outAEpsilonProduct(AEpsilonProduct node)
    {
        this.defaultOut(node);
    }

    @Override
    public void caseAEpsilonProduct(AEpsilonProduct node)
    {
        this.inAEpsilonProduct(node);
        this.outAEpsilonProduct(node);
    }

    @Override
    public void inAPowerPowerof(APowerPowerof node)
    {
        this.defaultIn(node);
    }


    @Override
    public void caseAPowerPowerof(APowerPowerof node)
    {
        this.inAPowerPowerof(node);
        if(node.getPower() != null)
        {
            node.getPower().apply(this);
        }
        if(node.getInt() != null)
        {
            node.getInt().apply(this);
        }
        this.outAPowerPowerof(node);
    }

    @Override
    public void inAEpsilonPowerof(AEpsilonPowerof node)
    {
        this.defaultIn(node);
    }

    @Override
    public void outAEpsilonPowerof(AEpsilonPowerof node)
    {
        this.defaultOut(node);
    }

    @Override
    public void caseAEpsilonPowerof(AEpsilonPowerof node)
    {
        this.inAEpsilonPowerof(node);
        this.outAEpsilonPowerof(node);
    }


    @Override
    public void outAAddend(AAddend node) {
        if (node.getProduct() instanceof AProductProduct) {
            SimplePolynomial factor = (SimplePolynomial) this.stack.pop();
            this.stack.push(((SimplePolynomial) this.stack.pop()).times(factor));
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
    public void outANegfactorFactor(ANegfactorFactor node) {
        if (node.getMinus() != null){
             this.stack.push( SimplePolynomial.ZERO.minus(((SimplePolynomial) this.stack.pop())));
        }
    }

    @Override
    public void outAPosfactorFactor(APosfactorFactor node) {
        if (node.getPowerof() instanceof APowerPowerof) {
            int exponent = ((Integer) this.stack.pop()).intValue();
            this.stack.push(((SimplePolynomial) this.stack.pop()).power(exponent));
        }
    }

    @Override
    public void outAIntegerBase(AIntegerBase node) {
        int number = Integer.valueOf(node.getInt().getText()).intValue();
        this.stack.push(SimplePolynomial.create(number));
    }

    @Override
    public void outAPolynomial(APolynomial node) {
        if (node.getSum() instanceof ASumSum) {
            SimplePolynomial addend = (SimplePolynomial) this.stack.pop();
            this.stack.push(((SimplePolynomial) this.stack.pop()).plus(addend));
        }
    }

    @Override
    public void outAPowerPowerof(APowerPowerof node) {
        this.stack.push(Integer.valueOf(node.getInt().getText()));
    }

    @Override
    public void outAProductProduct(AProductProduct node) {
        if (node.getProduct() instanceof AProductProduct) {
            SimplePolynomial factor = (SimplePolynomial) this.stack.pop();
            this.stack.push(((SimplePolynomial) this.stack.pop()).times(factor));
        }
    }

    @Override
    public void outASumSum(ASumSum node) {
        if (node.getSum() instanceof ASumSum) {
            SimplePolynomial addend = (SimplePolynomial) this.stack.pop();
            this.stack.push(((SimplePolynomial) this.stack.pop()).plus(addend));
        }
    }

    @Override
    public void outAVariableBase(AVariableBase node) {
        this.stack.push(SimplePolynomial.create(node.getVar().getText()));
    }

    @Override
    public void outStart(Start node) {
        this.resList = new ArrayList<SimplePolyConstraint> (this.stack.size());
        while (!this.stack.empty()) {
            this.resList.add((SimplePolyConstraint)this.stack.pop());
        }
    }


    public List<SimplePolyConstraint> getContraints () {
        return this.resList;
    }

}

