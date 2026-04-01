/**
 *
 * @author weidmann
 * @version $Id$
 */
package aprove.input.Programs.diologic;

import java.util.*;

import aprove.*;
import aprove.input.Generated.diologic.analysis.*;
import aprove.input.Generated.diologic.node.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;

/* OnePass is a tree walker class that tries to build a diophantine logic formula
 * out of the information gathered during abstract syntax tree traversal.
 */


public class OnePass extends  DepthFirstAdapter {

    private Stack stack; // to collect information during tree traversal
    private HashMap propVars; // to map propositional variables correctly
    private Formula<Diophantine> diofml; // to store the resulting formula, if any
    private Boolean inAPoly; // to remember whether we are in a polynomial

    private enum Relation {
        GT,
        GTE,
        LT,
        LTE,
        EQ
    }

    public OnePass() {
        this.stack = new Stack();
        this.propVars = new HashMap();
        this.diofml = null;
        this.inAPoly = false;
    }

    @Override
    public void inStart(Start node)
    {
        this.defaultOut(node);
    }

    @Override
    public void outStart(Start node) {
        Object o = this.stack.pop();
        // check whether we really got a formula
        if(o instanceof SimplePolynomial) {
            throw new ParseException("No formula, just a polynomial!");
        } else {
            this.diofml = (Formula<Diophantine>) o;
        }
    }

    /* When leaving such a node, get the last two formulae from the stack, create an
     * implication formula and put that back on the stack.
    */
    @Override
    public void outAImpformulaFormula(AImpformulaFormula node)
    {
        // check whether we really got two formulae
        Object r = this.stack.pop();
        Object l = this.stack.pop();

        Boolean rPoly = r instanceof SimplePolynomial;
        Boolean lPoly = l instanceof SimplePolynomial;

        if(rPoly || lPoly) {
            throw new ParseException(node.getImp(), "Implication is only allowed on formulae!");
        } else {
            FullSharingFactory<Diophantine> ff = new FullSharingFactory<Diophantine>();
            Formula<Diophantine> right = (Formula<Diophantine>) r;
            Formula<Diophantine> left = (Formula<Diophantine>) l;
            Formula<Diophantine> f = ff.buildImplication(left, right);
            this.stack.push(f);
        }
    }

    /* When leaving such a node, get the last two formulae from the stack, create an
     * equivalence formula and put that back on the stack.
    */
    @Override
    public void outAEqvformulaFormula(AEqvformulaFormula node)
    {
        // check whether we really got two formulae
        Object r = this.stack.pop();
        Object l = this.stack.pop();

        if((r instanceof SimplePolynomial)||(l instanceof SimplePolynomial)) {
            throw new ParseException(node.getEqv(), "Equivalence is only allowed on formulae!");
        } else {
            FullSharingFactory<Diophantine> ff = new FullSharingFactory<Diophantine>();
            Formula<Diophantine> right = (Formula<Diophantine>) r;
            Formula<Diophantine> left = (Formula<Diophantine>) l;
            Formula<Diophantine> f = ff.buildIff(left, right);
            this.stack.push(f);
        }
    }


    /* When leaving such a node, get the last two formulae from the stack and put
     * their exclusive disjunction back on the stack.
    */
    @Override
    public void outAXororformula(AXororformula node)
    {
        // check whether we really got two formulae
        Object r = this.stack.pop();
        Object l = this.stack.pop();

        if((r instanceof SimplePolynomial)||(l instanceof SimplePolynomial)) {
            throw new ParseException(node.getXor(),"XOR is only allowed on formulae!");
        } else {
            FullSharingFactory<Diophantine> ff = new FullSharingFactory<Diophantine>();
            Formula<Diophantine> right = (Formula<Diophantine>) r;
            Formula<Diophantine> left = (Formula<Diophantine>) l;
            Formula<Diophantine> f = ff.buildXor(left, right);
            this.stack.push(f);
        }
    }

    /* When leaving such a node, get the last two formulae from the stack and put
     * their disjunction back on the stack.
    */
    @Override
    public void outAOrandformula(AOrandformula node)
    {
        // check whether we really got two formulae
        Object r = this.stack.pop();
        Object l = this.stack.pop();

        if((r instanceof SimplePolynomial)||(l instanceof SimplePolynomial)) {
            throw new ParseException(node.getOr(), "Disjunction is only allowed on formulae!");
        } else {
            FullSharingFactory<Diophantine> ff = new FullSharingFactory<Diophantine>();
            Formula<Diophantine> right = (Formula<Diophantine>) r;
            Formula<Diophantine> left = (Formula<Diophantine>) l;
            Formula<Diophantine> f = ff.buildOr(left, right);
            this.stack.push(f);
        }
    }

    /* When leaving such a node, get the last two formulae from the stack and put
     * their conjunction back on the stack.
    */
    @Override
    public void outAAndlitformula(AAndlitformula node)
    {
        // check whether we really got two formulae
        Object r = this.stack.pop();
        Object l = this.stack.pop();

        if((r instanceof SimplePolynomial)||(l instanceof SimplePolynomial)) {
            throw new ParseException(node.getAnd(), "Conjunction is only allowed on formulae!");
        } else {
            FullSharingFactory<Diophantine> ff = new FullSharingFactory<Diophantine>();
            Formula<Diophantine> right = (Formula<Diophantine>) r;
            Formula<Diophantine> left = (Formula<Diophantine>) l;
            Formula<Diophantine> f = ff.buildAnd(left, right);
            this.stack.push(f);
        }
    }


    /* When leaving such a node, get the formula from the stack and
     * put its negation back on the stack.
    */
    @Override
    public void outANegLitformula(ANegLitformula node)
    {
        // check whether we really got a formula
        Object o = this.stack.pop();
        if(o instanceof SimplePolynomial) {
            throw new ParseException(node.getNeg(), "Negation is only allowed on formulae!");
        } else {
            FullSharingFactory<Diophantine> ff = new FullSharingFactory<Diophantine>();
            Formula<Diophantine> fml = (Formula<Diophantine>) o;
            Formula<Diophantine> f = ff.buildNot(fml);
            this.stack.push(f);
        }
    }

    /* When leaving such a node, put the boolean constant true
     * on the stack.
    */
    @Override
    public void outATrueAtom(ATrueAtom node)
    {
        FullSharingFactory<Diophantine> ff = new FullSharingFactory<Diophantine>();
        Constant<Diophantine> c =  ff.buildConstant(true);
        this.stack.push(c);
    }

    /* When leaving such a node, put the boolean constant false
     * on the stack.
    */
    @Override
    public void outAFalseAtom(AFalseAtom node)
    {
        FullSharingFactory<Diophantine> ff = new FullSharingFactory<Diophantine>();
        Constant<Diophantine> c =  ff.buildConstant(false);
        this.stack.push(c);
    }

    /* When entering such a node, we know that only two polys may follow.
    */
    @Override
    public void inARelDiophantine(ARelDiophantine node)
    {
        // check whether we are not already in a poly
        if (!this.inAPoly) {
            // set this flag to remember that we now expect only polys
            // to follow and no formulae.
            this.inAPoly = true;
        }
        else { // we are already in a poly
            // so we throw an exception, because e.g. a < b < c is not allowed.
            // TODO integrate token!
            throw new ParseException("Nested atomic diophantine formulae are not allowed!");
        }
    }


    /* When leaving such a node, we should have two polynomials and a relation
     * on the stack.
    */
    @Override
    public void outARelDiophantine(ARelDiophantine node)
    {
        Object right = this.stack.pop();
        Relation rel = (Relation) this.stack.pop();
        Object left = this.stack.pop();
        // check whether we have two polynomials
        if ((right instanceof SimplePolynomial) && (left instanceof SimplePolynomial)) {
            // create an atomic diophantine formula
            FullSharingFactory<Diophantine> ff = new FullSharingFactory<Diophantine>();
            Diophantine dio = null;
            switch(rel) {
            case EQ:
                dio = Diophantine.create(((SimplePolynomial) left).minus((SimplePolynomial) right), ConstraintType.EQ);
                break;
            case GT:
                dio = Diophantine.create(((SimplePolynomial) left).minus((SimplePolynomial) right), ConstraintType.GT);
                break;
            case LT:
                dio = Diophantine.create(((SimplePolynomial) right).minus((SimplePolynomial) left), ConstraintType.GT);
                break;
            case GTE:
                dio = Diophantine.create(((SimplePolynomial) left).minus((SimplePolynomial) right), ConstraintType.GE);
                break;
            case LTE:
                dio = Diophantine.create(((SimplePolynomial) right).minus((SimplePolynomial) left), ConstraintType.GE);
                break;

            }
            TheoryAtom<Diophantine> thAtom = ff.buildTheoryAtom(dio);

            this.stack.push(thAtom);
            this.inAPoly = false; // remove the flag
        }
        else {
//          TODO integrate Token
            throw new ParseException("The relation " + rel.toString() + " is only allowed on polynomials!");
        }

    }

    /* When leaving such a node, there is nothing to do.
    */
    @Override
    public void outAPolyDiophantine(APolyDiophantine node)
    {
        this.defaultOut(node);
    }



    /* When leaving such a node, we put the sum of two polynomials, if any,
     * on the stack.
     */
    @Override
    public void outAPlusPmsumf(APlusPmsumf node)
    {
        Object right = this.stack.pop();
        Object left = this.stack.pop();

        if ((right instanceof SimplePolynomial) && (left instanceof SimplePolynomial)) {
            this.stack.push(((SimplePolynomial)left).plus((SimplePolynomial)right));
        }
        else {
            throw new ParseException(node.getPlus(), "Addition is only allowed for polynomials, not for formulae!");
        }
    }

    /* When leaving such a node, we put the difference of two polynomials, if any,
     * on the stack.
     */
    @Override
    public void outAMinusPmsumf(AMinusPmsumf node)
    {
        Object right = this.stack.pop();
        Object left = this.stack.pop();

        if ((right instanceof SimplePolynomial) && (left instanceof SimplePolynomial)) {
            this.stack.push(((SimplePolynomial)left).minus((SimplePolynomial)right));
        }
        else {
            throw new ParseException(node.getMinus(), "Subtraction is only allowed for polynomials, not for formulae!");
        }
    }

    /* When leaving such a node, we put the product of two polynomials, if any,
     * on the stack.
     */
    @Override
    public void outAFactorpmexpf(AFactorpmexpf node)
    {
        Object right = this.stack.pop();
        Object left = this.stack.pop();

        if ((right instanceof SimplePolynomial) && (left instanceof SimplePolynomial)) {
            this.stack.push(((SimplePolynomial)left).times((SimplePolynomial)right));
        }
        else {
            throw new ParseException(node.getTimes(), "Multiplication is only allowed for polynomials, not for formulae!");
        }
    }


    /* When leaving such a node, we have to take care of the sign.
     */
    @Override
    public void outAMinusPmexpf(AMinusPmexpf node)
    {
        // check whether the top of the stack is a polynomial
        Object o = this.stack.pop();
        if(o instanceof SimplePolynomial)
        {
            this.stack.push( SimplePolynomial.ZERO.minus(((SimplePolynomial) o)));
        }
        else {
            throw new ParseException(node.getMinus(), "Signs are only allowed for polynomials, not for formulae!");
        }
    }

    /* When leaving such a node, we have to take care of the sign.
     */
    @Override
    public void outAPlusPmexpf(APlusPmexpf node)
    {
        Object o = this.stack.pop();
        // check whether the top of the stack is not a polynomial
        if (!(o instanceof SimplePolynomial)) {
            throw new ParseException(node.getPlus(), "Signs are only allowed for polynomials, not for formulae!");
        }
        else {
            // We do not have to handle a plus as sign, so we simply ignore it
            this.stack.push(o);
        }

    }

    /* When leaving such a node, we have nothing to do.
     */
    @Override
    public void outANonePmexpf(ANonePmexpf node)
    {
        this.defaultOut(node);
    }

     /* When leaving such a node, we create a power, if any,
      * and put that on the stack.
      */
     @Override
     public void outAExpf(AExpf node)
     {
         if (node.getExppotf()!= null) { // if there is an exponent
             int exponent = ((Integer) this.stack.pop()).intValue();
             // check whether the top of the stack is really a polynomial
             Object pOrf = this.stack.pop();
             if (pOrf instanceof SimplePolynomial) {
                 this.stack.push(((SimplePolynomial) pOrf).power(exponent));
             } else {
                 // TODO integrate token
                 throw new ParseException("Power operator is not allowed!");
             }
         } // else: no Power

     }

     /* When leaving such a node, we put the exponent on the stack.
      */
      @Override
      public void outAExppotf(AExppotf node)
      {
          this.stack.push(Integer.valueOf(node.getInt().getText()));
      }

    /* When leaving such a node, either create a propositional variable
     * or a numerical variable, depending on the flag.
    */
    @Override
    public void outAVariableBase(AVariableBase node)
    {
        String varname = node.getVar().getText();

        if(this.inAPoly) {
            this.stack.push(SimplePolynomial.create(varname));
        }
        else {
            // check whether a propositional variable with this name already exists
            Variable<Diophantine> v = (Variable<Diophantine>) this.propVars.get(varname);
            if (v == null){ // create a new variable and update the hashmap
                FullSharingFactory<Diophantine> ff = new FullSharingFactory<Diophantine>();
                v = ff.buildVariable();
                this.propVars.put(varname, v);
            }
            if(Globals.DEBUG_WEIDMANN) {
                System.err.println("Varname: " + varname + " ~> " + v.toString());
            }
            this.stack.push(v);
        }
    }

    /* When leaving such a node, we have an integer value,
     * so we create a simple polynomial out of it and put that on the stack.
    */
    @Override
    public void outAIntegerBase(AIntegerBase node)
    {
        int number = Integer.valueOf(node.getInt().getText()).intValue();
        this.stack.push(SimplePolynomial.create(number));
    }

    /* When leaving such a node, we either have a polynomial or a formula.
    */
    @Override
    public void outAPolynomialBase(APolynomialBase node)
    {
        this.defaultOut(node);
    }


    @Override
    public void outAGtRelation(AGtRelation node)
    {
        this.stack.push(Relation.GT);
    }

    @Override
    public void outAEqRelation(AEqRelation node)
    {
        this.stack.push(Relation.EQ);
    }

    @Override
    public void outALtRelation(ALtRelation node)
    {
        this.stack.push(Relation.LT);
    }

    @Override
    public void outAGteRelation(AGteRelation node)
    {
        this.stack.push(Relation.GTE);
    }

    @Override
    public void outALteRelation(ALteRelation node)
    {
        this.stack.push(Relation.LTE);
    }

    /* Returns the diophantine formula, if any.
     */
    public Formula<Diophantine> getFormula() {
        return this.diofml;
    }

}
