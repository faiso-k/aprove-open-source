package aprove.verification.oldframework.Verifier;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.theoremprover.TerminationVerifier.*;

/** Extension of the HashSet<Constraint> with a new
 *  constructor that takes rules and transforms them
 *  into strict constraints as well as a method
 *  for adding further sets of rules as constraints.
 *  This implementation also provides a method for
 *  getting the signature of this set's constraints.
 * @author Peter Schneider-Kamp, Carsten Pelikan
 * @version $Id$
 */

public class Constraints extends LinkedHashSet<Constraint> implements HTML_Able {

    private List<String> ASignature;
    private List<String> ACSignature;
    private List<String> CSignature;
    private Set<SyntacticFunctionSymbol> As;
    private Set<SyntacticFunctionSymbol> ACs;
    private Set<SyntacticFunctionSymbol> Cs;

    public Constraints(Collection<Constraint> someCollection) {
        super(someCollection);
    this.ASignature = new Vector<String>();
        this.ACSignature = new Vector<String>();
    this.CSignature = new Vector<String>();
    this.As = new LinkedHashSet<SyntacticFunctionSymbol>();
    this.ACs = new LinkedHashSet<SyntacticFunctionSymbol>();
    this.Cs = new LinkedHashSet<SyntacticFunctionSymbol>();
    }

    public Constraints() {
        super();
    this.ASignature = new Vector<String>();
    this.ACSignature = new Vector<String>();
    this.CSignature = new Vector<String>();
    this.As = new LinkedHashSet<SyntacticFunctionSymbol>();
    this.ACs = new LinkedHashSet<SyntacticFunctionSymbol>();
    this.Cs = new LinkedHashSet<SyntacticFunctionSymbol>();
    }

    /** Create a new hash set of constraints with a typed constraint
     *  for each rule in the given set.
     */
    public static Constraints createByRules(Collection<Rule> rules, int type) {

        Constraints newConstraints = new Constraints();

        newConstraints.ASignature = new Vector<String>();
        newConstraints.ACSignature = new Vector<String>();
        newConstraints.CSignature = new Vector<String>();
        newConstraints.As = new LinkedHashSet<SyntacticFunctionSymbol>();
        newConstraints.ACs = new LinkedHashSet<SyntacticFunctionSymbol>();
        newConstraints.Cs = new LinkedHashSet<SyntacticFunctionSymbol>();
        newConstraints.addRules(rules, type);

        return newConstraints;
    }

    public static Constraints createByNodes(Collection<Node<Rule>> nodes, int type) {

        Constraints newConstraints = new Constraints();

        newConstraints.ASignature = new Vector<String>();
        newConstraints.ACSignature = new Vector<String>();
        newConstraints.CSignature = new Vector<String>();
        newConstraints.As = new LinkedHashSet<SyntacticFunctionSymbol>();
        newConstraints.ACs = new LinkedHashSet<SyntacticFunctionSymbol>();
        newConstraints.Cs = new LinkedHashSet<SyntacticFunctionSymbol>();

        for (Node<Rule> node : nodes) {
            newConstraints.add(Constraint.create(node.getObject(), type));
        }

        return newConstraints;
    }

    /** Create a new hash set of constraints with a typed constraint
     *  for each equation in the given set.
     */
    public static Constraints createByTRSEquations(Collection<TRSEquation> equations, int type) {

        Constraints newConstraints = new Constraints();

        newConstraints.ASignature = new Vector<String>();
        newConstraints.ACSignature = new Vector<String>();
        newConstraints.CSignature = new Vector<String>();
        newConstraints.As = new LinkedHashSet<SyntacticFunctionSymbol>();
        newConstraints.ACs = new LinkedHashSet<SyntacticFunctionSymbol>();
        newConstraints.Cs = new LinkedHashSet<SyntacticFunctionSymbol>();
        newConstraints.addEquations(equations, type);

        return newConstraints;
    }

    /** Add a set of rules to this set of constraints.
     * @param type Type indicator.
     */
    public void addRules(Collection<Rule> rules, int type) {
        for (Iterator i = rules.iterator(); i.hasNext();) {
            this.add(Constraint.create((Rule)i.next(), type));
        }
    }

    /** Add a set of equations to this set of constraints.
     * @param type Type indicator.
     */
    public void addEquations(Collection<TRSEquation> equations, int type) {
        for (Iterator i = equations.iterator(); i.hasNext();) {
            TRSEquation eq = (TRSEquation)i.next();
            this.add(Constraint.create(eq.getOneSide(), eq.getOtherSide(), type));
        }
    }

    /** Add a set of dependency pairs to this set of constraints.
     */
    public void addDps(DependencyPairs dps, int type) {
        for (Iterator i = dps.iterator(); i.hasNext();) {
            Rule dp = (Rule)i.next();
            this.add(Constraint.create(dp.getLeft(), dp.getRight(), type));
        }
    }

    /** Get the signature for this set of constraints.
     * @return List of all the names of all function symbols.
     */
    public List<String> getSignature() {
        Set<SyntacticFunctionSymbol> sig = new LinkedHashSet<SyntacticFunctionSymbol>();
        for (Constraint c : this) {
            sig.addAll(c.getLeft().getFunctionSymbols());
            sig.addAll(c.getRight().getFunctionSymbols());
        }
        List<String> result = new Vector<String>();
        for (Symbol s : sig) {
            result.add(s.getName());
        }
        return result;
    }

    /** Returns the names of the A symbols for these constraints.
     */
    public List<String> getASignature() {
        return this.ASignature;
    }

    /** Set the A signature for these constraints.
     */
    public void setASignature(List<String> ASignature) {
        this.ASignature = ASignature;
    }

    /** Returns the names of the AC symbols for these constraints.
     */
    public List<String> getACSignature() {
        return this.ACSignature;
    }

    /** Set the AC signature for these constraints.
     */
    public void setACSignature(List<String> ACSignature) {
        this.ACSignature = ACSignature;
    }

    /** Returns the names of the C symbols for these constraints.
     */
    public List<String> getCSignature() {
        return this.CSignature;
    }

    /** Set the C signature for these constraints.
     */
    public void setCSignature(List<String> CSignature) {
        this.CSignature = CSignature;
    }

    /** Returns the A symbols for these constraints.
     */
    public Set<SyntacticFunctionSymbol> getASymbols() {
        return this.As;
    }

    /** Set the A symbols for these constraints.
     */
    public void setASymbols(Set<SyntacticFunctionSymbol> As) {
        this.As = As;
    }

    /** Returns the AC symbols for these constraints.
     */
    public Set<SyntacticFunctionSymbol> getACSymbols() {
        return this.ACs;
    }

    /** Set the AC symbols for these constraints.
     */
    public void setACSymbols(Set<SyntacticFunctionSymbol> ACs) {
        this.ACs = ACs;
    }

    /** Returns the C symbols for these constraints.
     */
    public Set<SyntacticFunctionSymbol> getCSymbols() {
        return this.Cs;
    }

    /** Set the C symbols for these constraints.
     */
    public void setCSymbols(Set<SyntacticFunctionSymbol> Cs) {
        this.Cs = Cs;
    }

    public void setEquationalSymbols(Program prog) {
        this.setACSymbols(prog.getACSymbols());
        this.setCSymbols(prog.getCSymbols());
        this.setASymbols(prog.getASymbols());
        this.setACSignature(prog.getACSignature());
        this.setCSignature(prog.getCSignature());
        this.setASignature(prog.getASignature());
    }

    public Set<SyntacticFunctionSymbol> getFunctionSymbols() {
        Set<SyntacticFunctionSymbol> defs = new LinkedHashSet<SyntacticFunctionSymbol>();
        for (Iterator i = this.iterator(); i.hasNext();) {
            Constraint c = (Constraint)i.next();
            defs.addAll(c.getLeft().getFunctionSymbols());
            defs.addAll(c.getRight().getFunctionSymbols());
        }
        return defs;
    }


    public Set<String> getVariableNames() {
      Set<String> variables = new HashSet<String>();
      for (Iterator iter = this.iterator(); iter.hasNext();) {
        Constraint c = (Constraint) iter.next();
        for (Iterator iterator = c.getLeft().getVars().iterator(); iterator.hasNext();) {
          AlgebraVariable var = (AlgebraVariable) iterator.next();
          variables.add(var.getName());
        }
        for (Iterator iterator = c.getRight().getVars().iterator(); iterator.hasNext();) {
          AlgebraVariable var = (AlgebraVariable) iterator.next();
          variables.add(var.getName());
        }
      }

      return variables;
    }

    public boolean checkVars() {
        Iterator i = this.iterator();
        while (i.hasNext()) {
            Constraint c = (Constraint)i.next();
            if (!c.checkVars()) {
                return false;
            }
        }
        return true;
    }

    @Override
    public String toHTML() {
        StringBuffer temp = new StringBuffer();
        for (Iterator i = this.iterator(); i.hasNext();) {
            Constraint c = (Constraint)i.next();
            temp.append(c.toHTML()+"<BR>\n");
        }
        return "<B>"+temp.toString()+"</B>";
    }

}
