package aprove.verification.theoremprover.TheoremProverProcedures.Induction;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;

/**
 * A class for a cover set triple.
 *
 * @author dickmeis
 * @version $Id$
 */

public class CoverSetTriple implements Exportable, HTML_Able, PLAIN_Able, LaTeX_Able{

    private List<AlgebraTerm> leftArguments;
    private List<List<AlgebraTerm>> allRecursiveArguments;
    private List<Equation> conditions;

    public CoverSetTriple(List<AlgebraTerm> leftArguments, List<List<AlgebraTerm>> allRecursiveArguments,
                          List<Equation> conditions){

        this.leftArguments = leftArguments;
        this.allRecursiveArguments = allRecursiveArguments;
        this.conditions = conditions;

    }

    public List<AlgebraTerm> getLeftArguments(){
        return this.leftArguments;
    }

    public List<List<AlgebraTerm>> getAllRecursiveArguments(){
        return this.allRecursiveArguments;
    }

    public List<Equation> getConditions(){
        return this.conditions;
    }

    public Set<AlgebraVariable> getVariables(){
        Set<AlgebraVariable> vars = new HashSet<AlgebraVariable>();

        for (AlgebraTerm t : this.leftArguments) {
            vars.addAll(t.getVars());
        }

        for (List<AlgebraTerm> lt : this.allRecursiveArguments) {
            for (AlgebraTerm t : lt) {
                vars.addAll(t.getVars());
            }
        }

        for (Equation c : this.conditions) {
            vars.addAll(c.getAllVariables());
        }

        return vars;
    }

    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();

        sb.append("(");
        sb.append(this.leftArguments);
        sb.append(", ");
        sb.append(this.allRecursiveArguments);
        sb.append(", ");
        sb.append(this.conditions);
        sb.append(")");

        return sb.toString();
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder sb = new StringBuilder();

        sb.append("(");
        sb.append(o.set(this.leftArguments, 12));
        sb.append(", ");

        if(this.allRecursiveArguments.isEmpty()){
            sb.append("{}");
        }
        else{
            sb.append("{");
            Iterator<List<AlgebraTerm>> iterator = this.allRecursiveArguments.iterator();

            sb.append(o.set(iterator.next(),12));

            while(iterator.hasNext()){
                sb.append(", ");
                sb.append(o.set(iterator.next(),12));
            }

            sb.append("}");
        }

        sb.append(", ");
        sb.append(o.set(this.conditions, 12));
        sb.append(")");

        return sb.toString();
    }

    public CoverSetTriple deepcopy() {
        List<AlgebraTerm> newLeftArguments = new ArrayList<AlgebraTerm>(this.leftArguments.size());
        for (AlgebraTerm arg : this.leftArguments) {
            newLeftArguments.add(arg.deepcopy());
        }

        List<List<AlgebraTerm>> newAllRecursiveArguments = new ArrayList<List<AlgebraTerm>>(this.allRecursiveArguments.size());
        for (List<AlgebraTerm> list : this.allRecursiveArguments) {
            List<AlgebraTerm> newList = new ArrayList<AlgebraTerm>(list.size());
            for (AlgebraTerm term : list) {
                newList.add(term.deepcopy());
            }
            newAllRecursiveArguments.add(newList);
        }

        List<Equation> newConditions = new ArrayList<Equation>(this.conditions.size());
        for (Equation equation : this.conditions) {
            newConditions.add((Equation)equation.deepcopy());
        }

        return new CoverSetTriple(newLeftArguments, newAllRecursiveArguments,
                newConditions);
    }

    @Override
    public String toLaTeX() {
        return this.export(new LaTeX_Util());
    }

    @Override
    public String toHTML() {
        return this.export(new HTML_Util());
    }

    @Override
    public String toPLAIN() {
        return this.export(new PLAIN_Util());
    }
}