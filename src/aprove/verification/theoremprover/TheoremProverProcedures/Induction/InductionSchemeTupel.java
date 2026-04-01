package aprove.verification.theoremprover.TheoremProverProcedures.Induction;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A class for an induction scheme tupel.
 *
 * @author dickmeis
 * @version $Id$
 */

public class InductionSchemeTupel implements Exportable, HTML_Able, PLAIN_Able, LaTeX_Able {

    private AlgebraSubstitution substitution;
    private List<Equation> conditions;
    private List<Pair<Position, AlgebraTerm>> replacement;

    public InductionSchemeTupel (AlgebraSubstitution substitution,
                                     List<Equation> conditions,
                                     List<Pair<Position, AlgebraTerm>> replacement){
        this.substitution = substitution;
        this.conditions = conditions;
        this.replacement = replacement;
    }

    public List<Equation> getConditions() {
        return this.conditions;
    }

    public List<Pair<Position, AlgebraTerm>> getReplacement(){
        return this.replacement;
    }

    public AlgebraSubstitution getSubstitution() {
        return this.substitution;
    }

    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();

        sb.append("Substitution: ");
        sb.append(this.substitution);
        sb.append(", Conditions: ");
        sb.append(this.conditions);
        sb.append(", Replacement: ");

        sb.append("{ ");

        Iterator<Pair<Position, AlgebraTerm>> iterator = this.replacement.iterator();

        if (iterator.hasNext()){
            Pair<Position, AlgebraTerm> p = iterator.next();
            sb.append(p.x);
            sb.append(" <-- ");
            sb.append(p.y);
        }

        while (iterator.hasNext()){
            sb.append(", ");
            Pair<Position, AlgebraTerm> p = iterator.next();
            sb.append(p.x);
            sb.append(" <-- ");
            sb.append(p.y);
        }

        sb.append(" }");

        return sb.toString();
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder sb = new StringBuilder();

        sb.append("Substitution: ");
        sb.append(this.substitution);
        sb.append(", Conditions: ");
        sb.append(o.set(this.conditions,12));
        sb.append(", Replacement: ");

        sb.append("{ ");

        Iterator<Pair<Position, AlgebraTerm>> iterator = this.replacement.iterator();

        if (iterator.hasNext()){
            Pair<Position, AlgebraTerm> p = iterator.next();
            sb.append(p.x);
            sb.append(" -- ");
            sb.append(p.y.export(o));
        }

        while (iterator.hasNext()){
            sb.append(", ");
            Pair<Position, AlgebraTerm> p = iterator.next();
            sb.append(p.x);
            sb.append(" -- ");
            sb.append(p.y.export(o));
        }

        sb.append(" }");

        return sb.toString();
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

    /**
     * Returns all occuring variables
     *
     * @return all occuring variables
     */
    public Set<AlgebraVariable> getVariables(){
        Set<AlgebraVariable> vars = new HashSet<AlgebraVariable>();

        vars.addAll(this.substitution.getTermDomain());
        vars.addAll(this.substitution.getRangeVariables());

        for (Equation eq : this.conditions) {
            vars.addAll(eq.getAllVariables());
        }

        for (Pair<Position, AlgebraTerm> p : this.replacement) {
            vars.addAll(p.y.getVars());
        }

        return vars ;
    }

    public InductionSchemeTupel deepcopy() {
        AlgebraSubstitution newSubstitution = this.substitution.deepcopy();

        ArrayList<Equation> newConditions = new ArrayList<Equation>(this.conditions.size());
        for (Equation equation : this.conditions) {
            newConditions.add((Equation)equation.deepcopy());
        }

        ArrayList<Pair<Position, AlgebraTerm>> newReplacement = new ArrayList<Pair<Position,AlgebraTerm>>(this.replacement.size());
        for (Pair<Position, AlgebraTerm> pair : this.replacement) {
            Pair<Position, AlgebraTerm> p = new Pair<Position, AlgebraTerm>(pair.x.deepcopy(), pair.y.deepcopy());
            newReplacement.add(p);
        }

        return new InductionSchemeTupel(newSubstitution, newConditions, newReplacement);
    }

}
