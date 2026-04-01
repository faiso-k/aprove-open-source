package aprove.verification.theoremprover.TheoremProverProcedures.Induction;

import java.util.*;
import java.util.Map.Entry;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LinearArithmetic.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 *
 * @author dickmeis
 * @version $Id$
 */

public class InductionSchemeComponent implements Exportable, HTML_Able, PLAIN_Able, LaTeX_Able{

    private InductionSchemeTupel conclusion;
    private List<InductionSchemeTupel> hypotheses;

    public InductionSchemeComponent(InductionSchemeTupel conclusion,
                           List<InductionSchemeTupel> hypotheses){
        this.conclusion = conclusion;
        this.hypotheses = hypotheses;
    }

    public InductionSchemeTupel getConclusion() {
        return this.conclusion;
    }

    public List<InductionSchemeTupel> getHypotheses() {
        return this.hypotheses;
    }

    @Override
    public String toString(){
        StringBuilder sb = new StringBuilder();

        sb.append("Conclusion: ");
        sb.append(this.conclusion);
        sb.append("\nHypotheses: ");
        sb.append(this.hypotheses);
        return sb.toString();
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder sb = new StringBuilder();

        sb.append("Conclusion: ");
        sb.append(this.conclusion.export(o));
        sb.append(o.newline());
        sb.append("Hypotheses: ");
        sb.append(o.set(this.hypotheses, 12));

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
     * Merges this with the given induction scheme component and returns its outcome.
     *
     * @param that the induction scheme component to merge with
     * @param useLA whether LA should be used
     * @return the merged induction scheme component
     */
    public InductionSchemeComponent merge(InductionSchemeComponent that,
            boolean useLA, LAProgramProperties laProgram, List<AlgebraVariable> variableOrdering) {
        InductionSchemeTupel thisConclusion = this.getConclusion();
        InductionSchemeTupel thatConclusion = that.getConclusion();

        AlgebraSubstitution thisSubst = thisConclusion.getSubstitution();
        AlgebraSubstitution thatSubst = thatConclusion.getSubstitution();

        Set<VariableSymbol> thisSubstDom = thisSubst.getDomain();
        Set<VariableSymbol> thatSubstDom = thatSubst.getDomain();

        AlgebraSubstitution delta;
        AlgebraSubstitution sigma;
        List<Equation> conds_c;
        List<Pair<Position, AlgebraTerm>> replacement;
        List<InductionSchemeTupel> hypotheses;

        List<Equation> thisConds = thisConclusion.getConditions();
        List<Equation> thatConds = thatConclusion.getConditions();

        if (useLA){
            LASolver las = new LASolver(variableOrdering);

            List<LinearConstraint> constraints = InductionSchemeComponent.SubstitutionToEquations(thisSubst, laProgram);
            las.addAllConstraints(constraints);

            constraints = InductionSchemeComponent.SubstitutionToEquations(thatSubst, laProgram);
            las.addAllConstraints(constraints);

            for (Equation eq : thisConds) {
                LinearConstraint constraint = LinearConstraint.create(eq, laProgram);
                las.addConstraint(constraint);
            }

            for (Equation eq : thatConds) {
                LinearConstraint constraint = LinearConstraint.create(eq, laProgram);
                las.addConstraint(constraint);
            }

            boolean solveable = las.solve();

            if(!solveable){
                // no merged induction case generated
                return null;
            }

            delta = LinearIntegerHelper.toSubstitution(las.getDissolvings(), laProgram);

            sigma = delta;

            ArrayList<LinearConstraint> c_c = las.getAllConstraints();

            conds_c = new ArrayList<Equation>(c_c.size());
            for (LinearConstraint constraint : c_c) {
                Equation eq = LinearIntegerHelper.toEquation(constraint, laProgram);
                conds_c.add(eq);
            }
        }
        else {
            delta = AlgebraSubstitution.create();

            for (VariableSymbol symbol : thisSubstDom) {
                if (!thatSubstDom.contains(symbol)){
                    continue;
                }

                // now we have the intersection of variables

                AlgebraTerm s = thisSubst.get(symbol);
                AlgebraTerm t = thatSubst.get(symbol);

                try {
                    delta = s.unifies(t,delta);
                }
                catch (UnificationException e) {
                    return null;
                }
            }

            AlgebraSubstitution subst1 = thisSubst.compose(delta);
            AlgebraSubstitution subst2 = thatSubst.compose(delta);

            // union of two disjunct substitutions
            sigma = subst1;
            for (Entry<VariableSymbol, AlgebraTerm> entry : subst2.getMapping().entrySet()) {
                VariableSymbol key = entry.getKey();
                AlgebraTerm value = entry.getValue();

                sigma.put(key, value);
            }

            conds_c = new ArrayList<Equation>(thisConds.size() + thatConds.size());

            for (Equation equation : thisConds) {
                Equation eq = (Equation)equation.apply(delta);
                conds_c.add(eq);
            }

            for (Equation equation : thatConds) {
                Equation eq = (Equation)equation.apply(delta);
                conds_c.add(eq);
            }
        }

        List<Pair<Position, AlgebraTerm>> thisReplacement = thisConclusion.getReplacement();
        List<Pair<Position, AlgebraTerm>> thatReplacement = thatConclusion.getReplacement();

        replacement = new ArrayList<Pair<Position,AlgebraTerm>>(
                thisReplacement.size() + thatReplacement.size());

        for (Pair<Position, AlgebraTerm> pair : thisReplacement) {
            AlgebraTerm r = pair.y.apply(delta);
            replacement.add(new Pair<Position, AlgebraTerm>(pair.x, r));
        }

        for (Pair<Position, AlgebraTerm> pair : thatReplacement) {
            AlgebraTerm r = pair.y.apply(delta);
            replacement.add(new Pair<Position, AlgebraTerm>(pair.x, r));
        }


        List<InductionSchemeTupel> thisHypotheses = this.getHypotheses();
        List<InductionSchemeTupel> thatHypotheses = that.getHypotheses();

        hypotheses = new ArrayList<InductionSchemeTupel>(
                thisHypotheses.size() + thatHypotheses.size());

        for (InductionSchemeTupel tupel_i : thisHypotheses) {

            Set<AlgebraVariable> thisVars = this.getVariables();
            List<InductionSchemeTupel> newHypotheses =
                this.mergeHypothesesTupel(tupel_i, thisVars, that, delta, laProgram);
            this.mergingHypothesesAdd(hypotheses, newHypotheses);

        }

        for (InductionSchemeTupel tupel_j : thatHypotheses) {

            Set<AlgebraVariable> thatVars = that.getVariables();
            List<InductionSchemeTupel> newHypotheses =
                this.mergeHypothesesTupel(tupel_j, thatVars, this, delta, laProgram);
            this.mergingHypothesesAdd(hypotheses, newHypotheses);

        }


        InductionSchemeTupel conclusion = new InductionSchemeTupel(sigma, conds_c, replacement);

        InductionSchemeComponent isc = new InductionSchemeComponent(conclusion, hypotheses);

        return isc;

    }

    /**
     * Merges the hypotheses.
     * If the substitutions and the conditions are identical
     * the new replacement is the union of the two others
     *
     * @param hypotheses
     * @param newHypotheses
     */
    private void mergingHypothesesAdd(List<InductionSchemeTupel> hypotheses,
            List<InductionSchemeTupel> newHypotheses) {

        outer : for (InductionSchemeTupel newTupel : newHypotheses) {
            AlgebraSubstitution newSubstitution = newTupel.getSubstitution();
            List<Equation> newConditions = newTupel.getConditions();

            for (InductionSchemeTupel tupel : hypotheses) {

                AlgebraSubstitution substitution = tupel.getSubstitution();
                List<Equation> conditions = tupel.getConditions();

                if(substitution.equals(newSubstitution) &&
                        conditions.containsAll(newConditions) &&
                        newConditions.containsAll(conditions)){

                    List<Pair<Position, AlgebraTerm>> newReplacement = newTupel.getReplacement();
                    List<Pair<Position, AlgebraTerm>> replacement = tupel.getReplacement();

                    replacement.addAll(newReplacement);
                }
                else{
                    hypotheses.add(newTupel);
                    continue outer;
                }
            }

            if (hypotheses.isEmpty()){
                hypotheses.add(newTupel);
            }
        }
    }

    /**
     * Merges a tupel with the hypotheses tupel of the given induction scheme component
     *
     * @param tupel the tupel to be merged
     * @param thisVars
     * @param that the induction scheme component which tupels of the hypotheses have to be merged with
     * @param unificator
     * @param laProgram
     *
     * @return a list with the results
     */
    private List<InductionSchemeTupel> mergeHypothesesTupel(
            InductionSchemeTupel tupel, Set<AlgebraVariable> thisVars,
            InductionSchemeComponent that, AlgebraSubstitution unificator,
            LAProgramProperties laProgram){

        List<InductionSchemeTupel> thatHypotheses = that.getHypotheses();
        AlgebraSubstitution thatSubst = that.getConclusion().getSubstitution();

        List<InductionSchemeTupel> hypotheses = new ArrayList<InductionSchemeTupel>(thatHypotheses.size());

        List<Equation>conds_i = tupel.getConditions();

        List<Pair<Position, AlgebraTerm>> replacement_i = tupel.getReplacement();

        List<Pair<Position, AlgebraTerm>> replacement_h = new ArrayList<Pair<Position,AlgebraTerm>>(replacement_i.size());

        for (Pair<Position, AlgebraTerm> pair : replacement_i) {
            AlgebraTerm r = pair.y.apply(unificator);
            replacement_h.add(new Pair<Position, AlgebraTerm>(pair.x, r));
        }

        AlgebraSubstitution iSubst = tupel.getSubstitution();
        AlgebraSubstitution sigma_ij = iSubst.compose(unificator);
        Set<AlgebraVariable> thatVars = that.getVariables();

        Set<AlgebraVariable> onlythatVars = new HashSet<AlgebraVariable>(thatVars.size());
        for (AlgebraVariable variable : thatVars) {
            if(!thisVars.contains(variable)){
                onlythatVars.add(variable);
            }
        }

        AlgebraSubstitution gamma_j;

        if(thatHypotheses.isEmpty()){

            gamma_j = thatSubst.restrictTo(onlythatVars);

            // union
            // and check if union is consistent
            for (Entry<VariableSymbol, AlgebraTerm> entry : gamma_j.getMapping().entrySet()) {
                VariableSymbol key = entry.getKey();
                AlgebraTerm value = entry.getValue();

                AlgebraTerm othervalue = sigma_ij.get(key);
                if(othervalue!=null){
                    if(!value.equals(othervalue)){
                        // not consistent
                        return null;
                    }
                }

                sigma_ij.put(key, value);
            }

            if(laProgram != null){

                LASolver las = new LASolver(new ArrayList<AlgebraVariable>());
                List<LinearConstraint> constraints = InductionSchemeComponent.SubstitutionToEquations(sigma_ij, laProgram);
                las.addAllConstraints(constraints);

                List<Equation> thisCond_i = tupel.getConditions();
                for (Equation equation : thisCond_i) {
                    las.addConstraint(equation, laProgram);
                }

                boolean solveable = las.solve();

                if(!solveable){
                    // not included
                    return hypotheses;
                }
            }

            List<Equation>conds_h = new ArrayList<Equation>(conds_i.size());

            for (Equation equation : conds_i) {
                Equation eq = (Equation) equation.apply(unificator);
                conds_h.add(eq);
            }

            InductionSchemeTupel ist = new InductionSchemeTupel(sigma_ij, conds_h, replacement_h);
            hypotheses.add(ist);
        }
        else{
            for (InductionSchemeTupel tupel_j : thatHypotheses) {

                gamma_j = tupel_j.getSubstitution().restrictTo(onlythatVars);

                // union
                // and check if union is consistent
                for (Entry<VariableSymbol, AlgebraTerm> entry : gamma_j.getMapping().entrySet()) {
                    VariableSymbol key = entry.getKey();
                    AlgebraTerm value = entry.getValue();

                    AlgebraTerm othervalue = sigma_ij.get(key);
                    if(othervalue!=null){
                        if(!value.equals(othervalue)){
                            // not consistent
                            return null;
                        }
                    }

                    sigma_ij.put(key, value);
                }

                if(laProgram != null){

                    LASolver las = new LASolver(new ArrayList<AlgebraVariable>());
                    List<LinearConstraint> constraints = InductionSchemeComponent.SubstitutionToEquations(sigma_ij, laProgram);
                    las.addAllConstraints(constraints);

                    List<Equation> thisCond_i = conds_i;
                    for (Equation equation : thisCond_i) {
                        las.addConstraint(equation, laProgram);
                    }

                    List<Equation> thatCond_j = tupel_j.getConditions();
                    for (Equation equation : thatCond_j) {
                        las.addConstraint(equation, laProgram);
                    }

                    boolean solveable = las.solve();

                    if(!solveable){
                        // not included
                        continue;
                    }
                }

                List<Equation> thatHypoConds = tupel_j.getConditions();

                List<Equation>conds_h = new ArrayList<Equation>(conds_i.size() + thatHypoConds.size());

                for (Equation equation : conds_i) {
                    Equation eq = (Equation) equation.apply(unificator);
                    conds_h.add(eq);
                }

                for (Equation equation : thatHypoConds) {
                    Equation eq = (Equation) equation.apply(unificator);
                    conds_h.add(eq);
                }

                // simplify
                if(laProgram != null){
                    LinearIntegerConstraintSimplifier lics = new LinearIntegerConstraintSimplifier();

                    for (Equation equation : conds_h) {
                        LinearConstraint constraint = LinearConstraint.create(equation, laProgram);
                        lics.addConstraint(constraint);
                    }

                    boolean satisfiable =lics.simplify();

                    if (satisfiable){

                        ArrayList<LinearConstraint> conds_h_constraints = lics.getAllConstraints();
                        ArrayList<Dissolving> dissolvings = lics.getDissolvings();

                        conds_h = new ArrayList<Equation>(conds_h.size() + dissolvings.size());

                        for (LinearConstraint constraint : conds_h_constraints) {
                            Equation eq = LinearIntegerHelper.toEquation(constraint, laProgram);
                            conds_h.add(eq);
                        }

                        for (Dissolving dissolving : dissolvings) {
                            Equation eq = LinearIntegerHelper.toEquation(dissolving.toEquation(), laProgram);
                            conds_h.add(eq);
                        }
                    }
                    else{
                        conds_h = new ArrayList<Equation>(1);
                        Equation eq = Equation.create(ConstructorApp.create(laProgram.csFalse), ConstructorApp.create(laProgram.csTrue));

                        conds_h.add(eq);
                    }

                    InductionSchemeTupel ist = new InductionSchemeTupel(sigma_ij, conds_h, replacement_h);
                    hypotheses.add(ist);
                }
                else{
                    // remove duplicates
                    HashSet<Equation> conds_h_set = new HashSet<Equation>(conds_h);
                    conds_h = new ArrayList<Equation>(conds_h_set);
                }

                InductionSchemeTupel ist = new InductionSchemeTupel(sigma_ij, conds_h, replacement_h);
                hypotheses.add(ist);

            }

        }

        return hypotheses;
    }

    /**
     * Transforms a substitution into a list of equations
     *
     * @param substitution The substitution to transform
     * @param laProgram Background information about the properties of LA
     *
     * @return the corresponding list of equations
     */
    private static List<LinearConstraint> SubstitutionToEquations(
            AlgebraSubstitution substitution, LAProgramProperties laProgram){

        Map<VariableSymbol, AlgebraTerm> mapping = substitution.getMapping();

        ArrayList<LinearConstraint> constraints = new ArrayList<LinearConstraint>(mapping.size());

        Set<AlgebraVariable> vars = substitution.getTermDomain();

        for (AlgebraVariable variable : vars) {
            AlgebraTerm right = mapping.get(variable.getVariableSymbol());

            LinearConstraint constraint = LinearConstraint.createEquation(variable, right, laProgram);

            constraints.add(constraint);
        }

        return constraints;

    }


    /**
     * returns all variables occuring in this
     *
     * @return all occuring variables
     */
    public Set<AlgebraVariable> getVariables(){
        Set<AlgebraVariable> vars = new HashSet<AlgebraVariable>();

        vars.addAll(this.conclusion.getVariables());

        for (InductionSchemeTupel ist : this.hypotheses) {
            vars.addAll(ist.getVariables());
        }

        return vars ;
    }

    public InductionSchemeComponent deepcopy() {

        ArrayList<InductionSchemeTupel> newHypotheses =
            new ArrayList<InductionSchemeTupel>(this.hypotheses.size());

        for (InductionSchemeTupel tupel : this.hypotheses) {
            newHypotheses.add(tupel.deepcopy());
        }

        return new InductionSchemeComponent(this.conclusion.deepcopy(), newHypotheses);
    }
}
