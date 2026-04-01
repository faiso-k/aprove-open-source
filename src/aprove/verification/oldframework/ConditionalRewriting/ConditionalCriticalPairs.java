package aprove.verification.oldframework.ConditionalRewriting;

import java.util.*;

import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LinearArithmetic.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Logic.Formulas.Visitors.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.theoremprover.TheoremProverProcedures.*;

/**
 * Generates the conditional critical pairs that can be formed from a set of
 * rules.
 * With the function removeJoinable() we try to find all joinable pairs.
 * Therefore we use evaluation and generalisation.
 *
 * @author Thomas Dickmeis
 * @version $Id$
 */

public class ConditionalCriticalPairs extends
        LinkedHashSet<ConditionalCriticalPair> {

    private ConditionalCriticalPairs() {
        super();
    }

    /**
     * Generates all conditional critical pairs of a program.
     *
     * @param program the program to generate the critical pairs from
     * @return all generated conditional critial pairs
     */
    public static ConditionalCriticalPairs create(Program program) {
        return ConditionalCriticalPairs.create(program.getRules(), program.laProgramProperties);
    }

    /**
     * Generates all conditional critical pairs of R.
     *
     * @param R the rules to generate the critical pairs from
     * @param laProgram LAProgramProperties use null, if you do not want to use LA
     * @return all generated conditional critial pairs
     */
    public static ConditionalCriticalPairs create(Collection<Rule> R, LAProgramProperties laProgram) {
        ConditionalCriticalPairs res = new ConditionalCriticalPairs();

        Iterator<Rule> i = R.iterator();
        while (i.hasNext()) {
            res.addAll(ConditionalCriticalPairs.generateCPs(i.next(), R, laProgram));
        }

        return res;
    }

    /**
     * Computes the conditional critical pairs of r with R.
     *
     * @param r
     * @param R
     * @param laProgram LAProgramProperties use null, if you do not want to use LA
     * @return all conditional critical pairs of r with R
     */
    public static ConditionalCriticalPairs generateCPs(Rule r, Collection<Rule> R, LAProgramProperties laProgram) {
        ConditionalCriticalPairs res = new ConditionalCriticalPairs();

        Iterator<Rule> i = R.iterator();
        while (i.hasNext()) {
            res.addAll(ConditionalCriticalPairs.create(r, i.next(), laProgram));
        }

        return res;
    }

    /**
     * Computes the conditional critical pairs of r with itself.
     *
     * @param r the rule
     * @param laProgram LAProgramProperties use null, if you do not want to use LA
     * @return all conditional critical pairs of r with itself
     */
    public static ConditionalCriticalPairs create(Rule r, LAProgramProperties laProgram) {
        ConditionalCriticalPairs result = ConditionalCriticalPairs.create(r, r, laProgram);
        return result;
    }


    public ConditionalCriticalPairs deepcopy() {
        ConditionalCriticalPairs result = new ConditionalCriticalPairs();
        Iterator<ConditionalCriticalPair> i = this.iterator();
        while (i.hasNext()) {
            result.add(i.next());
        }
        return result;
    }

    /**
     * Computes the conditional critical pairs of newRule1 with s.
     *
     * @param newRule1
     * @param s
     * @param laProgram
     * @return all conditional critical pairs of newRule1 with s
     */
    public static ConditionalCriticalPairs create(Rule newRule1, Rule s, LAProgramProperties laProgram) {
        ConditionalCriticalPairs res = new ConditionalCriticalPairs();

        boolean eq = newRule1.equals(s);

        Set<AlgebraVariable> usedVars = newRule1.getUsedVariables();
        Rule newRule2 = s.replaceVariables(usedVars);

        AlgebraTerm l1 = newRule1.getLeft();
        AlgebraTerm r1 = newRule1.getRight();
        AlgebraTerm l2 = newRule2.getLeft();
        AlgebraTerm r2 = newRule2.getRight();

        Set<Position> occ = l1.getPositions();
        Iterator i = occ.iterator();

        while (i.hasNext()) {
            Position pi = (Position) i.next();

            if (!pi.isRootPosition() || !eq) {
                AlgebraTerm l1_pi = l1.getSubterm(pi);
                if (!l1_pi.isVariable()) {
                    try {

                        AlgebraSubstitution sigma = null;

                        if(IsLATermVisitor.apply(l1_pi, laProgram) && IsLATermVisitor.apply(l2, laProgram))
                        {
                            // if both are LA terms
                            LinearConstraint constraint = LinearConstraint.createEquation(l1_pi, l2, laProgram);

                            LASolver las = new LASolver();
                            las.addConstraint(constraint);

                            boolean satisfiable = las.solve();

                            if(!satisfiable || !las.getAllConstraints().isEmpty()){
                                // not unifyable
                                continue;
                            }

                            ArrayList<Dissolving> dissolvings = las.getDissolvings();

                            sigma = LinearIntegerHelper.toSubstitution(dissolvings, laProgram);
                        }
                        else{
                            if (l1_pi instanceof AlgebraFunctionApplication) {
                                AlgebraFunctionApplication l1_pi_fa = (AlgebraFunctionApplication) l1_pi;
                                SyntacticFunctionSymbol l1_fs = l1_pi_fa.getFunctionSymbol();
                                if(laProgram.semilaBasedFunctionSymbols.contains(l1_fs)){
                                    if (l2 instanceof AlgebraFunctionApplication) {
                                        AlgebraFunctionApplication l2_fa = (AlgebraFunctionApplication) l2;
                                        SyntacticFunctionSymbol l2_fs = l2_fa.getFunctionSymbol();
                                        if(l1_fs.equals(l2_fs)){
                                            LASolver las = new LASolver();

                                            for(int j=0; j < l2_fs.getArity(); j++){

                                                LinearConstraint constraint = LinearConstraint.createEquation(
                                                        l1_pi_fa.getArgument(j), l2_fa.getArgument(j), laProgram);

                                                las.addConstraint(constraint);
                                            }

                                            boolean satisfiable = las.solve();

                                            if(!satisfiable || !las.getAllConstraints().isEmpty()){
                                                // not unifyable
                                                continue;
                                            }

                                            ArrayList<Dissolving> dissolvings = las.getDissolvings();

                                            sigma = LinearIntegerHelper.toSubstitution(dissolvings, laProgram);
                                        }
                                        else{
                                            // not unifyable
                                            continue;
                                        }
                                    }
                                    else{
                                        // not unifyable
                                        continue;
                                    }
                                }
                                else{
                                    sigma = l1_pi.unifies(l2);
                                }
                            }
                            else{
                                sigma = l1_pi.unifies(l2);
                            }
                        }

                        AlgebraTerm t = l1.deepcopy().replaceAt(r2, pi);

                        AlgebraTerm l = r1.apply(sigma);
                        AlgebraTerm r = t.apply(sigma);

                        List<Rule> conds1 = newRule1.getConds();
                        List<Rule> conds2 = newRule2.getConds();

                        Set<Rule> conds = new HashSet<Rule>(conds1.size() + conds2.size());

                        for (Rule rule : conds1) {
                            Rule newCond = rule.apply(sigma);
                            conds.add(newCond);
                        }
                        for (Rule rule : conds2) {
                            Rule newCond = rule.apply(sigma);
                            conds.add(newCond);
                        }

                        ConditionalCriticalPair ccp = new ConditionalCriticalPair(l, r, conds, newRule1, s);

                        res.add(ccp);
                    }
                    catch (UnificationException e) {
                        /* doesn't yield a CP */
                    }
                }
            }
        }

        return res;
    }

    /**
     * removes all conditional critical pairs that are joinable
     *
     * @param program the program with which they will be tried to join
     */
    public void removeJoinable(Program program){
        Iterator<ConditionalCriticalPair> iterator = this.iterator();

        while( iterator.hasNext()) {
            ConditionalCriticalPair ccp = (ConditionalCriticalPair) iterator.next();

            if(ccp.isTrivial()){
                iterator.remove();
                continue;
            }

            Equation eq = Equation.create(ccp.getLeft(), ccp.getRight());

            Set<Rule> conditions = ccp.getConditions();

            Formula formula=null;
            if(conditions.isEmpty()){
                formula = eq;
            }
            else{
                List<Equation> conds = new ArrayList<Equation>(conditions.size());

                for (Rule rule : conditions) {
                    AlgebraTerm l = rule.getLeft();
                    AlgebraTerm r = rule.getRight();
                    Equation cond = Equation.create(l, r);

                    conds.add(cond);
                }

                Formula premise = And.create(conds);

                Formula newpremise = this.evaluate(premise, program);

                if(newpremise.equals(FormulaTruthValue.FALSE)){
                    // check if the premise is unsatisfiable
                    iterator.remove();
                    continue;
                }

                formula = Implication.create(premise, eq);

            }

            Formula newformula = this.evaluate(formula, program);

            if(newformula.equals(FormulaTruthValue.TRUE)){
                iterator.remove();
                continue;
            }

            if (newformula instanceof Implication) {
                Implication impl = (Implication) newformula;
                newformula = impl.getRight();
            }

            List<Equation> eqs = InverseFunctionalityProcessor.inverseFunctionality(newformula);
            if(eqs != null){
                for (Equation equation : eqs) {
                    Formula neweq = this.evaluate(equation, program);

                    if(!neweq.equals(FormulaTruthValue.TRUE)){
                        break;
                    }
                }
                iterator.remove();
                continue;
            }

        }
    }


    /**
     * Evaluates a formula using symbolic evaluation
     *
     * @param formula the formula to evaluation
     * @param program the program with which it will be evaluated
     * @return the result of evaluation
     */
    private Formula evaluate(Formula formula, Program program){
        Formula newFormula=formula;

        if(program.laProgramProperties == null){
            do{
                formula = newFormula;
                newFormula = FormulaEvaluationVisitor.apply(formula, program);
            }
            while(!formula.equals(newFormula));
        }
        else{
            do{
                formula = newFormula;
                newFormula = FormulaOutermostLAEvaluationVisitor.apply(formula, program);
            }
            while(!formula.equals(newFormula));

            if(!formula.equals(FormulaTruthValue.TRUE)){
                Not negFormula = Not.create(formula);
                Formula negRes = LASimplificationProcessor.simplifyWithLA(negFormula, program);
                if(negRes.equals(FormulaTruthValue.FALSE)){
                    return FormulaTruthValue.TRUE;
                }
            }

        }

        return formula;
    }

}
