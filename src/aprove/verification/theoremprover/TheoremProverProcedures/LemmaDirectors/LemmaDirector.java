package aprove.verification.theoremprover.TheoremProverProcedures.LemmaDirectors;

import java.util.*;

import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.Algebra.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Rewriting.Rule;

/**
 * Manages the configurations of solvers.
 * With this configurations the solvers create orders.
 * A configurations are e.g. statuses and precedences.
 *
 * If we have found an applicable lemma which is an equation
 * and want to apply it from one side to the other
 * we check if such a direction works for an order specified by the configurations
 * and if so we work from then on with the new configurations.
 *
 * (Renamed from LemmaOrientator)
 *
 * @author dickmeis
 *
 */

public abstract class LemmaDirector {

    /**
     * all usable orders
     * a quasi order is possible, too
     * it is obtained via the configuration of the solver factory
     *
     *  the names must be a subset of MetaSolverFactory.getOrders()
     */
    private static String[] orders = {"LPO", "LPOS", "RPO", "RPOS"};

    /**
     * Returns all orders that can be used to orientate the lemmas
     *
     * The corresponding quasi order is usable, too.
     * It is obtained via the configuration of the solver factory.
     *
     * @return the list of all usable orders
     */
    public static String[] getUsableOrders(){
        return LemmaDirector.orders;
    }
    /**
     * The signature of the program
     */
    protected Set<FunctionSymbol> programSignature;

    /**
     * contains all valid configuration of the used solver
     * A configuration might consist of e.g. precedences, statuses.
     * If minimalHeuristic is set to true
     * there will always be only one configuration.
     */
    protected HashSet solverConfiguration;

    /**
     * If minimalHeuristic equals 0, all possible configurations
     * will be used in the next step. This may result in a large calculation effort.
     * If minimalHeuristic equals n>=1, only the n configurations with the least
     * restrictions is kept because they promise to be "most general".
     */
    protected int minimalHeuristic;

    LemmaDirector(Program program, int minimalHeuristic) {
        if (program != null) {
            Set<aprove.verification.oldframework.Syntax.SyntacticFunctionSymbol> sig = program.getFunctionSymbols();
            this.programSignature = new HashSet<FunctionSymbol>(sig.size());
            for (aprove.verification.oldframework.Syntax.SyntacticFunctionSymbol f : sig) {
                this.programSignature.add(f.toNewSymbol());
            }
        }

        this.minimalHeuristic = minimalHeuristic;
    }

    LemmaDirector(Program program) {
        this(program, 0);
    }

    /**
     * Creates a new solver
     *
     * @param programSiganature
     *             the signature of the program on which the solver should work
     * @param solverConfiguration
     *             the initial configuration of the solver
     * @return the new solver
     */
    abstract AbortableConstraintSolver<TRSTerm> newSolver(Set<FunctionSymbol> programSiganature,
            HashSet solverConfiguration);

    /**
     * Tries to orientate the rule (l>r). If this is possible the neccessary adaption
     * of the solver's configuration is stored
     *
     * @param rule
     *            to be orientated
     * @return true iff the rule was orientated successfully
     */
    public boolean extendByRule(Rule rule) {
        AbortableConstraintSolver<TRSTerm> abstractConstraintSolver;

        Set<Constraint<TRSTerm>> constraints = new LinkedHashSet<Constraint<TRSTerm>>();

        abstractConstraintSolver = this.newSolver(this.programSignature,
                this.solverConfiguration);

        constraints.add(Constraint.create(rule.getLeft().toNewTerm(), rule.getRight().toNewTerm(),
                OrderRelation.GR));

        try {
            abstractConstraintSolver.solve(constraints, AbortionFactory.create());
        } catch (AbortionException e) {
            if (aprove.Globals.DEBUG_DICKMEIS) {
                System.err.println(e);
            }
            return false;
        }

        HashSet newSolverConfiguration;
        newSolverConfiguration = this.getSolverConfiguration(abstractConstraintSolver);

        if (newSolverConfiguration != null) {

            if (this.minimalHeuristic==1) {
                SizeMeasure minimalConfiguration = (SizeMeasure) Collections.min(newSolverConfiguration, new SizeMeasureComparator());
                newSolverConfiguration = this.createNewSolverConfiguration();
                newSolverConfiguration.add(minimalConfiguration);
            }
            else if (this.minimalHeuristic>1) {
                ArrayList v = new ArrayList(newSolverConfiguration);
                Collections.sort(v, new SizeMeasureComparator());

                newSolverConfiguration = this.createNewSolverConfiguration();
                for (int i=0; i<this.minimalHeuristic && i<v.size(); i++) {
                    newSolverConfiguration.add(v.get(i));
                }
            }

            this.solverConfiguration = newSolverConfiguration;
            return true;
        }

        return false;
    }

//  /**
//  * Tries to sequentially orientate all unconditional rules
//  * of a given set of program rules and builds up an suitable order
//  *
//  * @param rules the set of program rules which should be orientated
//  */
//  public void orientateProgramRules(Set<Rule> rules){
//
//  for (Rule rule : rules) {
//
//  // only orientate unconditional rules
//  if (rule.getConds().isEmpty()){
//  extendByRule(rule);
//  }
//  }
//  this.programOrientated = true;
//  }

    /**
     * Gets all valid configurations of the solver
     * Needed to make the right casts
     *
     * @return all valid configurations
     */
    protected abstract HashSet getSolverConfiguration(AbortableConstraintSolver<TRSTerm> abstractConstraintSolver);

    public HashSet getSolverConfiguration(){
        return this.solverConfiguration;
    }

    public void setSolverConfiguration(HashSet solverConfiguration){
        this.solverConfiguration = solverConfiguration;
    }

    /**
     * Creates an empty configuration for the solver
     *
     * @return an empty configuration for the solver
     */
    abstract public HashSet createNewSolverConfiguration();


    /**
     * Comparator for the size of configurations
     */
    class SizeMeasureComparator implements Comparator{
        @Override
        public int compare(Object o1, Object o2) {
            if (o1 instanceof SizeMeasure) {
                SizeMeasure sm1 = (SizeMeasure) o1;
                if (o2 instanceof SizeMeasure) {
                    SizeMeasure sm2 = (SizeMeasure) o2;
                    return sm1.getSizeMeasure() - sm2.getSizeMeasure();
                }
                return 0;
            }
            return 0;
        }
    }

}
