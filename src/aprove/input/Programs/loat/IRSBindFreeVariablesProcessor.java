package aprove.input.Programs.loat;

import java.util.*;
import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * This class binds free variables in a given IRS.
 * It takes an IRS as obligation and returns a new IRS with no free variables.
 * 
 * This processor is used in combination with LoAT as backend to detect non-termination. 
 * It is necessary to bind the free variables to get a non-empty set as output from LoAT.
 * That set, again, is used to generate a violation witness.
 * 
 * @author Constantin Mensendiek
 */
public class IRSBindFreeVariablesProcessor extends Processor.ProcessorSkeleton {

    @Override
    public Result process(BasicObligation obl,
                          BasicObligationNode oblNode,
                          Abortion aborter,
                          RuntimeInformation rti) throws AbortionException {
        assert !Globals.useAssertions || obl instanceof IRSProblem;

        IRSProblem problem = (IRSProblem) obl;

        Triple<Set<IGeneralizedRule>, CollectionMap<String, String>, String> boundedRules =
                                                                                          bindFreeVariables(problem.getRules());

        IRSProblem newProblem = new IRSProblem(ImmutableCreator.create(boundedRules.x), problem.getStartTerm());
        newProblem.setParent(problem);
        newProblem.setVariableRenaming(boundedRules.y);

        return ResultFactory.provedAnd(Collections.singletonList(newProblem),
                                       YNMImplication.COMPLETE,
                                       new IRSBindFreeVariablesProof(boundedRules.z));
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof IRSProblem;
    }

    /**
     * Step (1) If the parameter useReplacing is set:
     * free variables that are sufficiently bound by the guard are replaced accordingly.
     * 
     * Step (2) Collect all remaining free variables and create a dummy variable for each free one.
     * 
     * Step (3) Append the list of dummy variables to each side of every rule. 
     * If the counterpart to the dummy variable appear in the rule, 
     * then substitute the dummy by the counterpart beforehand.
     * 
     * 
     * @param rules the rules of the IRS that supposed to be bound
     * @return 
     *  1. new set of rules with only bound variables, 
     *  2. a map for the fresh dummy variables,
     *  3. a string containing some log entries
     * 
     */
    private Triple<Set<IGeneralizedRule>, CollectionMap<String, String>, String>
            bindFreeVariables(Set<IGeneralizedRule> rules) {
        Set<IGeneralizedRule> currentRules = new HashSet<>();
        Set<IGeneralizedRule> newRules = new HashSet<>();
        String log = "";
        
        if (this.useReplacing) {
            // bind free variables that are sufficiently constrained
            log = "\nThe free variable in these rules were replaced by the term induced by the guard:\n\n";
            for (IGeneralizedRule r : rules) {
                Set<TRSVariable> unboundedVars = r.getRule().getUnboundedVariables();
                IGeneralizedRule currentRule = IGeneralizedRule.create(r.getLeft(), r.getRight(), r.getCondTerm());
                // find correct term to substitute free variable with
                for (TRSVariable current : unboundedVars) {
                    TRSTerm guard = currentRule.getCondTerm();
                    Optional<TRSTerm> replacement = Optional.empty();
                    if (guard instanceof TRSCompoundTerm)
                        replacement = findReplacementFor(current, (TRSCompoundTerm) guard);
                    if (replacement.isPresent()) {
                        TRSSubstitution substitution = TRSSubstitution.create(current, replacement.get());
                        TRSTerm rhs = currentRule.getRight().applySubstitution(substitution);
                        TRSTerm cond = currentRule.getCondTerm().applySubstitution(substitution);
                        currentRule = IGeneralizedRule.create(currentRule.getLeft(), rhs, cond);
                        log += substitution.toString() + "\n" + currentRule.toString() + "\n\n";
                    }
                }
                newRules.add(currentRule);
            }
            currentRules = newRules;
        } else {
            for (IGeneralizedRule r : rules) {
                currentRules.add(r);
            }
        }

        // collect all original variables of the rules
        Set<TRSVariable> allOriginalVars = new HashSet<>();
        currentRules.forEach(r -> allOriginalVars.addAll(r.getAllVariables()));

        // generate dummies for each free variables
        log += "\nThe free variables are assigned the following fresh dummy variables:\n\n";
        Set<TRSVariable> freeVars = new HashSet<>();
        currentRules.forEach(r -> freeVars.addAll(r.getRule().getUnboundedVariables()));
        Map<TRSVariable, TRSVariable> dummyVarsMap = new HashMap<>();
        int i = 0;
        for (TRSVariable free : freeVars) {
            TRSVariable dummy;
            // make sure dummy variable is fresh
            do {
                dummy = TRSTerm.createVariable("f" + i);
                i++;
            } while (allOriginalVars.contains(dummy));
            // and add it to the dummy variables map
            dummyVarsMap.put(free, dummy);
            log += free.getName() + " -> " + dummy.getName() + "\n";
        }

        // append all dummy variables as arguments to each rule
        // but rename a variable to its free variable counterpart if it is unbounded in the specified rule
        log += "\nThe rules with the fresh variables were changed to the following:\n\n";
        newRules = new HashSet<>();
        for (IGeneralizedRule r : currentRules) {
            GeneralizedRule oldRule = r.getRule();
            // adapt the current dummy variable list for this specified rule
            boolean adapted = false;
            List<TRSVariable> curDummyVars = new LinkedList<>(dummyVarsMap.values());
            for (TRSVariable curFree : oldRule.getUnboundedVariables()) {
                curDummyVars.set(curDummyVars.indexOf(dummyVarsMap.get(curFree)), curFree);
                adapted = true;
            }
            // extend left hand side
            List<TRSTerm> lhsArgs = new LinkedList<>();
            lhsArgs.addAll(oldRule.getLeft().getArguments());
            lhsArgs.addAll(curDummyVars);
            FunctionSymbol lf = FunctionSymbol.create(r.getLeft().getRootSymbol().getName(), lhsArgs.size());
            TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(lf, lhsArgs);
            // extend right hand side
            List<TRSTerm> rhsArgs = new LinkedList<>();
            rhsArgs.addAll(((TRSFunctionApplication) oldRule.getRight()).getArguments());
            rhsArgs.addAll(curDummyVars);
            FunctionSymbol rf = FunctionSymbol.create(
                                                      ((TRSFunctionApplication) oldRule.getRight()).getRootSymbol()
                                                                                                   .getName(),
                                                      rhsArgs.size());
            TRSFunctionApplication rhs = TRSTerm.createFunctionApplication(rf, rhsArgs);
            IGeneralizedRule newRule = IGeneralizedRule.create(lhs, rhs, r.getCondTerm());
            newRules.add(newRule);
            if (adapted)
                log += newRule.export(new PLAIN_Util()) + "\n";
        }

        // create renaming map: 
        // -> identity map for old vars
        // -> map the dummy variables to the corresponding (previously free) variable
        CollectionMap<String, String> variableRenaming = new CollectionMap<>();
        for (TRSVariable originalVar : allOriginalVars) {
            variableRenaming.add(originalVar.getName(), originalVar.getName());
            if (dummyVarsMap.containsKey(originalVar)) {
                variableRenaming.add(originalVar.getName(), dummyVarsMap.get(originalVar).getName());
            }
        }

        return new Triple<>(newRules, variableRenaming, log);
    }

    /**
     * find a replacement for a certain variable within the given guard
     * 
     * @param current variable we want to find a replacement for
     * @param guard conjunction of (in-)equations
     * @return if present, a term that is equivalent to current
     */
    private Optional<TRSTerm> findReplacementFor(TRSVariable current, TRSCompoundTerm guard) {

        // only continue if term contains the specified variable
        if (!guard.getVariables().contains(current) || guard.isGroundTerm() || guard.isVariable()) {
            return Optional.empty();
        }

        // equation found with specified variable
        if (guard.getRootSymbol().equals(Func.Eq.asFunctionSymbol())) {
            Optional<TRSTerm> repl = correctlyRewriteTerm(current, guard);
            if (repl.isPresent())
                return repl;
        }

        // try for all subterms
        for (int i = 0; i < guard.getArity(); i++) {
            TRSTerm subguard = guard.getArgument(i);
            if (subguard instanceof TRSCompoundTerm) {
                Optional<TRSTerm> repl = findReplacementFor(current, (TRSCompoundTerm) subguard);
                if (repl.isPresent())
                    return repl;
            }
        }

        return Optional.empty();

    }

    /**
     * Rewrite a variable by a term that is specified by the given equation. 
     * Try to the variable on the one side and all other terms on the other side.
     * Note: This function is only able to rewrite certain equation of very simple form, like
     * y = x + 1 => x = y - 1
     * 
     * @param current the variable to which the equation shall be rewritten to.
     * @param equation the given equation for containing the current variable
     * @return an optional term, if present the current variable is equivalent to that term
     */
    private Optional<TRSTerm> correctlyRewriteTerm(TRSVariable current, TRSCompoundTerm equation) {
        TRSTerm left = equation.getArgument(0);
        TRSTerm right = equation.getArgument(1);

        // right side holds the current var
        if (!right.getVariables().contains(current)) {
            TRSTerm temp = right;
            right = left;
            left = temp;
        }

        // only the right side holds the var
        if (left.getVariables().contains(current)) {
            return Optional.empty();
        }

        // rewrite term
        while (right instanceof TRSCompoundTerm
               && ((TRSCompoundTerm) right).getRootSymbol().equals(Func.Add.asFunctionSymbol())) {
            TRSTerm subleft = ((TRSCompoundTerm) right).getArgument(0);
            TRSTerm subright = ((TRSCompoundTerm) right).getArgument(1);

            //System.out.println(equation.export(new PLAIN_Util()));

            // right side holds the current var
            if (!subright.getVariables().contains(current)) {
                TRSTerm temp = subright;
                subright = subleft;
                subleft = temp;
            }

            // only the right side holds the var
            if (subleft.getVariables().contains(current)) {
                return Optional.empty();
            }

            left = TRSTerm.createFunctionApplication(Func.Sub.asFunctionSymbol(), left, subleft);
            right = subright;
        }

        if (right instanceof TRSVariable) {
            return Optional.of(left);
        }

        return Optional.empty();
    }

    private Pair<Set<IGeneralizedRule>, Map<TRSVariable, TRSVariable>>
            renameVariablesInRules(Set<IGeneralizedRule> rules, Set<TRSVariable> variables, String prefix) {
        List<TRSVariable> oldVars = new LinkedList<>(variables);
        List<String> oldNames = new LinkedList<>();
        oldVars.forEach(var -> oldNames.add(var.getName()));
        Map<TRSVariable, TRSVariable> renamingMap = new HashMap<>();
        for (int i = 0, j = 0; i < oldVars.size(); i++, j++) {
            while (oldNames.contains(prefix + j))
                j++;
            TRSVariable var = TRSTerm.createVariable(prefix + j);
            renamingMap.put(oldVars.get(i), var);
        }

        Set<IGeneralizedRule> renamedRules = new HashSet<>();
        rules.forEach(r -> renamedRules.add(r.getWithRenamedVariables(renamingMap)));
        return new Pair<>(renamedRules, renamingMap);
    }

    private final boolean useReplacing;

    /**
     * @param arguments The parameters of this processor.
     */
    @ParamsViaArgumentObject
    public IRSBindFreeVariablesProcessor(IRSBindFreeVariablesProcessor.Arguments arguments) {
        this.useReplacing = arguments.useReplacing;
    }

    public static class Arguments {

        public boolean useReplacing = true;
    }

    public static class IRSBindFreeVariablesProof extends DefaultProof {

        String log;

        public IRSBindFreeVariablesProof(String log) {
            this.shortName = "IRSBindFreeVariables";
            this.longName = "Bind all free variables in the given IRS";
            this.log = log;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return log;
        }
    }

}
