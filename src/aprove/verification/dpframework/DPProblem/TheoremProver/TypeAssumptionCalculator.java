package aprove.verification.dpframework.DPProblem.TheoremProver;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Unification.*;
import aprove.verification.dpframework.DPProblem.Processors.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @author micpar
 * @version $Id$
 */

public class TypeAssumptionCalculator {

    /*
     * attributes
     */
    private TypeAssumption typeAssumption = null;

    // suffix for fresh variables
    private int varIndex = 0;

    /**
     * New empty type assumption is created.
     */
    public TypeAssumptionCalculator() {
        this.typeAssumption = new TypeAssumption();
    }

    /**
     *
     * @return current type assumption
     */
    public TypeAssumption getTypeAssumption() {
        return this.typeAssumption;
    }

    /**
     *
     * @param rules
     * @return Type assumption according to rules
     */
    public TypeAssumption calculateTypeAssumption (ImmutableSet<Rule> rules){
        // Compute initial type assumption
        @SuppressWarnings("unchecked")
        Set<TRSVariable> vars = (Set<TRSVariable>)CollectionUtils.getVariables(rules);
        List<TRSVariable> usedVars = new ArrayList<TRSVariable>(vars);
        for (TRSVariable var : vars){
            List<TRSTerm> inputTypes = new ArrayList<TRSTerm>();
            TRSVariable outputType = (TRSVariable)this.getFreshNewVariables(1, usedVars).get(0);
            usedVars.add(outputType);
            Signature initialSig = new Signature(inputTypes, outputType);
            this.typeAssumption.addSignatureForSymbol(var.getName(), initialSig);
        }

        Set<FunctionSymbol> funSyms = CollectionUtils.getFunctionSymbols(rules);
        for (FunctionSymbol funSym : funSyms){
            List<TRSTerm> inputTypes = new ArrayList<TRSTerm>();
            inputTypes = this.getFreshNewVariables(funSym.getArity(), usedVars);
            for (TRSTerm inputType : inputTypes){
                usedVars.add((TRSVariable)inputType);
            }
            TRSVariable outputType = (TRSVariable)this.getFreshNewVariables(1, usedVars).get(0);
            usedVars.add(outputType);
            Signature initialSig = new Signature(inputTypes, outputType);
            this.typeAssumption.addSignatureForSymbol(funSym.getName(), initialSig);
        }

        // Now compute the real type assumption
        this.refineTypeAssumption(rules);
        return this.typeAssumption;
    }

    /*
     * Collect set of term equations unify them and this is the resulting type assumption
     */

    private void refineTypeAssumption(ImmutableSet<Rule> rules) {
        Set<Pair<TRSTerm, TRSTerm>> unify = new LinkedHashSet<Pair<TRSTerm, TRSTerm>>();
        for (Rule rule : rules) {
            unify.add(new Pair<TRSTerm, TRSTerm>(this.collectEquations(rule.getLeft(), unify), this.collectEquations(rule.getRight(), unify)));
        }
        Unification uni = new Unification(unify);
        this.typeAssumption.applySubstitution(uni.getMgu());
    }

    /*
     * Collect term equations for term
     */
    private TRSTerm collectEquations(TRSTerm t, Set<Pair<TRSTerm, TRSTerm>> unify){
        if (t.isVariable()){
            return this.typeAssumption.getSignatureForSymbol(t.getName()).getOutputType();
        }
        else {
            TRSFunctionApplication funApp = (TRSFunctionApplication) t;
            Signature sig = this.typeAssumption.getSignatureForSymbol(funApp.getRootSymbol().getName());
            List<TRSTerm> inputTypes = sig.getInputTypes();
            Iterator<TRSTerm> typeIter = inputTypes.iterator();
            for (TRSTerm s : funApp.getArguments()){
                TRSTerm typeOfS = this.collectEquations(s, unify);
                unify.add(new Pair<TRSTerm, TRSTerm>(typeOfS, typeIter.next()));
            }
            return this.typeAssumption.getSignatureForSymbol(funApp.getName()).getOutputType();
        }
    }

    /*
     * Get fresh variables, avoid variables in the usedVars list
     */
    private List<TRSTerm> getFreshNewVariables(int arity, List<TRSVariable> usedVars) {
        List<TRSTerm> vars = new ArrayList<TRSTerm>();
        for (int index = 0; index < arity; index++) {
            TRSVariable var = TRSTerm.createVariable(QDPTheoremProverProcessor.SORT_VAR_PREFIX
                    + String.valueOf(this.varIndex++));
            while (usedVars.contains(var)) {
                var = TRSTerm.createVariable(QDPTheoremProverProcessor.SORT_VAR_PREFIX
                        + String.valueOf(this.varIndex++));
            }
            vars.add(var);
        }
        return vars;
    }
}
