package aprove.input.Programs.loat;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * This processor takes a IRSProblem as obligation. It transforms it to an KoatProblem
 * Since the koat format for ITSs is very close the implementation of ITSs of AProVE. 
 * The only thing needed to guarantee is proper names for variables since some symbols are not allowed.
 * Thus, this processor renames all variables to k0, k1,... and determines the start symbol.
 * 
 * @author Constantin Mensendiek
 */
public class IRSToKoatProcessor extends Processor.ProcessorSkeleton {

    @Override
    public Result process(BasicObligation obl,
                          BasicObligationNode oblNode,
                          Abortion aborter,
                          RuntimeInformation rti) throws AbortionException {
        assert !Globals.useAssertions || obl instanceof IRSProblem;

        IRSProblem problem = (IRSProblem) obl;

        // rename all variables
        Set<TRSVariable> allVariables = new HashSet<>();
        problem.getRules().forEach(r -> allVariables.addAll(r.getVariables()));
        Pair<Set<IGeneralizedRule>, Map<TRSVariable, TRSVariable>> renaming = renameVariablesInRules(problem.getRules(),
                                                                                                     allVariables,
                                                                                                     "k");
        CollectionMap<String,String> varMap = new CollectionMap<>();
        for(TRSVariable key : renaming.y.keySet()) {
            varMap.add(key.getName(), Collections.singleton(renaming.y.get(key).getName()));
        }

        TRSFunctionApplication start = determineStartFunctionSymbol(problem);

        KoatProblem newProblem = new KoatProblem(ImmutableCreator.create(renaming.x),
                                                 start,
                                                 varMap,
                                                 problem);
        return ResultFactory.provedAnd(Collections.singletonList(newProblem),
                                       YNMImplication.EQUIVALENT,
                                       new IRSToKoatProof());

    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof IRSProblem;
    }

    /**
     * Simple function to rename all rules with a with the same variable substitution.
     * This ensures that previously same variables stay the same even if in different rules.
     * 
     * @param rules all rules whose variables are to be renamed
     * @param variables all variables to be renamed
     * @param prefix the prefix for the new variables
     * @return 1. the renamed rules, 2. a renaming map
     */
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

    /**
     * determine the start function symbol of the given ITS
     * 
     * @param problem the ITS
     * @return the start function symbol
     */
    private TRSFunctionApplication determineStartFunctionSymbol(IRSProblem problem) {
        TRSFunctionApplication startTerm = problem.getStartTerm();
        if (startTerm.getArity() != 0) {
            FunctionSymbol f = startTerm.getFunctionSymbol();
            FunctionSymbol f_ = FunctionSymbol.create(f.getName(), 0);
            startTerm = TRSTerm.createFunctionApplication(f_);
        }
        return startTerm;
    }

    public static class IRSToKoatProof extends DefaultProof {

        public IRSToKoatProof() {
            this.shortName = "IRSToKoat";
            this.longName = "Convert an IRS to a koat problem";
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "Convert an IRS to a koat problem";
        }
    }

}
