package aprove.input.Programs.newTrs;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;

/**
 * Helper class for creating ETRS problems in {@link ObligationCreator}
 */
class OblCreatorEtrs {

    public static Set<FunctionSymbol> buildSymColl(Collection<String> symNames) {
        final Set<FunctionSymbol> funcSymbColl = new LinkedHashSet<FunctionSymbol>();
        for (final String stringFuncSymb : symNames) {
            funcSymbColl.add(FunctionSymbol.create(stringFuncSymb, 2));
        }
        return funcSymbColl;
    }

    /**
     * This method increments the set of Equations by commutative equations.
     * For each function symbols in the given Collection funcSymbols the commutative equation is added,
     * if it is not already present in the set of Equations.
     * @param funcSymbols The function symbols for which the commutative equation should be created.
     * @param allFuncSymbs Necessary to avoid name conflicts with already defined function symbols of the TRS.
     * @return the extended set of Equations.
     */
    public static Set<Equation> getCommutativeEquations(
            final Collection<FunctionSymbol> funcSymbols,
            final Collection<FunctionSymbol> allFuncSymbs) {
        final Set<Equation> returnSet = new LinkedHashSet<Equation>();
        final FreshNameGenerator freshNameGen = new FreshNameGenerator(
                allFuncSymbs, FreshNameGenerator.VARIABLES);
        final TRSVariable x = TRSTerm.createVariable(freshNameGen.getFreshName(
                "x", true));
        final TRSVariable y = TRSTerm.createVariable(freshNameGen.getFreshName(
                "y", true));

        for (final FunctionSymbol funcSymb : funcSymbols) {
            final TRSTerm l = TRSTerm.createFunctionApplication(funcSymb, Equation
                    .createArgArrayList(Arrays.asList(x, y)));
            final TRSTerm r = TRSTerm.createFunctionApplication(funcSymb, Equation
                    .createArgArrayList(Arrays.asList(y, x)));
            returnSet.add(Equation.create(l, r));
        }
        return returnSet;
    }

    /**
     * This method increments the set of Equations by associative equations.
     * For each function symbols in the given Collection funcSymbols the associative equation is added,
     * if it is not already present in the set of Equations.
     * @param funcSymbols The function symbols for which the associative equations should be created.
     * @param allFuncSymbs Necessary to avoid name conflicts with already defined function symbols of the TRS.
     * @return the extended set of Equations.
     */
    public static Set<Equation> getAssociativeEquations(
            final Collection<FunctionSymbol> funcSymbols,
            final Collection<FunctionSymbol> allFuncSymbs) {
        final Set<Equation> returnSet = new LinkedHashSet<Equation>();
        final FreshNameGenerator freshNameGen = new FreshNameGenerator(
                allFuncSymbs, FreshNameGenerator.VARIABLES);
        final TRSVariable x = TRSTerm.createVariable(freshNameGen.getFreshName(
                "x", true));
        final TRSVariable y = TRSTerm.createVariable(freshNameGen.getFreshName(
                "y", true));
        final TRSVariable z = TRSTerm.createVariable(freshNameGen.getFreshName(
                "z", true));

        for (final FunctionSymbol funcSymb : funcSymbols) {
            final TRSTerm l = TRSTerm.createFunctionApplication(funcSymb, Equation
                    .createArgArrayList(Arrays.asList(TRSTerm
                            .createFunctionApplication(funcSymb, Equation
                                    .createArgArrayList(Arrays.asList(x, y))),
                            z)));
            final TRSTerm r = TRSTerm
                    .createFunctionApplication(funcSymb, Equation
                            .createArgArrayList(Arrays.asList(x, TRSTerm
                                    .createFunctionApplication(funcSymb,
                                            Equation.createArgArrayList(Arrays
                                                    .asList(y, z))))));
            returnSet.add(Equation.create(l, r));
        }
        return returnSet;
    }


}
