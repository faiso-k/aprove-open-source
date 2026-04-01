package aprove.verification.dpframework.DPProblem.TheoremProver;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Rule;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Logic.Formulas.Equation;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import immutables.*;

/**
 * In this class we receive a right hand side of a DP and we build a formula for
 * the theorem prover in order to delete this DP.
 *
 * @author micpar
 * @version $Id$
 */
public class FormulaCreator {

    private NameManager nameManager;
    private aprove.verification.dpframework.BasicStructures.TRSFunctionApplication myFalse = null;
    private aprove.verification.oldframework.BasicStructures.FunctionSymbol myOr = null;

    public FormulaCreator(NameManager nameManager) {
        this.myFalse = nameManager.getFalseApp();
        this.myOr = nameManager.getOrSym();
        this.nameManager = nameManager;
    }

    private ImmutableList<aprove.verification.dpframework.BasicStructures.TRSTerm> convert(
        ImmutableList<aprove.verification.dpframework.BasicStructures.TRSTerm> dpArguments
    ) {
        List<aprove.verification.dpframework.BasicStructures.TRSTerm> convertedDPArguments =
            new ArrayList<aprove.verification.dpframework.BasicStructures.TRSTerm>();
        for (aprove.verification.dpframework.BasicStructures.TRSTerm input : dpArguments) {
            if (!input.isVariable()) {
                aprove.verification.dpframework.BasicStructures.TRSFunctionApplication funApp =
                    (aprove.verification.dpframework.BasicStructures.TRSFunctionApplication)input;
                if (funApp.getRootSymbol().equals(this.myOr)) {
                    List<aprove.verification.dpframework.BasicStructures.TRSTerm> temp =
                        new ArrayList<aprove.verification.dpframework.BasicStructures.TRSTerm>();
                    if (funApp.getArgument(0).equals(this.myFalse)) {
                        temp.add(funApp.getArgument(1));
                        convertedDPArguments.addAll(ImmutableCreator.create(temp));
                    }
                    else if (funApp.getArgument(1).equals(this.myFalse)) {
                        temp.add(funApp.getArgument(0));
                        convertedDPArguments.addAll(ImmutableCreator.create(temp));
                    }
                    else {
                        convertedDPArguments.addAll(funApp.getArguments());
                    }
                }
                else {
                    convertedDPArguments.add(input);
                }
            }
        }
        return ImmutableCreator.create(convertedDPArguments);
    }

    /**
     * Receives the arguments of the selected DP and creates with them the
     * formula needed by the induction theorem prover
     *
     * @param dpArguments
     * @param prgrm
     * @param R
     * @return Formula, which is the input for the induction theorem prover
     */
    public Formula createFormula(
        ImmutableList<aprove.verification.dpframework.BasicStructures.TRSTerm> dpArguments,
        Program prgrm,
        ImmutableSet<Rule> R,
        SortCalculator sortCalculator,
        boolean unpack,
        boolean removeDups
    ) {

        dpArguments = this.convert(dpArguments);

        Formula frml = null;

        Set<aprove.verification.oldframework.BasicStructures.FunctionSymbol> constrSymbols = this.computeConstrSymbols(R, dpArguments);
        List<AlgebraTerm> arguments = new ArrayList<AlgebraTerm>();

        for (aprove.verification.dpframework.BasicStructures.TRSTerm argument : dpArguments) {
            arguments.add(this.convertNewTermToOldTerm(prgrm, argument, constrSymbols, sortCalculator));
        }

        List<AlgebraVariable> usedVars = new ArrayList<AlgebraVariable>(); // initially no variable has been used
        for (AlgebraTerm arg : arguments) {
            Formula subformula = this.createSubFormula(prgrm, arg, sortCalculator, usedVars, unpack, removeDups);
            if (frml == null) {
                // Create formula "x0 = subArg1 /\ ... /\ xN = subArgN =>
                // arg(x0,...,xN) = true" here if constructor unpacking is
                // enabled, otherwise arg = true
                frml = subformula;
            }
            else {
                // Create formula "x0 = subArg1 /\ ... /\ xN = subArgN =>
                // arg(x0,...,xN) = error \/ ... \/ x0 = subArg1 /\ ... /\ xN =
                // subArgN => arg(x0,...,xN) = true" here if constructor
                // unpacking is enabled, otherwise arg = true
                frml = Or.create(frml, subformula);
            }
        }

        return frml;
    }

    private Formula createSubFormula(Program prgrm, AlgebraTerm arg, SortCalculator sortCalculator,
            List<AlgebraVariable> usedVars, boolean unpack, boolean removeDups) {
        Formula frml = null;
        ConstructorApp myTrue = ConstructorApp.create(prgrm.getPredefined().getTrue());
        // If argument is variable construct formula "x = true"
        if (arg.isVariable() || !unpack) {
            // Create new variable because the maps don't contain old
            // ones and will crash otherwise with a null pointer exception
            frml = Equation.create(arg, myTrue);
        }
        else {
            // Create new function symbol because the maps don't contain old
            // ones and will crash otherwise with a null pointer exception
            aprove.verification.oldframework.BasicStructures.FunctionSymbol funSym =
                aprove.verification.oldframework.BasicStructures.FunctionSymbol.create(
                    arg.getSymbol().getName(),
                    arg.getArguments().size()
                );
            // arg is not a variable, so check if it is constant
            if (arg.isConstant()) {
                // if the constant is already true we can put "TRUE"
                if (arg.equals(myTrue)) {
                    frml = FormulaTruthValue.create(true);
                }
                // otherwise we put "constant = true", we cannot put "FALSE"
                // here, because the constant could be a defined symbol
                else {
                    frml = Equation.create(arg, myTrue);
                }
            }
            // Here we know that arg has arguments itself
            else {
                // Variables occurring in arg cannot be used
                // (and neither can variables that have been generated as
                // "fresh" earlier)
                usedVars.addAll(arg.getVars());
                List<AlgebraTerm> subArgs = this.eliminateDefinedFunctionContext(arg);
                // Create formula "x0 = subArg1 /\ ... /\ xN = subArgN"
                for (AlgebraTerm subArg : subArgs) {
                    // We don't want formulas of the form "x0=otherVar"
                    if (subArg.isVariable()) {
                        continue;
                    }
                    // Create xI = subArgI here
                    AlgebraVariable newVar = this.getFreshVariable(usedVars);
                    String name;
                    if (subArg.isVariable()) {
                        aprove.verification.dpframework.BasicStructures.TRSVariable var =
                            TRSTerm.createVariable(subArg.getSymbol().getName());
                        name = sortCalculator.getVariableSortMap().get(var).getName();
                    }
                    else {
                        funSym =
                            aprove.verification.oldframework.BasicStructures.FunctionSymbol.create(
                                subArg.getSymbol().getName(),
                                subArg.getArguments().size()
                            );
                        name = sortCalculator.getFunOutputSortMap().get(funSym).getName();
                    }
                    newVar.getSymbol().setSort(prgrm.getSort(name));
                    usedVars.add(newVar);
                    // arg = arg.replaceTermByTerm(subArg, newVar);
                    arg = this.replaceFirstOccurence(arg, subArg, newVar);

                    if (frml == null) {
                        frml = Equation.create(newVar, subArg);
                    }
                    else {
                        frml = And.create(frml, Equation.create(newVar, subArg));
                    }
                }
                // Create "x0 = subArg1 /\ ... /\ xN = subArgN => arg(x0,...,xN)
                // = true" here Special case for maxsort especially: frml ==
                // cons(x,xs) or similar
                if (frml != null) {
                    if (removeDups) {
                        Formula temp =
                            this.removeDuplicatesAndInvertUnpackedConstrs(arg, frml, usedVars, myTrue, prgrm);
                        if (temp != null) {
                            frml = temp;
                        }
                        else {
                            frml = Implication.create(frml, Equation.create(arg, myTrue));
                        }
                    }
                    else {
                        frml = Implication.create(frml, Equation.create(arg, myTrue));
                    }
                }
                else {
                    frml = Equation.create(arg, myTrue);
                }
            }
        }
        return frml;
    }

    private Formula removeDuplicatesAndInvertUnpackedConstrs(
        AlgebraTerm mainLeft,
        Formula frml,
        List<AlgebraVariable> usedVars,
        AlgebraTerm myTrue,
        Program prgrm
    ) {
        if (frml == null) {
            return null;
        }
        List<Equation> equations = frml.getAllEquations();
        List<Equation> equationsCopy = new ArrayList<Equation>(frml.getAllEquations());
        List<Equation> tmp = new ArrayList<Equation>();
        for (Equation equation : equationsCopy) {
            if (tmp.contains(equation)) {
                continue;
            }
            if (equation.getLeft().isVariable()) {
                AlgebraVariable leftVar = (AlgebraVariable) equation.getLeft();
                Iterator<Equation> eqIter = equations.iterator();
                while (eqIter.hasNext()) {
                    Equation innerEq = eqIter.next();
                    if (
                        !equation.equals(innerEq)
                        && equation.getRight().equals(innerEq.getRight())
                        && innerEq.getLeft().isVariable()
                    ) {
                        AlgebraVariable innerLeftVar = (AlgebraVariable) innerEq.getLeft();
                        eqIter.remove();
                        tmp.add(innerEq);
                        mainLeft = mainLeft.replaceTermByTerm(innerLeftVar, leftVar);
                    }
                }
            }
        }
        if (equations.isEmpty()) {
            equations = frml.getAllEquations();
        }
        frml = null;
        for (Equation equation : equations) {
            Formula innerfrml = equation;
            AlgebraTerm right = equation.getRight();
            AlgebraTerm left = equation.getLeft();
            boolean proceed = true;
            if (right.isConstructorTerm() && right.getArguments() != null) {
                for (AlgebraTerm rightArg : right.getArguments()) {
                    if (!rightArg.isVariable()) {
                        proceed = false;
                    }
                }
                if (proceed) {
                    List<ConstructorSymbol> conSyms =
                        new ArrayList<ConstructorSymbol>(right.getSort().getConstructorSymbols());
                    conSyms.removeAll(right.getConstructorSymbols());
                    innerfrml = null;
                    for (ConstructorSymbol conSym : conSyms) {
                        List<AlgebraVariable> args = new ArrayList<AlgebraVariable>();
                        for (int index = 0; index < conSym.getArity(); index++) {
                            AlgebraVariable newVar = this.getFreshVariable(usedVars);
                            newVar.getSymbol().setSort(prgrm.getConstructorSymbol(conSym.getName()).getArgSort(index));
                            args.add(newVar);
                            usedVars.addAll(args);
                        }
                        AlgebraTerm newRight = ConstructorApp.create(conSym, args);
                        if (innerfrml == null) {
                            innerfrml = Not.create(Equation.create(left, newRight));
                        }
                        else {
                            innerfrml = And.create(innerfrml, Not.create(Equation.create(left, newRight)));
                        }
                    }
                }
            }
            if (frml != null) {
                frml = And.create(frml, innerfrml);
            }
            else {
                frml = innerfrml;
            }
        }
        if (frml != null) {
            return Implication.create(frml, Equation.create(mainLeft, myTrue));
        }
        else {
            return null;
        }
    }

    private AlgebraTerm replaceFirstOccurence(AlgebraTerm mod, AlgebraTerm search, AlgebraTerm replace) {
        if (mod.equals(search)) {
            return replace;
        }
        if (mod.isVariable()) {
            return mod;
        }
        if (mod instanceof AlgebraFunctionApplication) {
            List<AlgebraTerm> newArgs = new Vector<AlgebraTerm>();
            boolean done = false;
            for (AlgebraTerm arg : mod.getArguments()) {
                AlgebraTerm newTerm = this.replaceFirstOccurence(arg, search, replace);
                if (!newTerm.equals(arg) && !done) {
                    done = true;
                    newArgs.add(newTerm);
                }
                else {
                    newArgs.add(arg);
                }
            }
            return AlgebraFunctionApplication.create((aprove.verification.oldframework.Syntax.SyntacticFunctionSymbol) mod.getSymbol(), newArgs);
        }
        else {
            return mod;
        }
    }

    private List<AlgebraTerm> eliminateDefinedFunctionContext(AlgebraTerm term) {
        List<AlgebraTerm> terms = new ArrayList<AlgebraTerm>();
        // If Variable, we're happy
        if (term.isVariable()) {
            terms.add(term);
            return terms;
        }
        else {
            // Here we have a constructor application, we're happy
            if (term instanceof ConstructorApp) {
                terms.add(term);
            }
            else {
                // Here there is a defined function wrapped around the arguments
                for (AlgebraTerm newTerm : term.getArguments()) {
                    terms.addAll(this.eliminateDefinedFunctionContext(newTerm));
                }
            }
        }
        return terms;
    }

    /*
     * Get fresh variable, avoid variables in the usedVars list
     */
    private AlgebraVariable getFreshVariable(Collection<AlgebraVariable> usedVars) {
        final String PREFIX = "z";
        int varIndex = 0;
        // circumvent nameManager naming facilities just here,
        // those z-names are nice (but check and register the name)
        String nameCand = PREFIX + String.valueOf(varIndex++);
        AlgebraVariable var = AlgebraVariable.create(VariableSymbol.create(nameCand));
        while ((! this.nameManager.isFresh(nameCand)) || usedVars.contains(var)) {
            nameCand = PREFIX + String.valueOf(varIndex++);
            var = AlgebraVariable.create(VariableSymbol.create(nameCand));
        }
        boolean varHithertoFresh = this.nameManager.addUnfreshName(nameCand);
        assert varHithertoFresh;
        return var;
    }

    /*
     * Convert new terms to old terms recursively
     */
    private aprove.verification.oldframework.Algebra.Terms.AlgebraTerm convertNewTermToOldTerm(
        Program prgrm,
        aprove.verification.dpframework.BasicStructures.TRSTerm newTerm,
        Set<aprove.verification.oldframework.BasicStructures.FunctionSymbol> constrSymbols,
        SortCalculator sortCalculator
    ) {
        if (newTerm.isVariable()) {
            if (Globals.useAssertions) {
                if (sortCalculator.getVariableSortMap().get(newTerm) == null) {
                    if (Globals.DEBUG_MICPAR) {
                        System.out.println(newTerm);
                    }
                }
                assert (sortCalculator.getVariableSortMap().get(newTerm) != null);
            }
            VariableSymbol varSym =
                VariableSymbol.create(
                    newTerm.getName(),
                    prgrm.getSort(sortCalculator.getVariableSortMap().get(newTerm).getName())
                );
            return AlgebraVariable.create(varSym);
        }
        else {
            aprove.verification.dpframework.BasicStructures.TRSFunctionApplication funApp =
                ((aprove.verification.dpframework.BasicStructures.TRSFunctionApplication)newTerm);
            if (constrSymbols.contains(funApp.getRootSymbol())) {
                List<AlgebraTerm> args = new Vector<AlgebraTerm>();
                for (aprove.verification.dpframework.BasicStructures.TRSTerm arg : funApp.getArguments()) {
                    args.add(this.convertNewTermToOldTerm(prgrm, arg, constrSymbols, sortCalculator));
                }
                ConstructorSymbol conSym = prgrm.getConstructorSymbol(funApp.getRootSymbol().getName());
                return aprove.verification.oldframework.Algebra.Terms.ConstructorApp.create(conSym, args);
            }
            else {
                List<AlgebraTerm> args = new Vector<AlgebraTerm>();
                for (aprove.verification.dpframework.BasicStructures.TRSTerm arg : funApp.getArguments()) {
                    args.add(this.convertNewTermToOldTerm(prgrm, arg, constrSymbols, sortCalculator));
                }
                DefFunctionSymbol defFunSym = prgrm.getDefFunctionSymbol(funApp.getRootSymbol().getName());
                // Quick-fix for or, because or is in PreDefs
                if (defFunSym == null) {
                    defFunSym = prgrm.getPredefFunctionSymbol(funApp.getRootSymbol().getName());
                }
                return aprove.verification.oldframework.Algebra.Terms.DefFunctionApp.create(defFunSym, args);
            }
        }
    }

    /*
     * Compute constructor symbols
     */
    private Set<aprove.verification.oldframework.BasicStructures.FunctionSymbol> computeConstrSymbols(
        ImmutableSet<aprove.verification.dpframework.BasicStructures.Rule> R,
        ImmutableList<aprove.verification.dpframework.BasicStructures.TRSTerm> dpArguments
    ) {
        Set<aprove.verification.oldframework.BasicStructures.FunctionSymbol> constrSymbols =
            new LinkedHashSet<aprove.verification.oldframework.BasicStructures.FunctionSymbol>();
        RuleAnalysis<Rule> analysis = new RuleAnalysis<Rule>(R, IDPPredefinedMap.EMPTY_MAP);
        ImmutableSet<aprove.verification.oldframework.BasicStructures.FunctionSymbol> allFuns = analysis.getFunctionSymbols();
        ImmutableSet<aprove.verification.oldframework.BasicStructures.FunctionSymbol> defFuns = analysis.getDefinedSymbols();
        // Add new pair to constrSymbols whenever funSym is NOT a
        // defFunctionSymbol
        for (aprove.verification.oldframework.BasicStructures.FunctionSymbol funSym : allFuns) {
            if (!defFuns.contains(funSym)) {
                constrSymbols.add(funSym);
            }
        }
        for (aprove.verification.dpframework.BasicStructures.TRSTerm dpArg : dpArguments) {
            for (aprove.verification.oldframework.BasicStructures.FunctionSymbol funSym : dpArg.getFunctionSymbols()) {
                if (!defFuns.contains(funSym)) {
                    constrSymbols.add(funSym);
                }
            }
        }
        return constrSymbols;
    }

}
