package aprove.verification.theoremprover.TheoremProverProcedures;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.TheoremProverProblem.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.TheoremProverProofs.*;

@NoParams
public class CaseAnalysisProcessor extends TheoremProverProcessor {

    @Override
    protected Result process(final TheoremProverObligation obligationInput,
        final BasicObligationNode obligationNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException {

        final Formula formula = obligationInput.getFormula();

        // caculate candidate variables for case analysis
        final Set<VariableSymbol> candidates = new LinkedHashSet<>();
        for (final Pair<Formula, Set<VariableSymbol>> hypothesis : obligationInput.getHypothesesAsSet()) {
            candidates.addAll(hypothesis.y);
        }
        candidates.retainAll(formula.getAllVariableSymbols());

        if (candidates.isEmpty() || obligationInput.getHypotheses().isEmpty()) {
            return ResultFactory.notApplicable();
        }

        Set<TheoremProverObligation> newObligations = new LinkedHashSet<>();

        for (final VariableSymbol candidate : candidates) {

            if (IfHeuristicVisitor.apply(formula, candidate, obligationInput.getProgram())) {
                continue;
            }

            newObligations = new LinkedHashSet<>();

            for (final ConstructorSymbol constructorSymbol : candidate.getSort().getConstructorSymbols()) {

                final AlgebraSubstitution substitution = AlgebraSubstitution.create();
                substitution.put(
                    candidate,
                    AlgebraFunctionApplication.createWithDisjointVars(constructorSymbol,
                        new FreshVarGenerator(obligationInput.getAllVariables())));

                final Formula newFormula = formula.apply(substitution);
                newObligations.add(new TheoremProverObligation(newFormula, obligationInput));
            }

            if (!newObligations.isEmpty()) {
                return ResultFactory.provedAnd(newObligations, YNMImplication.EQUIVALENT, new CaseAnalysisProof(
                    newObligations));
            }

        }

        return ResultFactory.notApplicable();
    }

}

class IfHeuristicVisitor implements CoarseFormulaVisitor<Boolean>, CoarseGrainedTermVisitor<Boolean> {

    protected Symbol symbol;
    protected Program program;
    protected int ifBranch;

    public static boolean apply(final Formula formula, final Symbol symbol, final Program program) {
        return formula.apply(new IfHeuristicVisitor(symbol, program));
    }

    protected IfHeuristicVisitor(final Symbol symbol, final Program program) {
        this.symbol = symbol;
        this.program = program;
        this.ifBranch = 0;
    }

    @Override
    public Boolean caseEquation(final Equation eqFormula) {
        return eqFormula.getLeft().apply(this) || eqFormula.getRight().apply(this);
    }

    @Override
    public Boolean caseJunctorFormula(final JunctorFormula jFormula) {
        return (jFormula.getRight() == null) ? jFormula.getLeft().apply(this)
            : (jFormula.getLeft().apply(this) || jFormula.getRight().apply(this));
    }

    @Override
    public Boolean caseTruthValue(final FormulaTruthValue truthvalFormula) {
        return false;
    }

    @Override
    public Boolean caseFunctionApp(final AlgebraFunctionApplication f) {
        boolean returnValue;

        if (f.getSymbol().getName().startsWith("if_")
            && (this.program.getPredefFunctionSymbol(f.getFunctionSymbol().getName()) != null)) {
            this.ifBranch++;
            returnValue =
                (!f.getArgument(0).apply(this)) && (f.getArgument(1).apply(this) || f.getArgument(2).apply(this));
            this.ifBranch--;
            return returnValue;
        } else {
            returnValue = false;
            for (final AlgebraTerm argument : f.getArguments()) {
                returnValue = returnValue || argument.apply(this);
            }
            return returnValue;
        }

    }

    @Override
    public Boolean caseVariable(final AlgebraVariable v) {
        return (this.ifBranch != 0) && v.getSymbol().equals(this.symbol);
    }

}
