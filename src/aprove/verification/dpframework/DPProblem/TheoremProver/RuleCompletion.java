package aprove.verification.dpframework.DPProblem.TheoremProver;

import java.util.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import immutables.*;

/**
 * @author micpar
 * @version $Id$
 */
public class RuleCompletion {

    /*
     * attributes
     */
    private SortCalculator     sortCalculator = null;
    private ImmutableSet<Rule> usableRules    = null;
    private NameManager        nameManager;

    /*
     * constructors
     */

    /**
     * @param R
     *            rule set to be completed
     * @param sortCalculator
     *            List of sorts and function symbols
     */
    private RuleCompletion(ImmutableSet<Rule> usableRules,
            SortCalculator sortCalculator, NameManager nameManager) {
        this.usableRules = usableRules;
        this.sortCalculator = sortCalculator;
        this.nameManager = nameManager;
    }

    /**
     * Create RuleCompletion object and initialize field R.
     *
     * @param R
     * @return new instance of RuleCompletion
     */
    public static RuleCompletion create(
        ImmutableSet<Rule> usableRules,
        SortCalculator sortCalculator,
        NameManager nameManager
    ) {
        return new RuleCompletion(usableRules, sortCalculator, nameManager);
    }

    /**
     * @return true iff R is complete
     */
    public ImmutableSet<Rule> completeRules() {
        RuleAnalysis<Rule> analysis = new RuleAnalysis<Rule>(this.usableRules, IDPPredefinedMap.EMPTY_MAP);
        // Compute CLS set here
        Set<TRSFunctionApplication> comLhs = new LinkedHashSet<TRSFunctionApplication>();
        for (FunctionSymbol defFunSym : analysis.getDefinedSymbols()) {
            ImmutableArrayList<TRSVariable> newVars = this.nameManager.getFreshVariablesImmutable(defFunSym.getArity());
            Iterator<TRSVariable> varIter = newVars.iterator();
            ImmutableList<Sort> sorts = this.sortCalculator.getFunInputSortMap().get(defFunSym);
            if (sorts != null) {
                for (Sort sort : sorts) {
                    this.sortCalculator.addVariableToMap(varIter.next(), sort);
                }
                TRSFunctionApplication fxs = TRSTerm.createFunctionApplication(defFunSym, newVars);
                for (TRSFunctionApplication funApp : this.completeFunction(fxs, analysis.getLeftHandSides(defFunSym))) {
                    comLhs.add(funApp);
                }
            }
        }
        if (comLhs.isEmpty()) {
            return this.usableRules;
        }
        Set<Rule> newRules = new LinkedHashSet<Rule>(this.usableRules);
        for (TRSFunctionApplication funApp : comLhs) {
            newRules.add(
                Rule.create(
                    funApp,
                    TRSTerm.createFunctionApplication(
                        this.sortCalculator.getFunOutputSortMap().get(funApp.getRootSymbol()).getWitnessTerm(),
                        TRSTerm.EMPTY_ARGS
                    )
                )
            );
        }
        return ImmutableCreator.create(newRules);
    }

    /*
     * Compute error_sortN rules and add them to the rule set.
     */
    private Set<TRSFunctionApplication> completeFunction(TRSFunctionApplication fxs, ImmutableSet<TRSFunctionApplication> fLeftHandSides) {
        Set<TRSFunctionApplication> newFLeftHandSides = new LinkedHashSet<TRSFunctionApplication>();
        // First case of algorithm A.
        if (fLeftHandSides.isEmpty()) {
            newFLeftHandSides.add(fxs);
            return ImmutableCreator.create(newFLeftHandSides);
        }

        // Second case of algorithm A
        ImmutableSet<Position> constructorPositions = this.computeConstructorPositions(fxs, fLeftHandSides);
        if (constructorPositions.isEmpty()) {
            return ImmutableCreator.create(newFLeftHandSides);
        }

        // Third and recursive case of algorithm A
        Position minPos = this.getSmallest(constructorPositions);
        for (FunctionSymbol constructor : this.getConstructorsForFunctionAtPosition(fxs, minPos)) {
            TRSFunctionApplication newFxs = TRSTerm.createFunctionApplication(fxs.getRootSymbol(), fxs.getArguments());
            // Get new variables
            ImmutableArrayList<TRSVariable> newVars = this.nameManager.getFreshVariablesImmutable(constructor.getArity());
                //getFreshNewVariables(constructor.getArity(), newFxs);

            // If the constructor has input arguments, give the variables the
            // type of the respective input argument. This is needed later for
            // program initialization
            if (constructor.getArity() > 0) {
                Iterator<TRSVariable> varIter = newVars.iterator();
                for (Sort sort : this.sortCalculator.getFunInputSortMap().get(constructor)) {
                    this.sortCalculator.addVariableToMap(varIter.next(), sort);
                }
            }
            // Replace variable at minimum constructor position according to
            // algorithm
            newFxs = (TRSFunctionApplication) newFxs.replaceAt(minPos, TRSTerm.createFunctionApplication(constructor, newVars));
            Set<TRSFunctionApplication> unifyingFLhs = new LinkedHashSet<TRSFunctionApplication>();
            for (TRSFunctionApplication flhs : fLeftHandSides) {
                if (flhs.unifies(newFxs)) {
                    unifyingFLhs.add(flhs);
                }
            }
            newFLeftHandSides.addAll(this.completeFunction(newFxs, ImmutableCreator.create(unifyingFLhs)));
        }
        return newFLeftHandSides;
    }

    private Position getSmallest(Set<Position> positions) {
        Position minPos = null;
        Position oldMinPos = null;
        do {
            oldMinPos = minPos;
            for (Position pos : positions) {
                if (minPos == null) {
                    oldMinPos = minPos;
                    minPos = pos;
                }
                else if (pos.isPrefixOf(minPos)) {
                    oldMinPos = minPos;
                    minPos = pos;
                }
                else if (pos.isIndependent(minPos)) {
                    int[] posArray = pos.toIntArray();
                    int[] minPosArray = minPos.toIntArray();
                    int minLength = Math.min(posArray.length, minPosArray.length);
                    for (int index = 0; index < minLength; index++) {
                        if (posArray[index] != minPosArray[index]) {
                            if (posArray[index] < minPosArray[index]) {
                                oldMinPos = minPos;
                                minPos = pos;
                            }
                        }
                    }
                }
            }
        }
        while (minPos == null || !minPos.equals(oldMinPos));
        return minPos;
    }

    private ImmutableSet<Position> computeConstructorPositions(TRSFunctionApplication fxs, ImmutableSet<TRSFunctionApplication> fLeftHandSides) {
        Set<Position> constrPos = new LinkedHashSet<Position>();
        Set<Position> positions = fxs.getPositions();
        for (Position position : positions) {
            for (TRSFunctionApplication lhs : fLeftHandSides) {
                TRSTerm lhsSubterm = lhs.getSubtermOrNull(position);
                // At this point we can be sure that the position is contained
                // in the positions of fxs
                TRSTerm fxsSubterm = fxs.getSubterm(position);
                // fxs must be a variable at this point and lhs must be a
                // constructor symbol of the right sort, otherwise we don't want
                // this position for
                // our algorithm A
                if (fxsSubterm.isVariable() && lhsSubterm != null && !lhsSubterm.isVariable()
                        && this.getConstructorsForFunctionAtPosition(fxs, position).contains(((TRSFunctionApplication) lhsSubterm).getRootSymbol())) {
                    constrPos.add(position);
                }
            }
        }
        return ImmutableCreator.create(constrPos);
    }

    /*
     * This method is intended to return the constructors of the sort which
     * belongs to the position in this particular function application
     */
    private ImmutableSet<FunctionSymbol> getConstructorsForFunctionAtPosition(TRSFunctionApplication funApp, Position pos) {
        // Get function application right above the position
        TRSTerm subTerm = funApp.getSubterm(pos.shorten(1));
        // If it is a variable bail out. Should not happen.
        if (Globals.useAssertions) {
            assert (!subTerm.isVariable());
        }
        // Get function symbol right above the position
        FunctionSymbol rootSym = ((TRSFunctionApplication) subTerm).getRootSymbol();
        // Return constructors of sort found at argument in this function symbol
        return this.sortCalculator.getFunInputSortMap().get(rootSym).get(pos.lastIndex()).getConstructors();
    }
}
