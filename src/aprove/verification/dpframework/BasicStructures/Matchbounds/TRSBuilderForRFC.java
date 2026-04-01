package aprove.verification.dpframework.BasicStructures.Matchbounds;

import java.util.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Matchbounds.TRSBoundsHelper.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class TRSBuilderForRFC {
    private Set<Rule> origLinearizedTRS;
    private Set<Rule> sharpTRS;
    private FunctionSymbol sharp;
    protected FunctionSymbolGenerator funcSymbGen;

    public TRSBuilderForRFC(Set<Rule> origTRS) {
        if (Globals.useAssertions) {
            assert (CollectionUtils.isRightLinear(origTRS));
        }

        this.origLinearizedTRS =  new LinkedHashSet<Rule>();

        for (Rule r : origTRS) {
            TRSFunctionApplication lhs = r.getLeft();
            TRSTerm rhs = r.getRight();
            if (lhs.isLinear()) {
                this.origLinearizedTRS.add(r);
            } else {
                Set<TRSVariable> origVariables = lhs.getVariables();
                Map<TRSVariable, List<Position>> origVarPositions = new LinkedHashMap<TRSVariable, List<Position>>(lhs.getVariablePositions());
                TRSFunctionApplication basicNewLhs = lhs;

                for (TRSVariable x : origVariables) {
                    basicNewLhs = (TRSFunctionApplication) basicNewLhs.linearize(x);
                }

                Set<List<Position>> possibleNewVarPositions = new LinkedHashSet<List<Position>>();
                possibleNewVarPositions.add(new ArrayList<Position>());

                for (Map.Entry<TRSVariable, List<Position>> entry : origVarPositions.entrySet()) {
                    Set<List<Position>> copy = new LinkedHashSet<List<Position>>(possibleNewVarPositions);
                    for (List<Position> varPosList : copy) {
                        possibleNewVarPositions.remove(varPosList);
                        for (Position p : entry.getValue()) {
                            List<Position> newPositions = new ArrayList<Position>(varPosList);
                            newPositions.add(p);
                            possibleNewVarPositions.add(newPositions);
                        }
                    }
                }

                Set<TRSFunctionApplication> newLhss = new LinkedHashSet<TRSFunctionApplication>();
                for (List<Position> newVarPos : possibleNewVarPositions) {
                    int index = 0;
                    TRSFunctionApplication newLhs = basicNewLhs;
                    for (Map.Entry<TRSVariable, List<Position>> entry : origVarPositions.entrySet()) {
                        TRSVariable x = entry.getKey();
                        Position p = newVarPos.get(index);
                        newLhs = (TRSFunctionApplication) newLhs.replaceAt(p, x);
                        index++;
                    }
                    newLhss.add(newLhs);
                }

                for (TRSFunctionApplication newLhs : newLhss) {
                    this.origLinearizedTRS.add(Rule.create(newLhs, rhs));
                }
            }
        }

        this.funcSymbGen = new FunctionSymbolGenerator(CollectionUtils.getFunctionSymbols(origTRS));
        this.sharp = this.funcSymbGen.getFresh("#", 0);
        this.sharpTRS = new LinkedHashSet<Rule>();
        this.sharpTRS.addAll(this.origLinearizedTRS);

    }

    public TRSFunctionApplication getSharpConst() {
        TRSFunctionApplication sharpConst = TRSTerm.createFunctionApplication(this.sharp, new ArrayList<TRSTerm>());
        return sharpConst;
    }

    public Set<Rule> getSharpedTRS(Abortion aborter) throws AbortionException {
        this.createSharpedTRS(aborter);
        return this.sharpTRS;
    }

    private void createSharpedTRS(Abortion aborter) throws AbortionException {
        Set<Rule> toAdd = new LinkedHashSet<>();
        do {
            toAdd.clear();
            // note: initially, sharpTRS contains the (linearized) original rules, see constructor
            for (Rule r : this.sharpTRS) {
                aborter.checkAbortion();
                TRSFunctionApplication lhs = r.getLeft();
                Set<Position> fPositions = new LinkedHashSet<Position>();
                for (Pair<Position, TRSTerm> pair : lhs.getPositionsWithSubTerms()) {
                    if (!pair.getValue().isVariable()) {
                        if (!pair.getKey().isEmptyPosition()) {
                            fPositions.add(pair.getKey());
                        }
                    }
                }

                for (Position p : fPositions) {
                    aborter.checkAbortion();
                    Pair<TRSFunctionApplication, TRSTerm> pair = this.createSharped(lhs, p);
                    TRSFunctionApplication newLhs = pair.getKey();
                    TRSTerm substituted = pair.getValue();
                    Set<TRSVariable> substitutedVariables = substituted.getVariables();
                    Map<TRSVariable, TRSTerm> subs = new LinkedHashMap<TRSVariable, TRSTerm>();
                    for (TRSVariable x : substitutedVariables) {
                        subs.put(x, TRSTerm.createFunctionApplication(this.sharp, new ArrayList<TRSTerm>()));
                    }
                    TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(subs));
                    TRSTerm newRhs = r.getRight().applySubstitution(sigma);
                    Rule newRule = Rule.create(newLhs, newRhs);

                    toAdd.add(newRule);
                }
            }
        } while (sharpTRS.addAll(toAdd));

    }

    private Pair<TRSFunctionApplication, TRSTerm> createSharped(TRSTerm t, Position p) {
        Pair<TRSFunctionApplication, TRSTerm> returnPair;
        if (p.isEmptyPosition()) {
            TRSFunctionApplication newFA = TRSTerm.createFunctionApplication(this.sharp, new ArrayList<TRSTerm>());
            returnPair = new Pair<TRSFunctionApplication, TRSTerm>(newFA, t);
        } else {
            TRSFunctionApplication fA = (TRSFunctionApplication) t; // we don't substitute sharp at a variable position
            int index = 0;
            ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>();
            TRSTerm newT = null;
            for (TRSTerm arg : fA.getArguments()) {
                TRSTerm newArg = arg;
                if (p.firstIndex() == index) {
                    Position posForArg = p.tail(1);
                    Pair<TRSFunctionApplication, TRSTerm> argPair = this.createSharped(arg, posForArg);
                    newArg = argPair.getKey();
                    newT = argPair.getValue();
                }
                newArgs.add(newArg);
                index++;
            }

            TRSFunctionApplication newFA = TRSTerm.createFunctionApplication(fA.getRootSymbol(), newArgs);
            returnPair = new Pair<TRSFunctionApplication, TRSTerm>(newFA, newT);
        }
        return returnPair;
    }
}
