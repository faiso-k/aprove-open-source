package aprove.verification.oldframework.IRSwT;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Bytecode.Processors.ToIDPv1.*;
import aprove.verification.oldframework.IRSwT.IRSwTFormatTransformer.RoundingBehaviour.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * Transforms all constructs which are not allowed in IRSs into equivalent constructs which are allowed in IRSs.
 * @author unknown, Marc Brockschmidt, cryingshadow
 * @version $Id$
 */
public class IRSwTFormatTransformer extends Processor.ProcessorSkeleton {

    /**
     * Describes how numbers should be rounded in division and modulo operations
     * @author Alex Hoppen
     */
    public static enum RoundingBehaviour {
        /**
         * It is unknown if numbers are rounded up or down
         * 
         * 0.2 could be rounded to both 0 and 1
         */
        UNKNOWN {
            /**
             * Transforms z = x / y to
             * <ul> 
             *   <li>x - y * z > -y
             *   <li>x - y * z <  y
             * </ul>
             */
            @Override 
            DivModResolvingResult divModEquivalent(TRSTerm x, TRSTerm y, FreshNameGenerator freshNameGen, IDPPredefinedMap predefinedMap) {
                Set<TRSTerm> conds = new LinkedHashSet<>();
                
                final TRSTerm z = TRSTerm.createVariable(freshNameGen.getFreshName("div", false));
                final FunctionSymbol lt = predefinedMap.getSym(Func.Lt, DomainFactory.INTEGER_INTEGER);
                final FunctionSymbol gt = predefinedMap.getSym(Func.Gt, DomainFactory.INTEGER_INTEGER);
                final FunctionSymbol sub = predefinedMap.getSym(Func.Sub, DomainFactory.INTEGER_INTEGER);
                final FunctionSymbol add = predefinedMap.getSym(Func.Add, DomainFactory.INTEGER_INTEGER);
                final FunctionSymbol mul = predefinedMap.getSym(Func.Mul, DomainFactory.INTEGER_INTEGER);
                
                // rem = x - y * z
                final TRSTerm rem = TRSTerm.createFunctionApplication(sub, x, TRSTerm.createFunctionApplication(mul, y, z));
                
                // x - y * z + y > 0 equivalent to x - y * z > -y 
                final TRSFunctionApplication lowerBound =
                    TRSTerm.createFunctionApplication(
                        gt,
                        TRSTerm.createFunctionApplication(add, rem, y),
                        predefinedMap.getIntTerm(BigIntImmutable.ZERO, DomainFactory.INTEGERS)
                    );
                
                // x - y * z <  y
                final TRSFunctionApplication upperBound = TRSTerm.createFunctionApplication(lt, rem, y);
                
                conds.add(lowerBound);
                conds.add(upperBound);
                
                return new DivModResolvingResult(z, rem, conds);
            }
        },
        /** 
         * Numbers are rounded towards 0
         * 
         * 1.7 is rounded to 1 and -3.2 to -3. 
         * 
         * This is the default rounding behaviour in C
         */
        TOWARDS_ZERO {
            /**
             * Concatenates the given terms with the binary function symbol, e.g. if funcSymb is &&
             * ((a && b) && c) && d ...
             */
            private TRSTerm applyFunctionSymbol(FunctionSymbol funcSym, TRSTerm... terms) {
                if (Globals.useAssertions) {
                    assert terms.length > 0;
                    assert funcSym.getArity() == 2;
                }
                TRSTerm intermediate = null;
                for (TRSTerm term : terms) {
                    if (intermediate == null) {
                        intermediate = term;
                    } else {
                        intermediate = TRSTerm.createFunctionApplication(funcSym, intermediate, term);
                    }
                }
                return intermediate;
            }
            
            @Override
            DivModResolvingResult divModEquivalent(TRSTerm x, TRSTerm y, FreshNameGenerator freshNameGen, IDPPredefinedMap predefinedMap) {
                final TRSTerm z = TRSTerm.createVariable(freshNameGen.getFreshName("div", false));
                final FunctionSymbol lt = predefinedMap.getSym(Func.Lt, DomainFactory.INTEGER_INTEGER);
                final FunctionSymbol gt = predefinedMap.getSym(Func.Gt, DomainFactory.INTEGER_INTEGER);
                final FunctionSymbol le = predefinedMap.getSym(Func.Le, DomainFactory.INTEGER_INTEGER);
                final FunctionSymbol ge = predefinedMap.getSym(Func.Ge, DomainFactory.INTEGER_INTEGER);
                final FunctionSymbol sub = predefinedMap.getSym(Func.Sub, DomainFactory.INTEGER_INTEGER);
                final FunctionSymbol add = predefinedMap.getSym(Func.Add, DomainFactory.INTEGER_INTEGER);
                final FunctionSymbol mul = predefinedMap.getSym(Func.Mul, DomainFactory.INTEGER_INTEGER);
                final FunctionSymbol and = predefinedMap.getSym(Func.Land, DomainFactory.BOOLEAN_BOOLEAN);
                final FunctionSymbol or = predefinedMap.getSym(Func.Lor, DomainFactory.BOOLEAN_BOOLEAN);
                final TRSTerm zero = predefinedMap.getIntTerm(BigIntImmutable.ZERO, DomainFactory.INTEGERS);
                
                // rem = x - y * z
                final TRSTerm rem = TRSTerm.createFunctionApplication(sub, x, TRSTerm.createFunctionApplication(mul, y, z));
                
                TRSTerm xPos = TRSTerm.createFunctionApplication(ge, x, zero);
                TRSTerm xNeg = TRSTerm.createFunctionApplication(lt, x, zero);
                TRSTerm yPos = TRSTerm.createFunctionApplication(ge, y, zero);
                TRSTerm yNeg = TRSTerm.createFunctionApplication(lt, y, zero);
                
                TRSTerm xPosYPos;
                TRSTerm xPosYNeg;
                TRSTerm xNegYPos;
                TRSTerm xNegYNeg;
                // Handle case: x >= 0, y >= 0
                {
                    // x - y * z >= 0 
                    final TRSFunctionApplication lowerBound = TRSTerm.createFunctionApplication(ge, rem, zero);
                    // x - y * z -y < 0  equivalent to x - y * z < y
                    final TRSTerm remMinusY = TRSTerm.createFunctionApplication(sub, rem, y);
                    final TRSFunctionApplication upperBound = TRSTerm.createFunctionApplication(lt, remMinusY, zero);
                    
                    xPosYPos = applyFunctionSymbol(and, xPos, yPos, lowerBound, upperBound);
                }
                // Handle case: x >= 0, y < 0
                {
                    // x - y * z >= 0 
                    final TRSFunctionApplication lowerBound = TRSTerm.createFunctionApplication(ge, rem, zero);
                    // x - y * z + y < 0  equivalent to  x - y * z < -y
                    final TRSTerm remPlusY = TRSTerm.createFunctionApplication(add, rem, y);
                    final TRSFunctionApplication upperBound = TRSTerm.createFunctionApplication(lt, remPlusY, zero);
                    
                    xPosYNeg = applyFunctionSymbol(and, xPos, yNeg, lowerBound, upperBound);
                }
                // Handle case: x < 0, y >= 0
                {
                    // x - y * z <= 0 
                    final TRSFunctionApplication upperBound = TRSTerm.createFunctionApplication(le, rem, zero);
                    // x - y * z + y > 0  equivalent to  x - y * z > -y
                    final TRSTerm remPlusY = TRSTerm.createFunctionApplication(add, rem, y);
                    final TRSFunctionApplication lowerBound = TRSTerm.createFunctionApplication(gt, remPlusY, zero);
                    
                    xNegYPos = applyFunctionSymbol(and, xNeg, yPos, lowerBound, upperBound);
                }
                // Handle case: x < 0, y < 0
                {
                    // x - y * z <= 0 
                    final TRSFunctionApplication upperBound = TRSTerm.createFunctionApplication(le, rem, zero);
                    // x - y * z - y > 0  equivalent to x - y * z > y
                    final TRSTerm remMinusY = TRSTerm.createFunctionApplication(sub, rem, y);
                    final TRSFunctionApplication lowerBound = TRSTerm.createFunctionApplication(gt, remMinusY, zero);
                    
                    xNegYNeg = applyFunctionSymbol(and, xNeg, yNeg, lowerBound, upperBound);
                }
                
                TRSTerm finalTerm = applyFunctionSymbol(or, xPosYPos, xPosYNeg, xNegYPos, xNegYNeg);
                
                return new DivModResolvingResult(z, rem, Collections.singleton(finalTerm));
            }
        };
        
        static class DivModResolvingResult extends ImmutableTriple<TRSTerm, TRSTerm, Set<TRSTerm>> {
            DivModResolvingResult(TRSTerm div, TRSTerm rem, Set<TRSTerm> conds) {
                super(div, rem, conds);
            }
            
            TRSTerm getDiv() {
                return x;
            }
            
            TRSTerm getRem() {
                return y;
            }
            
            Set<TRSTerm> getConds() {
                return z;
            }
        }
        
        /**
         * Creates a term that is equivalent to the division relation z = x/y where the remainder
         * is rem without using the division operator
         * 
         * @param dividend The number that should be divided
         * @param divisor The number to divide the dividend by
         * @param quotient The result of the division
         * @return A set of conditions whose conjunction is equivalent to the division operation
         */
        abstract DivModResolvingResult divModEquivalent(TRSTerm x, TRSTerm y, FreshNameGenerator freshNameGen, IDPPredefinedMap predefinedMap);
    }

    public static class Args {
        public boolean linearizeLhss = false;
        public boolean removeDivAndMod = true;
    }

    private Args args;

    @ParamsViaArgumentObject
    public IRSwTFormatTransformer(Args args) {
        this.args = args;
    }

    /**
     * @param f Some function application.
     * @param predefinedMap The predefined symbols.
     * @return An equivalent function application where all FALSE constants have been transformed away or null if the
     *         function application is equivalent to FALSE.
     */
    public static TRSTerm killFALSE(TRSFunctionApplication f, IDPPredefinedMap predefinedMap) {
        FunctionSymbol sym = f.getRootSymbol();
        if (sym.getName().equals("FALSE") && sym.getArity() == 0) {
            return null;
        } else if (predefinedMap.isLand(sym)) {
            TRSTerm left = f.getArgument(0);
            TRSTerm right = f.getArgument(1);
            final TRSTerm newLeft;
            final TRSTerm newRight;
            if (left.isVariable()) {
                newLeft = left;
            } else {
                newLeft = IRSwTFormatTransformer.killFALSE((TRSFunctionApplication)left, predefinedMap);
            }
            if (newLeft == null) {
                return null;
            }
            if (right.isVariable()) {
                newRight = right;
            } else {
                newRight = IRSwTFormatTransformer.killFALSE((TRSFunctionApplication)right, predefinedMap);
            }
            if (newRight == null) {
                return null;
            } else {
                return
                    TRSTerm.createFunctionApplication(
                        predefinedMap.getSym(Func.Land, DomainFactory.BOOLEAN_BOOLEAN),
                        newLeft,
                        newRight
                    );
            }
        } else if (predefinedMap.isLor(sym)) {
            TRSTerm left = f.getArgument(0);
            TRSTerm right = f.getArgument(1);
            final TRSTerm newLeft;
            final TRSTerm newRight;
            if (left.isVariable()) {
                newLeft = left;
            } else {
                newLeft = IRSwTFormatTransformer.killFALSE((TRSFunctionApplication)left, predefinedMap);
            }
            if (right.isVariable()) {
                newRight = right;
            } else {
                newRight = IRSwTFormatTransformer.killFALSE((TRSFunctionApplication)right, predefinedMap);
            }
            if (newLeft == null) {
                if (newRight == null) {
                    return null;
                } else {
                    return newRight;
                }
            } else if (newRight == null) {
                return newLeft;
            } else {
                return
                    TRSTerm.createFunctionApplication(
                        predefinedMap.getSym(Func.Lor, DomainFactory.BOOLEAN_BOOLEAN),
                        newLeft,
                        newRight
                    );
            }
        }
        ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
        for (TRSTerm arg : f.getArguments()) {
            if (arg.isVariable()) {
                args.add(arg);
            } else {
                TRSTerm killed = IRSwTFormatTransformer.killFALSE((TRSFunctionApplication)arg, predefinedMap);
                if (killed == null) {
                    throw new IllegalArgumentException("FALSE occurred in weird context!");
                }
                args.add(killed);
            }
        }
        return TRSTerm.createFunctionApplication(sym, args);
    }

    /**
     * @param condFA some function application used as condition
     * @param predefinedMap the predefined map
     * @return a function application in which "x != y" has been replaced by "x < y || x > y"
     */
    public static TRSFunctionApplication killNE(TRSFunctionApplication condFA, IDPPredefinedMap predefinedMap) {
        TRSFunctionApplication resFA = condFA;
        for (Pair<Position, TRSTerm> p : resFA.getPositionsWithSubTerms()) {
            final Position position = p.x;
            final TRSTerm subterm = p.y;
            if (subterm instanceof TRSFunctionApplication) {
                final TRSFunctionApplication fa = (TRSFunctionApplication)subterm;
                final FunctionSymbol fs = fa.getRootSymbol();
                if (predefinedMap.isLnot(fs)) {
                    //Check its only argument:
                    final TRSTerm argTerm = fa.getArgument(0);
                    if (!argTerm.isVariable() && predefinedMap.isEq(((TRSFunctionApplication)argTerm).getRootSymbol())) {
                        final TRSFunctionApplication argFa = (TRSFunctionApplication)argTerm;
                        resFA =
                            (TRSFunctionApplication)
                                resFA.replaceAt(
                                    position,
                                    IRSwTFormatTransformer.ltOrGt(
                                        argFa.getArgument(0),
                                        argFa.getArgument(1),
                                        predefinedMap
                                    )
                                );
                    } else {
                        assert (false) : "Usage of logical not in weird context in rule\n" + resFA;
                    }
                } else if (predefinedMap.isNeq(fs)) {
                    resFA =
                        (TRSFunctionApplication)
                            resFA.replaceAt(
                                position,
                                IRSwTFormatTransformer.ltOrGt(fa.getArgument(0), fa.getArgument(1), predefinedMap)
                            );
                }
            }
        }
        return resFA;
    }

    /**
     * @param condFA Some function application.
     * @param predefinedMap The predefined symbols.
     * @return An equivalent function application where each negation has been moved inside to the literals (i.e.,
     *         except for the symbol '!=', no negation occurs anymore in the resulting function application).
     */
    public static TRSTerm killNOT(TRSFunctionApplication condFA, IDPPredefinedMap predefinedMap) {
        FunctionSymbol sym = condFA.getRootSymbol();
        if (predefinedMap.isLnot(sym)) {
            TRSTerm arg = condFA.getArgument(0);
            if (arg.isVariable()) {
                throw new IllegalArgumentException("Negation of variable occurred!");
            }
            TRSTerm negated = IRSwTFormatTransformer.negate((TRSFunctionApplication)arg, predefinedMap);
            if (negated.isVariable()) {
                return negated;
            }
            return IRSwTFormatTransformer.killNOT((TRSFunctionApplication)negated, predefinedMap);
        }
        ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
        for (TRSTerm arg : condFA.getArguments()) {
            if (arg.isVariable()) {
                args.add(arg);
            } else {
                args.add(IRSwTFormatTransformer.killNOT((TRSFunctionApplication)arg, predefinedMap));
            }
        }
        return TRSTerm.createFunctionApplication(sym, args);
    }

    /**
     * @param condFA some function application used as condition
     * @param predefinedMap the predefined map
     * @return a set of terms, which, viewed as disjunction, are equivalent to the original term (obtained by removing
     * nested ORs)
     */
    public static Set<TRSTerm> killOR(TRSTerm condFA, IDPPredefinedMap predefinedMap) {
        final LinkedList<TRSTerm> todo = new LinkedList<TRSTerm>();
        todo.push(condFA);
        final Set<TRSTerm> res = new LinkedHashSet<TRSTerm>();
        TODO: while (!todo.isEmpty()) {
            final TRSTerm t = todo.pop();
            //Variables are stooopid:
            if (t.isVariable()) {
                res.add(t);
                continue;
            }
            final TRSFunctionApplication tFA = (TRSFunctionApplication)t;
            //Search for an OR somewhere on the inside, propagate it out:
            for (Pair<Position, TRSTerm> p : tFA.getPositionsWithSubTerms()) {
                final Position curPos = p.x;
                final TRSTerm curSubterm = p.y;
                if (curSubterm.isVariable()) {
                    continue;
                }
                //If we have an OR somewhere, split:
                final TRSFunctionApplication curFa = (TRSFunctionApplication)curSubterm;
                final FunctionSymbol curFs = curFa.getRootSymbol();
                if (predefinedMap.isLor(curFs)) {
                    //Replace or by the two arguments:
                    final TRSTerm leftArg = curFa.getArgument(0);
                    final TRSTerm rightArg = curFa.getArgument(1);
                    todo.add(t.replaceAt(curPos, leftArg));
                    todo.add(t.replaceAt(curPos, rightArg));
                    continue TODO;
                }
            }
            //Nothing was done, so put into res:
            res.add(t);
        }
        return res;
    }

    /**
     * @param rules some rules
     * @param predefinedMap the map of predefined symbols
     * @return new rules where all rules with non-linear left hand sides have
     *  been replaced by rules where the lhs is linear and conditions ensure
     *  that the variables have the same value.
     */
    public static Set<IGeneralizedRule> makeLhsLinear(
        Set<IGeneralizedRule> rules,
        IDPPredefinedMap predefinedMap
    ) {
        final LinkedHashSet<IGeneralizedRule> res = new LinkedHashSet<IGeneralizedRule>();
        for (IGeneralizedRule rule : rules) {
            final TRSFunctionApplication lhs = rule.getLeft();
            TRSTerm cond = rule.getCondTerm();
            final LinkedHashSet<TRSTerm> seenVars = new LinkedHashSet<>();
            final ArrayList<TRSTerm> newArgs = new ArrayList<>();
            final FreshNameGenerator fne = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
            fne.lockHasNames(rule.getVariables());
            if (cond != null) {
                fne.lockHasNames(cond.getVariables());
            }
            for (TRSTerm arg : lhs.getArguments()) {
                if (arg instanceof TRSFunctionApplication) {
                    if (!IDPPredefinedMap.DEFAULT_MAP.isPredefined(((TRSFunctionApplication)arg).getRootSymbol())) {
                        seenVars.addAll(arg.getVariables());
                    }
                }
            }
            for (TRSTerm arg : lhs.getArguments()) {
                if (arg.isVariable() && seenVars.add(arg)) {
                    newArgs.add(arg);
                } else {
                    if (arg instanceof TRSFunctionApplication) {
                        final TRSFunctionApplication f = (TRSFunctionApplication)arg;
                        if (!IDPPredefinedMap.DEFAULT_MAP.isPredefined(f.getRootSymbol())) {
                            newArgs.add(arg);
                            continue;
                        }
                    }
                    final TRSVariable newVar;
                    if (arg.isVariable()) {
                        newVar = TRSTerm.createVariable(fne.getFreshName(arg.getName(), false));
                    } else {
                        newVar = TRSTerm.createVariable(fne.getFreshName("c" + arg.getName().replace('-', 'm'), false));
                    }
                    final FunctionSymbol eq = predefinedMap.getSym(Func.Eq, DomainFactory.INTEGER_INTEGER);
                    final TRSFunctionApplication eqTerm = TRSTerm.createFunctionApplication(eq, arg, newVar);
                    cond = IDPv2ToIDPv1Utilities.getConjunction(cond, eqTerm);
                    newArgs.add(newVar);
                }
            }
            res.add(
                IGeneralizedRule.create(
                    TRSTerm.createFunctionApplication(lhs.getRootSymbol(), newArgs),
                    rule.getRight(),
                    cond
                )
            );
        }
        return res;
    }

    /**
     * @param rule some rule
     * @param predefinedMap the predefined map
     * @return a new rule in which all occurrences of arithmetic operations on the rhs have been replaced by fresh vars
     * which are bound by corresponding equalities in the conditions.
     */
    public static IGeneralizedRule moveArithmeticToConstrains(
        IGeneralizedRule rule,
        IDPPredefinedMap predefinedMap
    ) {
        final TRSFunctionApplication left = rule.getLeft();
        final TRSTerm right = rule.getRight();
        final TRSTerm oldConstraints = rule.getCondTerm();
        TRSTerm newRight = right;
        TRSTerm newConstraints = oldConstraints;
        final FreshNameGenerator fne = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        for (TRSVariable var : rule.getVariables()) {
            fne.lockName(var.getName());
        }
        for (TRSVariable var : rule.getCondVariables()) {
            fne.lockName(var.getName());
        }
        final Map<TRSTerm, TRSVariable> termToFreshVarMap = new LinkedHashMap<TRSTerm, TRSVariable>();
        final Queue<Pair<Position, TRSTerm>> todo = new LinkedList<Pair<Position, TRSTerm>>();
        todo.add(new Pair<Position, TRSTerm>(Position.create(), right));
        //newVar = new Variable(fne.getFreshName("arithMove" + pos.toString(), false));
        while (!todo.isEmpty()) {
            final Pair<Position, TRSTerm> p = todo.poll();
            final Position pos = p.x;
            final TRSTerm term = p.y;
            if (term.isConstant() || term.isVariable()) {
                //We don't care
                continue;
            }
            final TRSFunctionApplication fA = (TRSFunctionApplication)term;
            final ImmutableList<TRSTerm> fAArgs = fA.getArguments();
            for (int idx = 0; idx < fAArgs.size(); idx++) {
                final TRSTerm arg = fAArgs.get(idx);
                if (arg instanceof TRSFunctionApplication) {
                    final FunctionSymbol argFs = ((TRSFunctionApplication) arg).getRootSymbol();
                    final Position argPos = pos.append(idx);
                    if (
                        predefinedMap.isPredefinedFunction(argFs)
                        || argFs.equals(IntegerConstraintCleaner.INTERNAL_MAX_SYMBOL)
                    ) {
                        TRSVariable freshVar = termToFreshVarMap.get(arg);
                        if (freshVar == null) {
                            freshVar = TRSTerm.createVariable(fne.getFreshName("arith", false));
                            termToFreshVarMap.put(arg, freshVar);
                        }
                        newRight = newRight.replaceAt(argPos, freshVar);
                        final ArrayList<TRSTerm> eqArgs = new ArrayList<>();
                        eqArgs.add(freshVar);
                        eqArgs.add(arg);
                        final TRSFunctionApplication eqConstraint =
                            TRSTerm.createFunctionApplication(
                                predefinedMap.getSym(Func.Eq, DomainFactory.INTEGER_INTEGER),
                                eqArgs
                            );
                        newConstraints = IDPv2ToIDPv1Utilities.getConjunction(newConstraints, eqConstraint);
                    } else {
                        todo.add(new Pair<Position, TRSTerm>(argPos, arg));
                    }
                }
            }
        }
        return IGeneralizedRule.create(left, newRight, newConstraints);
    }

    /**
     * @param rule Some rule.
     * @param predefinedMap The map of predefined symbols.
     * @param keepEvenIfFalseCondition If set to true the rule has a false condition
     * @param removeDivMod should we remove DIV and MOD from rules?
     * @return The transformed rules where all division, modulo, and negation operations as well as FALSE constants
     *         have been replaced by equivalent constructs without these operations and constants.
     */
    public static Set<IGeneralizedRule> removeDivModAndNotAndNotEqualAndOrAndFalse(
        IGeneralizedRule rule,
        RoundingBehaviour roundingBehaviour, 
        IDPPredefinedMap predefinedMap,
        boolean keepEvenIfFalseCondition,
        boolean removeDivMod
    ) {
        final Set<IGeneralizedRule> res = new LinkedHashSet<IGeneralizedRule>();
        final TRSTerm cond = rule.getCondTerm();
        if (cond == null || cond.isVariable()) {
            res.add(rule);
        } else {
            Set<IGeneralizedRule> newRules;
            if(removeDivMod) {
            	newRules =  IRSwTFormatTransformer.killDivMod(rule, roundingBehaviour, predefinedMap);
            } else {
            	newRules = Collections.singleton(rule);
            }
            
            for (IGeneralizedRule newRule : newRules) {
                final TRSFunctionApplication condFA = (TRSFunctionApplication)newRule.getCondTerm();
                TRSTerm killedNot = IRSwTFormatTransformer.killNOT(condFA, predefinedMap);
                final Set<TRSTerm> newConds =
                    killedNot.isVariable() ?
                        Collections.singleton(killedNot) :
                            IRSwTFormatTransformer.killOR(
                                IRSwTFormatTransformer.killNE(
                                    (TRSFunctionApplication)killedNot,
                                    predefinedMap
                                ),
                                predefinedMap
                            );
                for (TRSTerm newCond : newConds) {
                    if (newCond.isVariable()) {
                        res.add(IGeneralizedRule.create(newRule.getLeft(), newRule.getRight(), newCond, newRule.getLeftOutputVariables()));
                    } else {
                        TRSTerm killedFalse =
                            IRSwTFormatTransformer.killFALSE((TRSFunctionApplication)newCond, predefinedMap);
                        if (killedFalse != null) {
                            res.add(IGeneralizedRule.create(newRule.getLeft(), newRule.getRight(), killedFalse, newRule.getLeftOutputVariables()));
                        } else if (keepEvenIfFalseCondition) { // killed false but keep even if false condition
                            res.add(IGeneralizedRule.create(newRule.getLeft(), newRule.getRight(), newCond, newRule.getLeftOutputVariables()));
                        }
                    }
                }
            }
        }
        return res;
    }

    /**
     * Transforms input rules into the format that is used by the following IRS processors (left-linear, no !=, no
     * division/modulo operations).
     * @param rules the rules to transform
     * @param predefinedMap semantics of predefined symbols
     * @param map a map which stores the mapping from old to new rules for CeTA
     * @return transformed rules
     */
    public static Set<IGeneralizedRule> transformRules(Set<IGeneralizedRule> rules, RoundingBehaviour roundingBehaviour, IDPPredefinedMap predefinedMap, Map<IGeneralizedRule,IGeneralizedRule> map) {
        return new IRSwTFormatTransformer(new Args()).transform(rules, roundingBehaviour, predefinedMap, map);
    }

    private Set<IGeneralizedRule> transform(Set<IGeneralizedRule> rules, RoundingBehaviour roundingBehaviour, IDPPredefinedMap predefinedMap, Map<IGeneralizedRule,IGeneralizedRule> map) {
        final LinkedHashSet<IGeneralizedRule> newRules = new LinkedHashSet<IGeneralizedRule>();
        for (IGeneralizedRule rule : rules) {
            final IGeneralizedRule newRule = IRSwTFormatTransformer.moveArithmeticToConstrains(rule, predefinedMap);
            //Remove ! (does not exist anyway, done) and != and the ensuing ||:
            Set<IGeneralizedRule> tmp = Collections.singleton(newRule);
            if (args.removeDivAndMod) {
                tmp = IRSwTFormatTransformer.removeDivModAndNotAndNotEqualAndOrAndFalse(newRule, roundingBehaviour, predefinedMap, false, true);
            }
            if (args.linearizeLhss) {
                tmp = makeLhsLinear(tmp, predefinedMap);
            }
            if (Options.certifier.isCeta()) {
                if (tmp.size() == 1) {
                    map.put(rule, tmp.iterator().next());
                } else {
                    throw new RuntimeException("IRSwTFormatTranslator must not transform a single rule into multiple rules in certified mode");
                }
            }
            newRules.addAll(tmp);
        }
        return newRules;
    }

    /**
     * @param t some term
     * @param fne a fresh name generator used to get new variable names
     * @param newConds the set in which we push new conditions
     * @param predefinedMap the predefined map
     * @return a rule in which division operations have been replaced by an equivalent expression using multiplication
     * and additional variables
     */
    private static TRSTerm killDivInTerm(
        TRSTerm t,
        RoundingBehaviour roundingBehaviour,
        FreshNameGenerator fne,
        Set<TRSTerm> newConds,
        IDPPredefinedMap predefinedMap
    ) {
        if (t == null || t.isVariable()) {
            return t;
        }
        final TRSFunctionApplication fa = (TRSFunctionApplication)t;
        final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(fa.getArguments().size());
        for (TRSTerm arg : fa.getArguments()) {
            if (arg.isVariable()) {
                newArgs.add(arg);
                continue;
            }
            final TRSFunctionApplication argFa = (TRSFunctionApplication)arg;
            final FunctionSymbol argFs = argFa.getRootSymbol();
            if (predefinedMap.isDiv(argFs) || predefinedMap.isMod(argFs)) {
                final TRSTerm x = IRSwTFormatTransformer.killDivInTerm(argFa.getArgument(0), roundingBehaviour, fne, newConds, predefinedMap);
                final TRSTerm y = IRSwTFormatTransformer.killDivInTerm(argFa.getArgument(1), roundingBehaviour, fne, newConds, predefinedMap);

                DivModResolvingResult divModRes = roundingBehaviour.divModEquivalent(x, y, fne, predefinedMap);
                
                newConds.addAll(divModRes.getConds());
                
                if (predefinedMap.isDiv(argFs)) {
                    newArgs.add(divModRes.getDiv());
                } else if (predefinedMap.isMod(argFs)) {
                    newArgs.add(divModRes.getRem());
                }
            } else {
                newArgs.add(IRSwTFormatTransformer.killDivInTerm(arg, roundingBehaviour, fne, newConds, predefinedMap));
            }
        }
        return TRSTerm.createFunctionApplication(fa.getRootSymbol(), newArgs);
    }

    /**
     * @param rule some rule
     * @param predefinedMap the predefined map
     * @return a rule in which division and modulo operations have been replaced by an equivalent expression using
     * multiplication and additional variables
     */
    private static Set<IGeneralizedRule> killDivMod(IGeneralizedRule rule, RoundingBehaviour roundingBehaviour, IDPPredefinedMap predefinedMap) {
        final Set<TRSTerm> newConds = new LinkedHashSet<TRSTerm>();
        final FreshNameGenerator fne = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        fne.lockHasNames(rule.getVariables());
        final TRSTerm newRhs = IRSwTFormatTransformer.killDivInTerm(rule.getRight(), roundingBehaviour, fne, newConds, predefinedMap);
        TRSTerm newCondTerm = IRSwTFormatTransformer.killDivInTerm(rule.getCondTerm(), roundingBehaviour, fne, newConds, predefinedMap);
        //We had some DIV/MOD:
        if (newConds.size() > 0) {
            final FunctionSymbol lhsSym = rule.getLeft().getRootSymbol();
            final FunctionSymbol lhsSymTmp = FunctionSymbol.create(lhsSym.getName() + "'", lhsSym.getArity());
            final TRSFunctionApplication middleFA =
                TRSTerm.createFunctionApplication(lhsSymTmp, rule.getLeft().getArguments());
            final LinkedHashSet<IGeneralizedRule> res = new LinkedHashSet<>();
            res.add(IGeneralizedRule.create(rule.getLeft(), middleFA, newCondTerm, rule.getLeftOutputVariables()));
            for (TRSTerm additionalCond : newConds) {
                newCondTerm = IDPv2ToIDPv1Utilities.getConjunction(additionalCond, newCondTerm);
            }
            res.add(IGeneralizedRule.create(middleFA, newRhs, newCondTerm, rule.getLeftOutputVariables()));
            return res;
        }
        return Collections.<IGeneralizedRule> singleton(rule);
    }

    /**
     * @param left The left-hand side.
     * @param right The right-hand side.
     * @param predefinedMap The predefined symbols.
     * @return The term 'left < right || left > right'.
     */
    private static TRSFunctionApplication ltOrGt(TRSTerm left, TRSTerm right, IDPPredefinedMap predefinedMap) {
        return
            TRSTerm.createFunctionApplication(
                predefinedMap.getSym(Func.Lor, DomainFactory.BOOLEAN_BOOLEAN),
                TRSTerm.createFunctionApplication(
                    predefinedMap.getSym(Func.Lt, DomainFactory.INTEGER_INTEGER),
                    left,
                    right
                ),
                TRSTerm.createFunctionApplication(
                    predefinedMap.getSym(Func.Gt, DomainFactory.INTEGER_INTEGER),
                    left,
                    right
                )
            );
    }

    /**
     * @param f Some function application.
     * @param predefinedMap The predefined symbols.
     * @return The negation of the specified function application.
     */
    private static TRSTerm negate(TRSFunctionApplication f, IDPPredefinedMap predefinedMap) {
        FunctionSymbol sym = f.getRootSymbol();
        if (sym.getName().equals("TRUE") && sym.getArity() == 0) {
            return TRSTerm.createFunctionApplication(FunctionSymbol.create("FALSE", 0));
        } else if (sym.getName().equals("FALSE") && sym.getArity() == 0) {
            return TRSTerm.createFunctionApplication(FunctionSymbol.create("TRUE", 0));
        } else if (predefinedMap.isLnot(sym)) {
            return f.getArgument(0);
        } else if (predefinedMap.isGe(sym)) {
            return
                TRSTerm.createFunctionApplication(
                    predefinedMap.getSym(Func.Lt, DomainFactory.INTEGER_INTEGER),
                    f.getArguments()
                );
        } else if (predefinedMap.isGt(sym)) {
            return
                TRSTerm.createFunctionApplication(
                    predefinedMap.getSym(Func.Le, DomainFactory.INTEGER_INTEGER),
                    f.getArguments()
                );
        } else if (predefinedMap.isLe(sym)) {
            return
                TRSTerm.createFunctionApplication(
                    predefinedMap.getSym(Func.Gt, DomainFactory.INTEGER_INTEGER),
                    f.getArguments()
                );
        } else if (predefinedMap.isLt(sym)) {
            return
                TRSTerm.createFunctionApplication(
                    predefinedMap.getSym(Func.Ge, DomainFactory.INTEGER_INTEGER),
                    f.getArguments()
                );
        } else if (predefinedMap.isEq(sym)) {
            return
                TRSTerm.createFunctionApplication(
                    predefinedMap.getSym(Func.Neq, DomainFactory.INTEGER_INTEGER),
                    f.getArguments()
                );
        } else if (predefinedMap.isNeq(sym)) {
            return
                TRSTerm.createFunctionApplication(
                    predefinedMap.getSym(Func.Eq, DomainFactory.INTEGER_INTEGER),
                    f.getArguments()
                );
        } else if (predefinedMap.isLor(sym)) {
            ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
            for (TRSTerm arg : f.getArguments()) {
                if (arg.isVariable()) {
                    continue;
                }
                args.add(IRSwTFormatTransformer.negate((TRSFunctionApplication)arg, predefinedMap));
            }
            return TRSTerm.createFunctionApplication(predefinedMap.getSym(Func.Land, DomainFactory.BOOLEAN_BOOLEAN), args);
        } else if (predefinedMap.isLand(sym)) {
            ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
            for (TRSTerm arg : f.getArguments()) {
                if (arg.isVariable()) {
                    continue;
                }
                args.add(IRSwTFormatTransformer.negate((TRSFunctionApplication)arg, predefinedMap));
            }
            return TRSTerm.createFunctionApplication(predefinedMap.getSym(Func.Lor, DomainFactory.BOOLEAN_BOOLEAN), args);
        } else {
            throw new IllegalArgumentException("Cannot negate input term " + f.toString() + "!");
        }
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof IRSLike && !((IRSLike) obl).isBounded();
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti)
    throws AbortionException {
        assert obl instanceof IRSLike : "Wrong obligation type!";
        final IRSLike irs = (IRSLike)obl;
        final Set<IGeneralizedRule> rules = irs.getRules();
        Map<IGeneralizedRule, IGeneralizedRule> oldNewMap = new LinkedHashMap<>();
        final Set<IGeneralizedRule> newRules = transform(rules, RoundingBehaviour.UNKNOWN, IDPPredefinedMap.DEFAULT_MAP, oldNewMap);
        // if (!IntTRSFreeVarFilter.haveSameRules(newRules, rules)) {
            return ResultFactory.proved(irs.create(newRules, irs.getStartTerm()), YNMImplication.EQUIVALENT, new IRSFormatTransformerProof(irs, oldNewMap));
        // }
        // return ResultFactory.unsuccessful();
    }

    /**
     * A very fine proof.
     * @author Marc Brockschmidt (don't blame me)
     */
    public class IRSFormatTransformerProof extends DefaultProof {

        private final IRSLike lts;
        private final Map<IGeneralizedRule,IGeneralizedRule> oldNew;
        
        public IRSFormatTransformerProof(IRSLike lts, Map<IGeneralizedRule,IGeneralizedRule> oldNew) {
            this.lts = lts;
            this.oldNew = oldNew;
        }
        
        /**
         * @param o export helper
         * @param level unused
         * @return a useless string
         */
        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return
                "Reformatted IRS to match normalized format "
                + "(transformed away non-linear left-hand sides, !=, / and %).";
        }     
        
        /**
         * This proof is used as switch-to-cooperation problem
         */
        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            Element cps = CPFTag.LTS_CUT_POINTS.create(doc);
            Set<FunctionSymbol> fs = new HashSet<FunctionSymbol>(); 
            for (IGeneralizedRule rule : oldNew.values()) {
               fs.add(rule.getRootSymbol());   
            }
            for (FunctionSymbol f : fs) {
                String loc = f.getName();
                Element cp = CPFTag.LTS_CUT_POINT.create(doc);
                cp.appendChild(CPFTag.LTS_LOCATION_ID.create(doc, loc));
                cp.appendChild(CPFTag.LTS_SKIP_ID.create(doc, loc));
                Element conj = CPFTag.LTS_CONJUNCTION.create(doc);
                int n = f.getArity();
                for (int i = 1; i <= n; i++) {
                    String xi = IGeneralizedRule.VAR + i;
                    Element pre = CPFTag.LTS_VARIABLE_ID.create(doc, xi);
                    Element post = CPFTag.LTS_POST_VARIABLE.create(doc, CPFTag.LTS_VARIABLE_ID.create(doc, xi));
                    conj.appendChild(CPFTag.LTS_EQ.create(doc, post, pre));
                }
                cp.appendChild(CPFTag.LTS_SKIP_FORMULA.create(doc, conj));
                cps.appendChild(cp);
            }
            return CPFTag.LTS_TERMINATION_PROOF.create(doc,CPFTag.LTS_SWITCH_COOPERATION.create(doc, cps, childrenProofs[0]));
        }
        
        @Override
        public XMLMetaData adaptMetaData(final XMLMetaData xmlPreMetaData) {
            XMLMetaData xmlPre = IRSwTProblem.createInitialMetaData(this.lts);
            return xmlPre.adjustOldNew(this.oldNew);
        }


        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return modus.isPositive();
        }


    }

}
