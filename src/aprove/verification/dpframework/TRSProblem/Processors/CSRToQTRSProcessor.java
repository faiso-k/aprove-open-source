/*
 * Created on 13.04.2005
 */
package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * @version $Id$
 */

public class CSRToQTRSProcessor extends CSRProcessor {

    private final Transformation transformation;

    @ParamsViaArgumentObject
    public CSRToQTRSProcessor(final Arguments arguments) {
        this.transformation = arguments.transformation;
    }

    @Override
    public Result processCSR(final CSRProblem csr, final Abortion aborter) throws AbortionException {

        final Quadruple<Set<Rule>, Boolean, YNMImplication, CSRProof> newProblem =
            this.transformation.getTransformed(csr.getR(), csr.getReplacementMap(), csr.getInnermost());

        if (newProblem != null) {

            QTRSProblem qtrs;
            if (newProblem.x) {
                final Set<Rule> newRules = newProblem.w;
                qtrs = QTRSProblem.create(ImmutableCreator.create(newRules), CollectionUtils.getLeftHandSides(newRules));
            } else {
                qtrs = QTRSProblem.create(ImmutableCreator.create(newProblem.w));
            }
            return ResultFactory.proved(qtrs, newProblem.y, newProblem.z);
        } else {
            return ResultFactory.unsuccessful();
        }

    }

    @Override
    public boolean isCSRApplicable(final CSRProblem csr) {
        if (Options.certifier.isCeta()) {
            return false;
        }
        return true;
    }

    @SuppressWarnings("serial")
    private static class VariableConditionException extends Exception {};
    private static final VariableConditionException VAR_COND = new VariableConditionException();

    /**
     * now here are all the transformations given.
     * @author thiemann
     *
     */
    protected static enum Transformation {

        /**
         * the trivial transformation just ignores the replacementMap
         */
        Trivial{
            @Override
            public String cite(final Export_Util eu) {
                return "";
            }

            @Override
            public Quadruple<Set<Rule>, Boolean, YNMImplication, CSRProof> getTransformed(
                final Set<Rule> R,
                final Map<FunctionSymbol, ? extends Set<Integer>> replacementMap,
                final boolean innermost)
            {
                final boolean newInnermost = false;
                return new Quadruple<Set<Rule>, Boolean, YNMImplication, CSRProof>(
                        R,
                        newInnermost,
                        YNMImplication.SOUND,
                        new TransformationProof(R, this)
                        );
            }
        },

        /**
         * lucas transformation does not require a constant in signature!
         */
        Lucas{
            @Override
            public String cite(final Export_Util eu) {
                return eu.cite(Citation.CS_Luc);
            }
            private TRSTerm transform(
                    final TRSTerm t,
                    final Map<FunctionSymbol, ? extends Set<Integer>> replacementMap,
                    final Map<FunctionSymbol, FunctionSymbol> oldToNewFs,
                    final FunctionSymbolGenerator funSymGen,
                    final Set<TRSVariable> vars,
                    final boolean enlarge // true for left hand sides
                    ) throws VariableConditionException {
                if (t.isVariable()) {
                    if (enlarge) {
                        vars.add((TRSVariable) t);
                    } else {
                        if (!vars.contains(t)) {
                            throw CSRToQTRSProcessor.VAR_COND;
                        }
                    }
                    return t;
                } else {
                    final TRSFunctionApplication ft = (TRSFunctionApplication) t;
                    final FunctionSymbol f = ft.getRootSymbol();
                    final Set<Integer> positions = replacementMap.get(f);
                    FunctionSymbol newF = oldToNewFs.get(f);

                    if (newF == null) {
                        // obtain new function symbol if not yet determined
                        newF = funSymGen.getFresh(f.getName(), positions.size());
                        oldToNewFs.put(f, newF);
                    }

                    final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(newF.getArity());
                    for (final Integer position : positions) {
                        final TRSTerm oldArg = ft.getArgument(position);
                        final TRSTerm newArg = this.transform(oldArg, replacementMap, oldToNewFs, funSymGen, vars, enlarge);
                        newArgs.add(newArg);
                    }

                    return TRSTerm.createFunctionApplication(newF, ImmutableCreator.create(newArgs));
                }
            }

            @Override
            public Quadruple<Set<Rule>, Boolean, YNMImplication, CSRProof> getTransformed(
                final Set<Rule> R,
                final Map<FunctionSymbol, ? extends Set<Integer>> replacementMap,
                final boolean innermost)
            {
                final Map<FunctionSymbol, FunctionSymbol> oldToNewFs = new HashMap<FunctionSymbol, FunctionSymbol>(replacementMap.size());
                final FunctionSymbolGenerator funSymGen = new FunctionSymbolGenerator(replacementMap.size());
                final Set<TRSVariable> vars = new HashSet<TRSVariable>();
                final Set<Rule> newRules = new LinkedHashSet<Rule>(R.size());
                try {
                    for (final Rule rule : R) {
                        vars.clear();
                        final TRSTerm left = this.transform(rule.getLeft(), replacementMap, oldToNewFs, funSymGen, vars, true);
                        final TRSTerm right = this.transform(rule.getRight(), replacementMap, oldToNewFs, funSymGen, vars, false);
                        newRules.add(Rule.create((TRSFunctionApplication)left, right));
                    }
                    final boolean newInnermost = false;
                    return new Quadruple<Set<Rule>, Boolean, YNMImplication, CSRProof>(
                            newRules,
                            newInnermost,
                            YNMImplication.SOUND,
                            new TransformationProof(newRules, this)
                            );
                } catch (final VariableConditionException e) {
                    return null;
                }
            }
        },

        /**
         * zantema transformation does not require a constant in signature!
         */
        Zantema{
            @Override
            public String cite(final Export_Util eu) {
                return eu.cite(Citation.CS_Zan);
            }

            private TRSTerm transform(
                    final TRSTerm t,
                    final FunctionSymbol a, // null if we are on the left hand side
                    final boolean zPrime, // use z or zPrime
                    final Map<FunctionSymbol, ? extends Set<Integer>> replacementMap,
                    final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbol>> oldToNewFs, // f to <f, f_inact>
                    final FunctionSymbolGenerator funSymGen, // to get unique names.
                    final Set<FunctionSymbol> usedFinact, // the set where we add those f, if f_inact is built.
                    final Set<TRSVariable> inactiveVars, // the set of variables at inactive positions in lhs.
                    final boolean addInactive // are we at an inactive position? irrelevant if a != null
                    ) {
                if (t.isVariable()) {
                    if (a == null) { // on lhs compute inactive vars
                        if (addInactive) {
                            inactiveVars.add((TRSVariable) t);
                        }
                        return t;
                    } else {
                        // on rhs do replacement
                        if (inactiveVars.contains(t)) {
                            return TRSTerm.createFunctionApplication(a, new TRSTerm[]{t});
                        } else {
                            return t;
                        }
                    }
                } else {
                    final TRSFunctionApplication ft = (TRSFunctionApplication) t;
                    final FunctionSymbol f = ft.getRootSymbol();
                    final int arity = f.getArity();
                    final Set<Integer> positions = replacementMap.get(f);
                    Pair<FunctionSymbol,FunctionSymbol> newFF = oldToNewFs.get(f);

                    if (newFF == null) {
                        // obtain new function symbols if not yet determined
                        final String name = f.getName();
                        newFF = new Pair<FunctionSymbol, FunctionSymbol>(funSymGen.getFresh(name, arity), funSymGen.getFresh(name+"Inact", arity));
                        oldToNewFs.put(f, newFF);
                    }

                    final FunctionSymbol newF;
                    if (zPrime) {
                        newF = newFF.y;
                        usedFinact.add(f);
                    } else {
                        newF = newFF.x;
                    }

                    final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(arity);
                    int i = 0;
                    for (final TRSTerm oldArg : ft.getArguments()) {
                        final boolean inactivePosition = !positions.contains(Integer.valueOf(i));
                        final TRSTerm newArg = this.transform(oldArg, a, inactivePosition, replacementMap, oldToNewFs, funSymGen, usedFinact, inactiveVars, addInactive || inactivePosition);
                        newArgs.add(newArg);
                        i++;
                    }

                    return TRSTerm.createFunctionApplication(newF, ImmutableCreator.create(newArgs));
                }
            }

            @Override
            public Quadruple<Set<Rule>, Boolean, YNMImplication, CSRProof> getTransformed(
                final Set<Rule> R,
                final Map<FunctionSymbol, ? extends Set<Integer>> replacementMap,
                final boolean innermost)
            {
                final int nrOfFs = replacementMap.size();
                final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbol>> oldToNewFs = new HashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbol>>(nrOfFs);
                final FunctionSymbolGenerator funSymGen = new FunctionSymbolGenerator(nrOfFs*2 + 1);
                final Set<FunctionSymbol> usedFinact = new LinkedHashSet<FunctionSymbol>(nrOfFs);
                final Set<TRSVariable> inactiveVars = new HashSet<TRSVariable>();
                final FunctionSymbol a = funSymGen.getFresh("a", 1);
                final Set<Rule> newRules = new LinkedHashSet<Rule>(R.size() + nrOfFs*2 + 1);
                // add Rmu Z_1
                // add Z(l) -> Z(r)sigma
                for (final Rule rule : R) {
                    inactiveVars.clear();
                    final TRSTerm left = this.transform(rule.getLeft(), null, false, replacementMap, oldToNewFs, funSymGen, usedFinact, inactiveVars, false);
                    final TRSTerm right = this.transform(rule.getRight(), a, false, replacementMap, oldToNewFs, funSymGen, usedFinact, inactiveVars, false);
                    newRules.add(Rule.create((TRSFunctionApplication)left, right));
                }
                // add Rmu Z_2
                // add a(x) -> x
                final TRSVariable x = TRSTerm.createVariable("x");
                newRules.add(Rule.create(TRSTerm.createFunctionApplication(a, new TRSTerm[]{x}), x));
                // add remaining rules
                for (final FunctionSymbol f : usedFinact) {
                    final Pair<FunctionSymbol, FunctionSymbol> newFF = oldToNewFs.get(f);
                    final int n = f.getArity();
                    final ArrayList<TRSVariable> xsList = new ArrayList<TRSVariable>(n);
                    for (int i=1; i<=n; i++) {
                        xsList.add(TRSTerm.createVariable("x"+i));
                    }
                    final ImmutableArrayList<TRSVariable> xs = ImmutableCreator.create(xsList);
                    final TRSFunctionApplication fx = TRSTerm.createFunctionApplication(newFF.x, xs);
                    final TRSFunctionApplication inactFx = TRSTerm.createFunctionApplication(newFF.y, xs);
                    newRules.add(Rule.create(fx, inactFx));
                    newRules.add(Rule.create(TRSTerm.createFunctionApplication(a, new TRSTerm[]{inactFx}), fx));
                }
                final boolean newInnermost = false;
                return new Quadruple<Set<Rule>, Boolean, YNMImplication, CSRProof>(
                        newRules,
                        newInnermost,
                        YNMImplication.SOUND,
                        new TransformationProof(newRules, this)
                );
            }
        },

        /**
         * Improved FerreiraRibeiro does not require a constant in signature!
         * (The one rule that would be added for a fresh constant is clearly
         *  superflouos as it is an instance of the a(x) -> x rule.)
         */
        ImprovedFerreiraRibeiro{
            @Override
            public String toString() {
                return "Improved Ferreira Ribeiro";
            }

            @Override
            public String cite(final Export_Util eu) {
                return eu.cite(new Citation[]{Citation.CS_FR, Citation.CS_Term});
            }

            private TRSTerm transform(
                    final TRSTerm t,
                    final FunctionSymbol a, // null if we are on the left hand side
                    final boolean frPrime, // use FR or FR' (the same as are we at inactive position)
                    final Map<FunctionSymbol, ? extends Set<Integer>> replacementMap,
                    final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbol>> oldToNewFs, // f to <f, f_inact>
                    final FunctionSymbolGenerator funSymGen, // to get unique names.
                    final Set<FunctionSymbol> usedFinact, // the set where we add those f, if f_inact is built.
                    final Set<TRSVariable> inactiveVars // the set of variables at inactive positions in lhs.
                    ) {
                if (t.isVariable()) {
                    if (a == null) { // on lhs compute inactive vars
                        if (frPrime) {
                            inactiveVars.add((TRSVariable) t);
                        }
                        return t;
                    } else {
                        // on rhs do replacement
                        if (inactiveVars.contains(t)) {
                            return TRSTerm.createFunctionApplication(a, new TRSTerm[]{t});
                        } else {
                            return t;
                        }
                    }
                } else {
                    final TRSFunctionApplication ft = (TRSFunctionApplication) t;
                    final FunctionSymbol f = ft.getRootSymbol();
                    final int arity = f.getArity();
                    final Set<Integer> positions = replacementMap.get(f);
                    Pair<FunctionSymbol,FunctionSymbol> newFF = oldToNewFs.get(f);

                    if (newFF == null) {
                        // obtain new function symbols if not yet determined
                        final String name = f.getName();
                        newFF = new Pair<FunctionSymbol, FunctionSymbol>(funSymGen.getFresh(name, arity), funSymGen.getFresh(name+"Inact", arity));
                        oldToNewFs.put(f, newFF);
                    }

                    final FunctionSymbol newF;
                    if (frPrime) {
                        newF = newFF.y;
                        usedFinact.add(f);
                    } else {
                        newF = newFF.x;
                    }

                    final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(arity);
                    int i = 0;
                    for (final TRSTerm oldArg : ft.getArguments()) {
                        final boolean inactivePosition = frPrime || !positions.contains(Integer.valueOf(i));
                        final TRSTerm newArg = this.transform(oldArg, a, inactivePosition, replacementMap, oldToNewFs, funSymGen, usedFinact, inactiveVars);
                        newArgs.add(newArg);
                        i++;
                    }

                    return TRSTerm.createFunctionApplication(newF, ImmutableCreator.create(newArgs));
                }
            }

            @Override
            public Quadruple<Set<Rule>, Boolean, YNMImplication, CSRProof> getTransformed(
                final Set<Rule> R,
                final Map<FunctionSymbol, ? extends Set<Integer>> replacementMap,
                final boolean innermost)
            {
                final int nrOfFs = replacementMap.size();
                final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbol>> oldToNewFs = new HashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbol>>(nrOfFs);
                final FunctionSymbolGenerator funSymGen = new FunctionSymbolGenerator(nrOfFs*2 + 1);
                final Set<FunctionSymbol> usedFinact = new LinkedHashSet<FunctionSymbol>(nrOfFs);
                final Set<TRSVariable> inactiveVars = new LinkedHashSet<TRSVariable>();
                final FunctionSymbol a = funSymGen.getFresh("a", 1);
                final Set<Rule> newRules = new LinkedHashSet<Rule>(R.size() + nrOfFs*2 + 1);
                // add Rmu FR_1
                // add FR(l) -> FR(r)sigma
                for (final Rule rule : R) {
                    inactiveVars.clear();
                    final TRSTerm left = this.transform(rule.getLeft(), null, false, replacementMap, oldToNewFs, funSymGen, usedFinact, inactiveVars);
                    final TRSTerm right = this.transform(rule.getRight(), a, false, replacementMap, oldToNewFs, funSymGen, usedFinact, inactiveVars);
                    newRules.add(Rule.create((TRSFunctionApplication)left, right));
                }
                // add Rmu FR_2
                // add a(x) -> x
                final TRSVariable x = TRSTerm.createVariable("x");
                newRules.add(Rule.create(TRSTerm.createFunctionApplication(a, new TRSTerm[]{x}), x));
                // add remaining rules
                // (we used improved variant of JFP-report)
                for (final FunctionSymbol f : usedFinact) {
                    final Pair<FunctionSymbol, FunctionSymbol> newFF = oldToNewFs.get(f);
                    final int n = f.getArity();
                    final ArrayList<TRSVariable> xsList = new ArrayList<TRSVariable>(n);
                    final ArrayList<TRSTerm> xsList2 = new ArrayList<TRSTerm>(n);
                    int i = 0;
                    while (i<n) {
                        final boolean actPos = replacementMap.get(f).contains(i);
                        i++;
                        final TRSVariable x_i = TRSTerm.createVariable("x"+i);
                        xsList.add(x_i);
                        if (actPos) {
                            xsList2.add(TRSTerm.createFunctionApplication(a, new TRSTerm[]{x_i}));
                        } else {
                            xsList2.add(x_i);
                        }
                    }
                    final ImmutableArrayList<TRSVariable> xs = ImmutableCreator.create(xsList);
                    final ImmutableArrayList<TRSTerm> xs2 = ImmutableCreator.create(xsList2);
                    final FunctionSymbol newF = newFF.x;
                    final TRSFunctionApplication fx = TRSTerm.createFunctionApplication(newF, xs);
                    final TRSFunctionApplication fx2 = TRSTerm.createFunctionApplication(newF, xs2);
                    final TRSFunctionApplication inactFx = TRSTerm.createFunctionApplication(newFF.y, xs);
                    newRules.add(Rule.create(fx, inactFx));
                    newRules.add(Rule.create(TRSTerm.createFunctionApplication(a, new TRSTerm[]{inactFx}), fx2));
                }
                final boolean newInnermost = false;
                return new Quadruple<Set<Rule>, Boolean, YNMImplication, CSRProof>(
                        newRules,
                        newInnermost,
                        YNMImplication.SOUND,
                        new TransformationProof(newRules, this)
                );
            }
        },

        /**
         * R^1_mu.
         * Needs constant in signature.
         * For counterexample consider CSR f(x,x) -> f(x,x) with mu(f) = {1} which shows that constant is needed.
         * Uses different transformations for innermost and termination (innermostReport and JFP).
         * Perhaps the better JFP-version is also sound for innermost, but currently this is unknown.
         */
        IncompleteGieslMiddeldorp{

            @Override
            public String toString() {
                return "Incomplete Giesl Middeldorp";
            }

            @Override
            public String cite(final Export_Util eu) {
                return eu.cite(Citation.CS_Term);
            }

            private TRSTerm transform(
                    final TRSTerm t,
                    final FunctionSymbol mark,
                    final Map<FunctionSymbol, ? extends Set<Integer>> replacementMap,
                    final Map<FunctionSymbol, FunctionSymbol> oldToMaybeActiveFs // f to f_active for f in D, f to f for f in C
                    ) {
                if (t.isVariable()) {
                    return TRSTerm.createFunctionApplication(mark, new TRSTerm[]{t});
                } else {
                    final TRSFunctionApplication ft = (TRSFunctionApplication) t;
                    final FunctionSymbol f = ft.getRootSymbol();
                    final int arity = f.getArity();
                    final Set<Integer> positions = replacementMap.get(f);
                    final FunctionSymbol maybeActiveF = oldToMaybeActiveFs.get(f);

                    final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(arity);
                    int i = 0;
                    for (final TRSTerm oldArg : ft.getArguments()) {
                        if (positions.contains(i)) {
                            newArgs.add( this.transform(oldArg, mark, replacementMap, oldToMaybeActiveFs) );
                        } else {
                            newArgs.add( oldArg );
                        }
                        i++;
                    }

                    return TRSTerm.createFunctionApplication(maybeActiveF, ImmutableCreator.create(newArgs));
                }
            }

            @Override
            public Quadruple<Set<Rule>, Boolean, YNMImplication, CSRProof> getTransformed(
                final Set<Rule> R,
                final Map<FunctionSymbol, ? extends Set<Integer>> replacementMap,
                final boolean innermost)
            {
                if (innermost) {

                    // DLT-report version of R^1_mu

                    final int nrOfFs = replacementMap.size();
                    final FunctionSymbolGenerator funSymGen = new FunctionSymbolGenerator(nrOfFs + 2);
                    final FunctionSymbol mark = funSymGen.getFresh("mark", 1);
                    final FunctionSymbol active = funSymGen.getFresh("active", 1);
                    final Set<Rule> newRules = new LinkedHashSet<Rule>(R.size() + nrOfFs+1);

                    // add rules for original rules
                    for (final Rule rule : R) {
                        newRules.add(Rule.create(
                                TRSTerm.createFunctionApplication(active, new TRSTerm[]{rule.getLeft()}),
                                TRSTerm.createFunctionApplication(mark, new TRSTerm[]{rule.getRight()})
                                ));
                    }

                    boolean gotConstant = false;

                    // add rules for signature
                    for (final Map.Entry<FunctionSymbol, ? extends Set<Integer>> fRep : replacementMap.entrySet()) {
                        FunctionSymbol f = fRep.getKey();
                        final Set<Integer> replacement = fRep.getValue();
                        final int n = f.getArity();
                        if (n == 0) {
                            gotConstant = true;
                        }
                        f = funSymGen.getFresh(f.getName(), n);

                        final ArrayList<TRSVariable> xsList = new ArrayList<TRSVariable>(n);
                        final ArrayList<TRSTerm> xsList2 = new ArrayList<TRSTerm>(n);
                        for (int i=0; i<n; i++) {
                            final TRSVariable x_i = TRSTerm.createVariable("x"+(i+1));
                            xsList.add(x_i);
                            if (replacement.contains(i)) {
                                xsList2.add(TRSTerm.createFunctionApplication(mark, new TRSTerm[]{x_i}));
                            } else {
                                xsList2.add(x_i);
                            }
                        }
                        final ImmutableArrayList<TRSVariable> xs = ImmutableCreator.create(xsList);
                        final ImmutableArrayList<TRSTerm> xs2 = ImmutableCreator.create(xsList2);

                        final TRSFunctionApplication fx = TRSTerm.createFunctionApplication(f, xs);
                        final TRSFunctionApplication fx2 = TRSTerm.createFunctionApplication(f, xs2);

                        // mark -> active
                        newRules.add(Rule.create(
                                TRSTerm.createFunctionApplication(mark, new TRSTerm[]{fx}),
                                TRSTerm.createFunctionApplication(active, new TRSTerm[]{fx2})
                                ));

                    }

                    // dummy constant rule
                    if (!gotConstant) {
                        final TRSTerm[] dummy =
                            new TRSTerm[]{
                                TRSTerm.createFunctionApplication(funSymGen.getFresh("dummy", 0), TRSTerm.EMPTY_ARGS)
                            };
                        newRules.add(Rule.create(
                                TRSTerm.createFunctionApplication(mark, dummy),
                                TRSTerm.createFunctionApplication(active, dummy)
                                ));
                    }

                    // active(x) -> x
                    final TRSTerm x = TRSTerm.createVariable("x");
                    newRules.add(Rule.create(TRSTerm.createFunctionApplication(active, new TRSTerm[]{x}), x));

                    final boolean newInnermost = true;
                    return new Quadruple<Set<Rule>, Boolean, YNMImplication, CSRProof>(
                            newRules,
                            newInnermost,
                            YNMImplication.SOUND,
                            new TransformationProof(newRules, this)
                    );
                } else {

                    // JFP version of R^1_mu

                    final int nrOfFs = replacementMap.size();
                    final Map<FunctionSymbol, FunctionSymbol> oldToNewFs = new HashMap<FunctionSymbol, FunctionSymbol>(nrOfFs);
                    final Map<FunctionSymbol, FunctionSymbol> oldToMaybeActiveFs = new HashMap<FunctionSymbol, FunctionSymbol>(nrOfFs);
                    final FunctionSymbolGenerator funSymGen = new FunctionSymbolGenerator(nrOfFs*2 + 1);
                    final FunctionSymbol mark = funSymGen.getFresh("mark", 1);
                    final Set<Rule> newRules = new LinkedHashSet<Rule>(R.size() + nrOfFs*2);

                    boolean gotConstant = false;

                    // add rules for defined function symbols and determine new symbols
                    for (final Rule rule : R) {
                        final FunctionSymbol f = rule.getRootSymbol();
                        FunctionSymbol newF = oldToNewFs.get(f);
                        if (newF == null) {
                            final int n = f.getArity();
                            if (n == 0) {
                                gotConstant = true;
                            }
                            final String name = f.getName();
                            newF = funSymGen.getFresh(name, n);
                            final FunctionSymbol activeF = funSymGen.getFresh(name+"Active", n);
                            oldToNewFs.put(f, newF);
                            oldToMaybeActiveFs.put(f, activeF);

                            final ArrayList<TRSVariable> xsList = new ArrayList<TRSVariable>(n);
                            final ArrayList<TRSTerm> xsList2 = new ArrayList<TRSTerm>(n);
                            int i = 0;
                            while (i<n) {
                                final boolean actPos = replacementMap.get(f).contains(i);
                                i++;
                                final TRSVariable x_i = TRSTerm.createVariable("x"+i);
                                xsList.add(x_i);
                                if (actPos) {
                                    xsList2.add(TRSTerm.createFunctionApplication(mark, new TRSTerm[]{x_i}));
                                } else {
                                    xsList2.add(x_i);
                                }
                            }
                            final ImmutableArrayList<TRSVariable> xs = ImmutableCreator.create(xsList);
                            final ImmutableArrayList<TRSTerm> xs2 = ImmutableCreator.create(xsList2);

                            final TRSFunctionApplication fx = TRSTerm.createFunctionApplication(newF, xs);
                            final TRSFunctionApplication fxAct = TRSTerm.createFunctionApplication(activeF, xs);
                            final TRSFunctionApplication fxAct2 = TRSTerm.createFunctionApplication(activeF, xs2);

                            newRules.add(Rule.create(TRSTerm.createFunctionApplication(mark, new TRSTerm[]{fx}), fxAct2));
                            newRules.add(Rule.create(fxAct, fx));
                        }
                    }

                    // add rules for constructor symbols
                    for (final Map.Entry<FunctionSymbol, ? extends Set<Integer>> fRep : replacementMap.entrySet()) {
                        final FunctionSymbol f = fRep.getKey();
                        FunctionSymbol newF = oldToNewFs.get(f);
                        if (newF == null) { // we have a constructor
                            final int n = f.getArity();
                            if (n == 0) {
                                gotConstant = true;
                            }
                            newF = funSymGen.getFresh(f.getName(), n);
                            oldToNewFs.put(f, newF);
                            oldToMaybeActiveFs.put(f, newF);

                            final ArrayList<TRSVariable> xsList = new ArrayList<TRSVariable>(n);
                            final ArrayList<TRSTerm> xsList2 = new ArrayList<TRSTerm>(n);
                            int i = 0;
                            while (i<n) {
                                final boolean actPos = replacementMap.get(f).contains(i);
                                i++;
                                final TRSVariable x_i = TRSTerm.createVariable("x"+i);
                                xsList.add(x_i);
                                if (actPos) {
                                    xsList2.add(TRSTerm.createFunctionApplication(mark, new TRSTerm[]{x_i}));
                                } else {
                                    xsList2.add(x_i);
                                }
                            }
                            final ImmutableArrayList<TRSVariable> xs = ImmutableCreator.create(xsList);
                            final ImmutableArrayList<TRSTerm> xs2 = ImmutableCreator.create(xsList2);

                            final TRSFunctionApplication fx = TRSTerm.createFunctionApplication(newF, xs);
                            final TRSFunctionApplication fx2 = TRSTerm.createFunctionApplication(newF, xs2);

                            newRules.add(Rule.create(TRSTerm.createFunctionApplication(mark, new TRSTerm[]{fx}), fx2));
                        }
                    }

                    // add dummy rule if no constant is present
                    if (!gotConstant) {
                        final TRSTerm dummy =
                            TRSTerm.createFunctionApplication(funSymGen.getFresh("dummy", 0), TRSTerm.EMPTY_ARGS);
                        newRules.add(Rule.create(TRSTerm.createFunctionApplication(mark, new TRSTerm[]{dummy}), dummy));
                    }

                    // add rules for R
                    for (final Rule rule : R) {
                        final TRSFunctionApplication left = rule.getLeft();
                        final TRSTerm right = rule.getRight();
                        final FunctionSymbol f = left.getRootSymbol();
                        final TRSFunctionApplication newLeft =
                            TRSTerm.createFunctionApplication(oldToMaybeActiveFs.get(f), left.getArguments());
                        final TRSTerm newRight = this.transform(right, mark, replacementMap, oldToMaybeActiveFs);
                        newRules.add(Rule.create(newLeft, newRight));
                    }

                    final boolean newInnermost = innermost;
                    return new Quadruple<Set<Rule>, Boolean, YNMImplication, CSRProof>(
                            newRules,
                            newInnermost,
                            YNMImplication.SOUND,
                            new TransformationProof(newRules, this)
                    );
                }
            }
        },



        /**
         * R^2_mu.
         * this transformation does require a constant in signature!
         * For a counterexample consider f(x) -> f(x) with mu(f) = 1
         */
        CompleteGieslMiddeldorp{

            @Override
            public String toString() {
                return "Complete Giesl Middeldorp";
            }

            @Override
            public String cite(final Export_Util eu) {
                return eu.cite(Citation.CS_Term);
            }

            /* real implementation moved to CompleteGieslMiddeldorpTransformation class */
            @Override
            public Quadruple<Set<Rule>, Boolean, YNMImplication, CSRProof> getTransformed(
                final Set<Rule> R,
                final Map<FunctionSymbol, ? extends Set<Integer>> replacementMap,
                final boolean innermost)
            {
                final Set<Rule> newRules = CompleteGieslMiddeldorpTransformation.transform(
                        R, replacementMap, innermost, "mark", "proper", "ok", "active", "top");

                final boolean newInnermost = true;
                return new Quadruple<Set<Rule>, Boolean, YNMImplication, CSRProof>(
                        newRules,
                        newInnermost,
                        YNMImplication.EQUIVALENT,
                        new TransformationProof(newRules, this)
                );
            }

        },


        /**
         * R^3_mu.
         * In the proof I did not see anything were we need a constant. Hence, we do not introduce a dummy constant.
         * Moreover, perhaps one can switch to version like the improved version of JFP, compare difference
         * of R^1_mu in JFP and DLT.
         */
        InnermostGieslMiddeldorp{

            @Override
            public String toString() {
                return "Innermost Giesl Middeldorp";
            }

            @Override
            public String cite(final Export_Util eu) {
                return eu.cite(Citation.CS_Inn);
            }

            @Override
            public Quadruple<Set<Rule>, Boolean, YNMImplication, CSRProof> getTransformed(
                final Set<Rule> R,
                final Map<FunctionSymbol, ? extends Set<Integer>> replacementMap,
                final boolean innermost)
            {
                final int nrOfFs = replacementMap.size();
                final FunctionSymbolGenerator funSymGen = new FunctionSymbolGenerator(nrOfFs + 2);
                final FunctionSymbol mark = funSymGen.getFresh("mark", 1);
                final FunctionSymbol active = funSymGen.getFresh("active", 1);
                final Set<Rule> newRules = new LinkedHashSet<Rule>(R.size() + nrOfFs*5);

                // add rules for original rules
                for (final Rule rule : R) {
                    newRules.add(Rule.create(
                            TRSTerm.createFunctionApplication(active, new TRSTerm[]{rule.getLeft()}),
                            TRSTerm.createFunctionApplication(mark, new TRSTerm[]{rule.getRight()})
                            ));
                }


                // add rules for signature
                for (final Map.Entry<FunctionSymbol, ? extends Set<Integer>> fRep : replacementMap.entrySet()) {
                    FunctionSymbol f = fRep.getKey();
                    final Set<Integer> replacement = fRep.getValue();
                    final int n = f.getArity();
                    f = funSymGen.getFresh(f.getName(), n);

                    final ArrayList<TRSVariable> xsList = new ArrayList<TRSVariable>(n);
                    final ArrayList<TRSTerm> xsList2 = new ArrayList<TRSTerm>(n);
                    final TRSTerm[] xsArray = new TRSTerm[n];
                    for (int i=0; i<n; i++) {
                        final TRSVariable x_i = TRSTerm.createVariable("x"+(i+1));
                        xsList.add(x_i);
                        xsArray[i] = x_i;
                        if (replacement.contains(i)) {
                            xsList2.add(TRSTerm.createFunctionApplication(mark, new TRSTerm[]{x_i}));
                        } else {
                            xsList2.add(x_i);
                        }
                    }
                    final ImmutableArrayList<TRSVariable> xs = ImmutableCreator.create(xsList);
                    final ImmutableArrayList<TRSTerm> xs2 = ImmutableCreator.create(xsList2);

                    final TRSFunctionApplication fx = TRSTerm.createFunctionApplication(f, xs);
                    final TRSFunctionApplication fx2 = TRSTerm.createFunctionApplication(f, xs2);

                    // mark -> active
                    newRules.add(Rule.create(
                            TRSTerm.createFunctionApplication(mark, new TRSTerm[]{fx}),
                            TRSTerm.createFunctionApplication(active, new TRSTerm[]{fx2})
                            ));

                    // active -> x, mark -> x
                    for (final Integer j : replacement) {
                        final int i = j;
                        final TRSTerm[] x_i = new TRSTerm[]{xsArray[i]};

                        // active -> x
                        xsArray[i] = TRSTerm.createFunctionApplication(active, x_i);
                        newRules.add(Rule.create(TRSTerm.createFunctionApplication(f, xsArray), fx));

                        // mark -> x
                        xsArray[i] = TRSTerm.createFunctionApplication(mark, x_i);
                        newRules.add(Rule.create(TRSTerm.createFunctionApplication(f, xsArray), fx));

                        // and make array x_1 to x_n again
                        xsArray[i] = x_i[0];
                    }
                }


                final boolean newInnermost = true;
                return new Quadruple<Set<Rule>, Boolean, YNMImplication, CSRProof>(
                        newRules,
                        newInnermost,
                        YNMImplication.EQUIVALENT,
                        new TransformationProof(newRules, this)
                );
            }

        };



        public abstract String cite(Export_Util eu);

        public abstract Quadruple<Set<Rule>, Boolean, YNMImplication, CSRProof> getTransformed(
            Set<Rule> R,
            Map<FunctionSymbol, ? extends Set<Integer>> replacementMap,
            boolean innermost);
    };

    /**
     * Implementation of Transformation.CompleteGieslMiddeldorp.
     *
     * <p>
     * Extracted from the Transformation enum, as usage not covered by the
     * Transformation API was needed.
     * </p>
     */
    protected static class CompleteGieslMiddeldorpTransformation {

        public static Set<Rule> transform(final Set<Rule> R, final Map<FunctionSymbol, ? extends Set<Integer>> replacementMap, final boolean innermost,
                final String markName, final String properName, final String okName, final String activeName, final String topName) {
            final int nrOfFs = replacementMap.size();
            final FunctionSymbolGenerator funSymGen = new FunctionSymbolGenerator(nrOfFs + 5);
            final FunctionSymbol mark = funSymGen.getFresh(markName, 1);
            final FunctionSymbol proper = funSymGen.getFresh(properName, 1);
            final FunctionSymbol ok = funSymGen.getFresh(okName, 1);
            final FunctionSymbol active = funSymGen.getFresh(activeName, 1);
            final FunctionSymbol top = funSymGen.getFresh(topName, 1);
            final Set<Rule> newRules = new LinkedHashSet<Rule>();



            // add active -> mark rules
            for (final Rule rule : R) {
                newRules.add(Rule.create(
                        TRSTerm.createFunctionApplication(active, new TRSTerm[]{rule.getLeft()}),
                        TRSTerm.createFunctionApplication(mark, new TRSTerm[]{rule.getRight()})));
            }

            boolean gotConstant = false;
            for (final Map.Entry<FunctionSymbol, ? extends Set<Integer>> fRep : replacementMap.entrySet()) {
                FunctionSymbol f = fRep.getKey();
                final int arity = f.getArity();
                f = funSymGen.getFresh(f.getName(), arity);
                if (arity == 0) {
                    gotConstant = true;
                    final TRSFunctionApplication c = TRSTerm.createFunctionApplication(f, TRSTerm.EMPTY_ARGS);
                    newRules.add(Rule.create(
                            TRSTerm.createFunctionApplication(proper, new TRSTerm[]{c}),
                            TRSTerm.createFunctionApplication(ok, new TRSTerm[]{c})
                    ));
                } else {

                    final ArrayList<TRSVariable> xsList = new ArrayList<TRSVariable>(arity);
                    final TRSTerm[] xsArray = new TRSTerm[arity];
                    final ArrayList<TRSTerm> xsProperList = new ArrayList<TRSTerm>(arity);
                    final ArrayList<TRSTerm> xsOkList = new ArrayList<TRSTerm>(arity);
                    for (int i = 0; i<arity; i++) {
                        final TRSVariable x_i = TRSTerm.createVariable("x"+(i+1));
                        xsList.add(x_i);
                        xsArray[i] = x_i;
                        xsProperList.add(TRSTerm.createFunctionApplication(proper, new TRSTerm[]{x_i}));
                        xsOkList.add(TRSTerm.createFunctionApplication(ok, new TRSTerm[]{x_i}));
                    }

                    final ImmutableArrayList<TRSVariable> xs = ImmutableCreator.create(xsList);

                    final TRSFunctionApplication fx = TRSTerm.createFunctionApplication(f, xs);


                    // active and mark rules
                    final TRSFunctionApplication actFx = TRSTerm.createFunctionApplication(active, new TRSTerm[]{fx});
                    final TRSFunctionApplication markFx = TRSTerm.createFunctionApplication(mark, new TRSTerm[]{fx});
                    for (final Integer j : fRep.getValue()) {
                        final int i = j;

                        final TRSTerm[] x_i = new TRSTerm[]{xsArray[i]};

                        // active
                        xsArray[i] = TRSTerm.createFunctionApplication(active, x_i);
                        newRules.add(Rule.create(actFx, TRSTerm.createFunctionApplication(f, xsArray)));

                        // mark
                        xsArray[i] = TRSTerm.createFunctionApplication(mark, x_i);
                        newRules.add(Rule.create(TRSTerm.createFunctionApplication(f, xsArray), markFx));

                        // reset
                        xsArray[i] = x_i[0];
                    }



                    // proper rules
                    final ImmutableArrayList<TRSTerm> properXs = ImmutableCreator.create(xsProperList);
                    newRules.add(Rule.create(
                            TRSTerm.createFunctionApplication(proper, new TRSTerm[]{fx}),
                            TRSTerm.createFunctionApplication(f, properXs)
                    ));

                    // ok rules
                    final ImmutableArrayList<TRSTerm> okXs = ImmutableCreator.create(xsOkList);
                    newRules.add(Rule.create(
                            TRSTerm.createFunctionApplication(f, okXs),
                            TRSTerm.createFunctionApplication(ok, new TRSTerm[]{fx})
                    ));

                }
            }

            // we must have at least one constant, use dummy constant
            if (!gotConstant) {
                final FunctionSymbol f = funSymGen.getFresh("dummy", 0);
                final TRSFunctionApplication c = TRSTerm.createFunctionApplication(f, TRSTerm.EMPTY_ARGS);
                newRules.add(Rule.create(
                        TRSTerm.createFunctionApplication(proper, new TRSTerm[]{c}),
                        TRSTerm.createFunctionApplication(ok, new TRSTerm[]{c})
                        ));
            }

            // top rules
            final TRSTerm[] x = new TRSTerm[]{TRSTerm.createVariable("x")};
            final TRSTerm markX = TRSTerm.createFunctionApplication(mark, x);
            final TRSTerm properX = TRSTerm.createFunctionApplication(proper, x);
            final TRSTerm okX = TRSTerm.createFunctionApplication(ok, x);
            final TRSTerm activeX = TRSTerm.createFunctionApplication(active, x);
            newRules.add(Rule.create(
                    TRSTerm.createFunctionApplication(top, new TRSTerm[]{markX}),
                    TRSTerm.createFunctionApplication(top, new TRSTerm[]{properX})
                    ));
            newRules.add(Rule.create(
                    TRSTerm.createFunctionApplication(top, new TRSTerm[]{okX}),
                    TRSTerm.createFunctionApplication(top, new TRSTerm[]{activeX})
                    ));


            return newRules;
        }

    }

    private static final class TransformationProof extends CSRProof {

        private final Set<Rule> rules;
        private final Transformation transformation;

        public TransformationProof(final Set<Rule> rules, final Transformation transformation) {
            final String name = transformation.toString() + "-Transformation";
            this.longName = name;
            this.shortName = name;
            this.rules = rules;
            this.transformation = transformation;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "We applied the "+this.transformation +" transformation "+
                this.transformation.cite(o)+
                " to transform the context-sensitive TRS to a usual TRS.";
        }
    }

    /**
     * very simple fresh name generator
     */
    private static final class FunctionSymbolGenerator {

        private final Set<FunctionSymbol> fs;

        public FunctionSymbolGenerator(final int size) {
            this.fs = new HashSet<FunctionSymbol>(size);
        }

        public FunctionSymbol getFresh(final String name, final int arity) {
            int j = 0;
            String currentName = name;
            FunctionSymbol f;
            while (true) {
                f = FunctionSymbol.create(currentName, arity);
                if (this.fs.add(f)) {
                    return f;
                } else {
                    currentName = name+j;
                    j++;
                }
            }
        }

    }

    public static class Arguments {
        public Transformation transformation = Transformation.Zantema;
    }

}
