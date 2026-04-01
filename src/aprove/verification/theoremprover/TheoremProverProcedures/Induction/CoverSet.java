package aprove.verification.theoremprover.TheoremProverProcedures.Induction;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Algebra.Terms.*;
import aprove.verification.oldframework.LinearArithmetic.*;
import aprove.verification.oldframework.LinearArithmetic.QuantifierEliminator.*;
import aprove.verification.oldframework.LinearArithmetic.Structure.*;
import aprove.verification.oldframework.Logic.Formulas.*;
import aprove.verification.oldframework.Logic.Formulas.Visitors.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Syntax.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * A class for a CoverSet.
 * It is created by its factory.
 * It can create an InductionScheme.
 *
 * @author dickmeis
 */

public class CoverSet implements Exportable, HTML_Able, PLAIN_Able, LaTeX_Able {

    private final List<SyntacticFunctionSymbol> functionSymbols;

    private final List<CoverSetTriple> coverSetTriples;

    private final LAProgramProperties laProgram;

    private CoverSet(final SyntacticFunctionSymbol functionSymbol, final List<CoverSetTriple> coverSetTriples,
            final LAProgramProperties laProgram) {
        this.functionSymbols = new ArrayList<SyntacticFunctionSymbol>(1);
        this.functionSymbols.add(functionSymbol);
        this.coverSetTriples = coverSetTriples;
        this.laProgram = laProgram;
    }

    private CoverSet(final List<SyntacticFunctionSymbol> functionSymbols, final List<CoverSetTriple> coverSetTriples,
            final LAProgramProperties laProgram) {
        this.functionSymbols = functionSymbols;
        this.coverSetTriples = coverSetTriples;
        this.laProgram = laProgram;
    }

    private CoverSet mergeWith(final CoverSet that, final Set<AlgebraVariable> usedVars) {
        usedVars.addAll(this.getVariables());

        that.renameVars(usedVars);

        final List<CoverSetTriple> thisCoverSetTriples = this.getCoverSetTriples();
        final List<CoverSetTriple> thatCoverSetTriples = that.getCoverSetTriples();

        final List<CoverSetTriple> coverSetTriples =
            new ArrayList<CoverSetTriple>(thisCoverSetTriples.size() * thatCoverSetTriples.size());

        for (final CoverSetTriple thisCoverSetTriple : thisCoverSetTriples) {
            for (final CoverSetTriple thatCoverSetTriple : thatCoverSetTriples) {

                // merge left args
                final List<AlgebraTerm> thisLeftArgs = thisCoverSetTriple.getLeftArguments();
                final List<AlgebraTerm> thatLeftArgs = thatCoverSetTriple.getLeftArguments();

                final ArrayList<AlgebraTerm> leftArgs = new ArrayList<AlgebraTerm>(thisLeftArgs.size() + thatLeftArgs.size());
                leftArgs.addAll(thisLeftArgs);
                leftArgs.addAll(thatLeftArgs);

                // merge conditions
                final List<Equation> thisConditions = thisCoverSetTriple.getConditions();
                final List<Equation> thatConditions = thatCoverSetTriple.getConditions();

                final ArrayList<Equation> conditions = new ArrayList<Equation>(thisConditions.size() + thatConditions.size());
                conditions.addAll(thisConditions);
                conditions.addAll(thatConditions);

                // merge recursive args
                final List<List<AlgebraTerm>> thisAllRecursiveArguments = thisCoverSetTriple.getAllRecursiveArguments();
                final List<List<AlgebraTerm>> thatAllRecursiveArguments = thatCoverSetTriple.getAllRecursiveArguments();

                List<List<AlgebraTerm>> allRecursiveArguments = null;

                if (thisAllRecursiveArguments.isEmpty() && thatAllRecursiveArguments.isEmpty()) {
                    allRecursiveArguments = new ArrayList<List<AlgebraTerm>>();
                } else if (thisAllRecursiveArguments.isEmpty() && !thatAllRecursiveArguments.isEmpty()) {
                    allRecursiveArguments = new ArrayList<List<AlgebraTerm>>(thatAllRecursiveArguments.size());
                    for (final List<AlgebraTerm> thatRecursiveArguments : thatAllRecursiveArguments) {
                        final ArrayList<AlgebraTerm> recArgs =
                            new ArrayList<AlgebraTerm>(thisLeftArgs.size() + thatRecursiveArguments.size());
                        recArgs.addAll(thisLeftArgs);
                        recArgs.addAll(thatRecursiveArguments);
                        allRecursiveArguments.add(recArgs);
                    }
                } else if (!thisAllRecursiveArguments.isEmpty() && thatAllRecursiveArguments.isEmpty()) {
                    allRecursiveArguments = new ArrayList<List<AlgebraTerm>>(thisAllRecursiveArguments.size());
                    for (final List<AlgebraTerm> thisRecursiveArguments : thisAllRecursiveArguments) {
                        final ArrayList<AlgebraTerm> recArgs =
                            new ArrayList<AlgebraTerm>(thisRecursiveArguments.size() + thatLeftArgs.size());
                        recArgs.addAll(thisRecursiveArguments);
                        recArgs.addAll(thatLeftArgs);
                        allRecursiveArguments.add(recArgs);
                    }
                } else if (!thisAllRecursiveArguments.isEmpty() && !thatAllRecursiveArguments.isEmpty()) {
                    allRecursiveArguments =
                        new ArrayList<List<AlgebraTerm>>(thisAllRecursiveArguments.size() * thatAllRecursiveArguments.size());
                    for (final List<AlgebraTerm> thisRecursiveArguments : thisAllRecursiveArguments) {
                        for (final List<AlgebraTerm> thatRecursiveArguments : thatAllRecursiveArguments) {
                            final ArrayList<AlgebraTerm> recArgs =
                                new ArrayList<AlgebraTerm>(thisRecursiveArguments.size() + thatRecursiveArguments.size());
                            recArgs.addAll(thisRecursiveArguments);
                            recArgs.addAll(thatRecursiveArguments);
                            allRecursiveArguments.add(recArgs);
                        }
                    }
                }

                final CoverSetTriple cst = new CoverSetTriple(leftArgs, allRecursiveArguments, conditions);
                coverSetTriples.add(cst);
            }
        }

        final List<SyntacticFunctionSymbol> funcSymbys = this.getFunctionSymbols();
        funcSymbys.addAll(that.getFunctionSymbols());

        final CoverSet cs = new CoverSet(funcSymbys, coverSetTriples, this.laProgram);
        return cs;
    }

    private List<SyntacticFunctionSymbol> getFunctionSymbols() {
        return this.functionSymbols;
    }

    private void renameVars(final Set<AlgebraVariable> usedVariables) {

        final FreshVarGenerator fg = new FreshVarGenerator(usedVariables);

        for (final CoverSetTriple thisCoverSetTriple : this.getCoverSetTriples()) {
            final List<AlgebraTerm> leftArgs = thisCoverSetTriple.getLeftArguments();
            for (final AlgebraTerm term : leftArgs) {
                term.renameVars(fg);
            }

            final List<List<AlgebraTerm>> allRecursiveArguments = thisCoverSetTriple.getAllRecursiveArguments();
            for (final List<AlgebraTerm> recArgs : allRecursiveArguments) {
                for (final AlgebraTerm term : recArgs) {
                    term.renameVars(fg);
                }
            }

            final List<Equation> conditions = thisCoverSetTriple.getConditions();
            for (final Equation equation : conditions) {
                equation.renameVars(fg);
            }
        }
    }

    public static InductionScheme generateMergedInductionScheme(List<Pair<AlgebraTerm, Position>> termsWithPosition,
        final boolean useLA,
        final Set<AlgebraVariable> usedVars,
        final Program program,
        final boolean skipLAHypothesisHeuristic) {

        if (termsWithPosition.isEmpty()) {
            return null;
        }

        int counter = 6;
        final List<Pair<AlgebraTerm, Position>> cutTermsWithPosition = new ArrayList<Pair<AlgebraTerm, Position>>(counter);
        for (final Pair<AlgebraTerm, Position> pair : termsWithPosition) {
            cutTermsWithPosition.add(pair);
            counter--;
            if (counter <= 0) {
                break;
            }
        }
        termsWithPosition = cutTermsWithPosition;

        // collect all arguments
        // needed for unification afterwards
        final List<AlgebraTerm> termargs = new ArrayList<AlgebraTerm>();
        for (final Pair<AlgebraTerm, Position> pair : termsWithPosition) {
            termargs.addAll(pair.x.getArguments());
        }

        // merge CoverSets
        CoverSet cs = null;
        for (final Pair<AlgebraTerm, Position> pair : termsWithPosition) {
            assert (pair.x instanceof DefFunctionApp);
            final DefFunctionApp term = (DefFunctionApp) pair.x;
            final SyntacticFunctionSymbol termFunctionSymbol = term.getFunctionSymbol();

            final CoverSet termCoverSet = CoverSet.createCoverSet(termFunctionSymbol, usedVars, program);

            if (cs == null) {
                cs = termCoverSet;
            } else {
                final CoverSet newcs = cs.mergeWith(termCoverSet, usedVars);
                cs = newcs;
            }
        }

        final LAProgramProperties laProgram = cs.laProgram;

        if (useLA && laProgram == null) {
            // error
            return null;
        }

        final Set<AlgebraVariable> tVars = new HashSet<AlgebraVariable>();
        boolean termIsConstructorTerm = true;
        for (final AlgebraTerm t : termargs) {
            tVars.addAll(t.getVars());
            termIsConstructorTerm = termIsConstructorTerm && t.isConstructorTerm();
        }

        final List<CoverSetTriple> coverSetTriples = cs.getCoverSetTriples();

        ArrayList<InductionSchemeComponent> inductionSchemeComponents;
        inductionSchemeComponents = new ArrayList<InductionSchemeComponent>(coverSetTriples.size());

        cst: for (final CoverSetTriple cst : coverSetTriples) {

            List<Equation> cstConditions;

            AlgebraSubstitution sigma;
            AlgebraSubstitution sigma_c;
            List<Equation> cond_c;

            List<Dissolving> sigmaDissolving = null;
            List<Dissolving> mhyDissolving = null;
            List<LinearConstraint> c_c = null;

            /*
             * generate induction conclusion
             */

            cstConditions = cst.getConditions();

            final List<AlgebraTerm> sArgs = cst.getLeftArguments();

            if (useLA) {
                boolean satisfiable;

                // we want to dissolve for the variables from the induction term
                ArrayList<AlgebraVariable> variableOrdering = new ArrayList<AlgebraVariable>();
                for (final AlgebraTerm t : termargs) {
                    variableOrdering.addAll(t.getVars());
                }
                LASolver las = new LASolver(variableOrdering);

                // generate and add constraint equations
                final List<AlgebraTerm> tArgs = termargs;
                int size = tArgs.size();
                for (int i = 0; i < size; i++) {
                    final AlgebraTerm ti = tArgs.get(i);
                    final AlgebraTerm si = sArgs.get(i);
                    final LinearConstraint ce = LinearConstraint.createEquation(ti, si, laProgram);
                    las.addConstraint(ce);
                }

                // add conditions
                for (final Equation eq : cstConditions) {

                    final LinearConstraint constraint = LinearConstraint.create(eq, laProgram);

                    las.addConstraint(constraint);
                }

                satisfiable = las.solve();
                if (!satisfiable) {
                    // vacuous induction case
                    continue;
                }

                final ArrayList<Dissolving> dissolvings = las.getDissolvings();
                final ArrayList<LinearConstraint> allConstraints = las.getAllConstraints();

                final List<Pair<List<LinearConstraint>, List<Dissolving>>> pairs =
                    NaturalEnumerator.enumerate(allConstraints, dissolvings, variableOrdering);

                for (final Pair<List<LinearConstraint>, List<Dissolving>> pair : pairs) {

                    c_c = pair.x;
                    sigmaDissolving = pair.y;
                    sigma = LinearIntegerHelper.toSubstitution(sigmaDissolving, laProgram);

                    sigma_c = sigma.restrictTo(tVars);

                    final Set<AlgebraVariable> cstVars = cst.getVariables();
                    mhyDissolving = CoverSet.restrictTo(sigmaDissolving, cstVars);

                    // because of our LA solver algorithm
                    // we do not need to apply mhy to the constraints

                    cond_c = new ArrayList<Equation>(c_c.size());
                    for (final LinearConstraint constraint : c_c) {
                        final Equation eq = LinearIntegerHelper.toEquation(constraint, laProgram);
                        cond_c.add(eq);
                    }

                    final List<Pair<Position, AlgebraTerm>> replacement_c =
                        new ArrayList<Pair<Position, AlgebraTerm>>(termsWithPosition.size());

                    int argIndex = 0;
                    for (final Pair<AlgebraTerm, Position> termWithPosition : termsWithPosition) {

                        AlgebraTerm s_sigma = null;
                        final AlgebraTerm term = termWithPosition.x;
                        if (term instanceof AlgebraFunctionApplication) {
                            final AlgebraFunctionApplication fterm = (AlgebraFunctionApplication) term;
                            final SyntacticFunctionSymbol functionSymbol = fterm.getFunctionSymbol();

                            final int arity = fterm.getArguments().size();
                            final int newargIndex = argIndex + arity;

                            final List<AlgebraTerm> actualsArgs = new ArrayList<AlgebraTerm>(arity);

                            // collect args
                            for (int i = argIndex; i < newargIndex; i++) {
                                actualsArgs.add(sArgs.get(i));
                            }

                            argIndex = newargIndex;

                            final AlgebraTerm s = AlgebraFunctionApplication.create(functionSymbol, actualsArgs);

                            s_sigma = s.apply(sigma);
                        }

                        replacement_c.add(new Pair<Position, AlgebraTerm>(termWithPosition.y, s_sigma));

                    }

                    InductionSchemeTupel conclusion;
                    conclusion = new InductionSchemeTupel(sigma_c, cond_c, replacement_c);

                    /*
                     * generate induction hypotheses
                     */
                    final List<List<AlgebraTerm>> allRecursiveArguments = cst.getAllRecursiveArguments();
                    ArrayList<InductionSchemeTupel> hypotheses;
                    hypotheses = new ArrayList<InductionSchemeTupel>(allRecursiveArguments.size());

                    for (final List<AlgebraTerm> siArgs : allRecursiveArguments) {
                        AlgebraSubstitution sigma_i;
                        AlgebraSubstitution sigma_c_i;
                        List<Equation> cond_c_i;

                        // just for LA
                        ArrayList<LinearConstraint> c_c_i = null;

                        // we want to dissolve for the variables from the induction term
                        variableOrdering = new ArrayList<AlgebraVariable>(tVars);
                        variableOrdering.addAll(sigma.getTermDomain());
                        las = new LASolver(variableOrdering);

                        // generate and add constraint equations
                        size = tArgs.size();
                        for (int i = 0; i < size; i++) {
                            final AlgebraTerm ti = tArgs.get(i);
                            final AlgebraTerm si = siArgs.get(i);
                            final LinearConstraint ce = LinearConstraint.createEquation(ti, si, laProgram);
                            las.addConstraint(ce);
                        }

                        // add conditions
                        if (skipLAHypothesisHeuristic) {
                            for (final Equation eq : cond_c) {
                                // because of the builder they have the form (linear condition = true)
                                // so we take only the left side
                                final AlgebraTerm left = eq.getLeft();
                                las.addConstraint(left, laProgram);
                            }

                            for (final Dissolving dissolving : mhyDissolving) {
                                final LinearConstraint eq = dissolving.toEquation();
                                las.addConstraint(eq);
                            }
                        } else {
                            for (final Equation eq : cstConditions) {

                                final LinearConstraint constraint = LinearConstraint.create(eq, laProgram);

                                las.addConstraint(constraint);
                            }
                        }

                        satisfiable = las.solve();
                        if (!satisfiable) {
                            // no induction hypothesis
                            continue;
                        }

                        sigma_i = LinearIntegerHelper.toSubstitution(las.getDissolvings(), laProgram);
                        c_c_i = las.getAllConstraints();

                        sigma_c_i = sigma_i.restrictTo(tVars);

                        //                        cstConditions = cst.getConditions();

                        // because of our LA solver algorithm
                        // we do not need to apply mhy to the constraints

                        cond_c_i = new ArrayList<Equation>(c_c_i.size());
                        for (final LinearConstraint constraint : c_c_i) {
                            final Equation eq = LinearIntegerHelper.toEquation(constraint, laProgram);
                            cond_c_i.add(eq);
                        }

                        final List<Pair<Position, AlgebraTerm>> replacement_i =
                            new ArrayList<Pair<Position, AlgebraTerm>>(termsWithPosition.size());

                        argIndex = 0;
                        for (final Pair<AlgebraTerm, Position> termWithPosition : termsWithPosition) {

                            AlgebraTerm s_i_sigma = null;
                            final AlgebraTerm term = termWithPosition.x;
                            if (term instanceof AlgebraFunctionApplication) {
                                final AlgebraFunctionApplication fterm = (AlgebraFunctionApplication) term;
                                final SyntacticFunctionSymbol functionSymbol = fterm.getFunctionSymbol();

                                final int arity = fterm.getArguments().size();
                                final int newargIndex = argIndex + arity;

                                final List<AlgebraTerm> actualsArgs = new ArrayList<AlgebraTerm>(arity);

                                // collect args
                                for (int i = argIndex; i < newargIndex; i++) {
                                    actualsArgs.add(siArgs.get(i));
                                }

                                argIndex = newargIndex;

                                final AlgebraTerm s_i = AlgebraFunctionApplication.create(functionSymbol, actualsArgs);

                                s_i_sigma = s_i.apply(sigma_i);
                            }

                            replacement_i.add(new Pair<Position, AlgebraTerm>(termWithPosition.y, s_i_sigma));

                        }

                        InductionSchemeTupel hypothesis;
                        hypothesis = new InductionSchemeTupel(sigma_c_i, cond_c_i, replacement_i);
                        hypotheses.add(hypothesis);
                    }

                    final InductionSchemeComponent isc = new InductionSchemeComponent(conclusion, hypotheses);
                    inductionSchemeComponents.add(isc);
                }
            } else {
                // not LA
                final int mergedCoverSetArity = termargs.size();
                sigma = AlgebraSubstitution.create();
                for (int i = 0; i < mergedCoverSetArity; i++) {
                    final AlgebraTerm t_i = termargs.get(i);
                    final AlgebraTerm s_i = sArgs.get(i);
                    try {
                        sigma = t_i.unifies(s_i, sigma);
                    } catch (final UnificationException e) {
                        if (termIsConstructorTerm && cs.isConstructorBased()) {
                            // no induction case is generated
                            continue cst;
                        } else {
                            return null;
                        }
                    }
                }

                sigma_c = sigma.restrictTo(tVars);

                cond_c = new ArrayList<Equation>(cstConditions.size());
                for (final Equation eq : cstConditions) {
                    final Equation eq_prime = (Equation) eq.apply(sigma);
                    cond_c.add(eq_prime);
                }

                final List<Pair<Position, AlgebraTerm>> replacement_c =
                    new ArrayList<Pair<Position, AlgebraTerm>>(termsWithPosition.size());

                int argIndex = 0;
                for (final Pair<AlgebraTerm, Position> termWithPosition : termsWithPosition) {

                    AlgebraTerm s_sigma = null;
                    final AlgebraTerm term = termWithPosition.x;
                    if (term instanceof AlgebraFunctionApplication) {
                        final AlgebraFunctionApplication fterm = (AlgebraFunctionApplication) term;
                        final SyntacticFunctionSymbol functionSymbol = fterm.getFunctionSymbol();

                        final int arity = fterm.getArguments().size();
                        final int newargIndex = argIndex + arity;

                        final List<AlgebraTerm> actualsArgs = new ArrayList<AlgebraTerm>(arity);

                        // collect args
                        for (int i = argIndex; i < newargIndex; i++) {
                            actualsArgs.add(sArgs.get(i));
                        }

                        argIndex = newargIndex;

                        final AlgebraTerm s = AlgebraFunctionApplication.create(functionSymbol, actualsArgs);

                        s_sigma = s.apply(sigma);
                    }

                    replacement_c.add(new Pair<Position, AlgebraTerm>(termWithPosition.y, s_sigma));

                }

                InductionSchemeTupel conclusion;
                conclusion = new InductionSchemeTupel(sigma_c, cond_c, replacement_c);

                /*
                 * generate induction hypotheses
                 */
                final List<List<AlgebraTerm>> allRecursiveArguments = cst.getAllRecursiveArguments();
                ArrayList<InductionSchemeTupel> hypotheses;
                hypotheses = new ArrayList<InductionSchemeTupel>(allRecursiveArguments.size());

                hypo: for (final List<AlgebraTerm> siArgs : allRecursiveArguments) {
                    List<Equation> cond_c_i;

                    AlgebraSubstitution sigma_i = AlgebraSubstitution.create();
                    for (int i = 0; i < mergedCoverSetArity; i++) {
                        final AlgebraTerm t_i = termargs.get(i);
                        final AlgebraTerm s_i = siArgs.get(i);
                        try {
                            sigma_i = t_i.unifies(s_i, sigma);
                        } catch (final UnificationException e) {
                            if (termIsConstructorTerm && cs.isConstructorBased()) {
                                // no induction hypothesis is generated
                                continue hypo;
                            } else {
                                return null;
                            }
                        }
                    }

                    final AlgebraSubstitution sigma_c_i = sigma_i.restrictTo(tVars);

                    cstConditions = cst.getConditions();

                    cond_c_i = new ArrayList<Equation>(cstConditions.size());
                    for (final Equation eq : cstConditions) {
                        final Equation eq_prime = (Equation) eq.apply(sigma);
                        cond_c_i.add(eq_prime);
                    }

                    final List<Pair<Position, AlgebraTerm>> replacement_i =
                        new ArrayList<Pair<Position, AlgebraTerm>>(termsWithPosition.size());

                    argIndex = 0;
                    for (final Pair<AlgebraTerm, Position> termWithPosition : termsWithPosition) {

                        AlgebraTerm s_i_sigma_i = null;
                        final AlgebraTerm term = termWithPosition.x;
                        if (term instanceof AlgebraFunctionApplication) {
                            final AlgebraFunctionApplication fterm = (AlgebraFunctionApplication) term;
                            final SyntacticFunctionSymbol functionSymbol = fterm.getFunctionSymbol();

                            final int arity = fterm.getArguments().size();
                            final int newargIndex = argIndex + arity;

                            final List<AlgebraTerm> actualsArgs = new ArrayList<AlgebraTerm>(arity);

                            // collect args
                            for (int i = argIndex; i < newargIndex; i++) {
                                actualsArgs.add(siArgs.get(i));
                            }

                            argIndex = newargIndex;

                            final AlgebraTerm s_i = AlgebraFunctionApplication.create(functionSymbol, actualsArgs);

                            s_i_sigma_i = s_i.apply(sigma_i);
                        }

                        replacement_i.add(new Pair<Position, AlgebraTerm>(termWithPosition.y, s_i_sigma_i));

                    }

                    InductionSchemeTupel hypothesis;
                    hypothesis = new InductionSchemeTupel(sigma_c_i, cond_c_i, replacement_i);
                    hypotheses.add(hypothesis);

                }

                final InductionSchemeComponent isc = new InductionSchemeComponent(conclusion, hypotheses);
                inductionSchemeComponents.add(isc);
            }

        }

        return new InductionScheme(inductionSchemeComponents);

    }

    /**
     * Generates an induction scheme for a term.
     * It can be said whether the LA decision procedure should be used.
     *
     * @param t The term the induction scheme should be generated for.
     * @param pos The position the term stands at.
     * @param useLA specifies whether the LA decision procedure should be used.
     *
     * @return The induction scheme, null if an error has occured
     */
    public InductionScheme generateInductionScheme(final AlgebraTerm t, final Position pos, final boolean useLA) {

        if (this.functionSymbols.size() != 1) {
            return null;
        }

        if (useLA && this.laProgram == null) {
            // error
            return null;
        }

        final boolean termIsConstructorTerm = t.isConstructorTerm();

        ArrayList<InductionSchemeComponent> inductionSchemeComponents;
        inductionSchemeComponents = new ArrayList<InductionSchemeComponent>(this.coverSetTriples.size());

        cst: for (final CoverSetTriple cst : this.coverSetTriples) {

            List<Equation> cstConditions;

            AlgebraSubstitution sigma;
            AlgebraSubstitution sigma_c;
            List<Equation> cond_c;
            AlgebraTerm s;
            AlgebraTerm s_sigma;

            List<Dissolving> sigmaDissolving = null;
            List<Dissolving> mhyDissolving = null;
            List<LinearConstraint> c_c = null;

            /*
             * generate induction conclusion
             */

            cstConditions = cst.getConditions();

            final List<AlgebraTerm> sArgs = cst.getLeftArguments();
            s = AlgebraFunctionApplication.create(this.functionSymbols.get(0), sArgs);

            if (useLA) {
                boolean satisfiable;

                // we want to dissolve for the variables from the induction term
                ArrayList<AlgebraVariable> variableOrdering = new ArrayList<AlgebraVariable>(t.getVars());
                LASolver las = new LASolver(variableOrdering);

                // generate and add constraint equations
                List<AlgebraTerm> tArgs = t.getArguments();
                int size = tArgs.size();
                for (int i = 0; i < size; i++) {
                    final AlgebraTerm ti = tArgs.get(i);
                    final AlgebraTerm si = sArgs.get(i);
                    final LinearConstraint ce = LinearConstraint.createEquation(ti, si, this.laProgram);
                    las.addConstraint(ce);
                }

                // add conditions
                for (final Equation eq : cstConditions) {

                    final LinearConstraint constraint = LinearConstraint.create(eq, this.laProgram);

                    las.addConstraint(constraint);
                }

                satisfiable = las.solve();
                if (!satisfiable) {
                    // vacuous induction case
                    continue;
                }

                final ArrayList<Dissolving> dissolvings = las.getDissolvings();
                final ArrayList<LinearConstraint> allConstraints = las.getAllConstraints();

                final List<Pair<List<LinearConstraint>, List<Dissolving>>> pairs =
                    NaturalEnumerator.enumerate(allConstraints, dissolvings, variableOrdering);

                for (final Pair<List<LinearConstraint>, List<Dissolving>> pair : pairs) {

                    c_c = pair.x;
                    sigmaDissolving = pair.y;
                    sigma = LinearIntegerHelper.toSubstitution(sigmaDissolving, this.laProgram);

                    sigma_c = sigma.restrictTo(t.getVars());

                    final Set<AlgebraVariable> cstVars = cst.getVariables();
                    mhyDissolving = CoverSet.restrictTo(sigmaDissolving, cstVars);

                    // because of our LA solver algorithm
                    // we do not need to apply mhy to the constraints

                    cond_c = new ArrayList<Equation>(c_c.size());
                    for (final LinearConstraint constraint : c_c) {
                        final Equation eq = LinearIntegerHelper.toEquation(constraint, this.laProgram);
                        cond_c.add(eq);
                    }

                    s_sigma = s.apply(sigma);

                    final List<Pair<Position, AlgebraTerm>> replacement_c = new ArrayList<Pair<Position, AlgebraTerm>>(1);
                    replacement_c.add(new Pair<Position, AlgebraTerm>(pos, s_sigma));

                    InductionSchemeTupel conclusion;
                    conclusion = new InductionSchemeTupel(sigma_c, cond_c, replacement_c);

                    /*
                     * generate induction hypotheses
                     */
                    final List<List<AlgebraTerm>> allRecursiveArguments = cst.getAllRecursiveArguments();
                    ArrayList<InductionSchemeTupel> hypotheses;
                    hypotheses = new ArrayList<InductionSchemeTupel>(allRecursiveArguments.size());

                    for (final List<AlgebraTerm> siArgs : allRecursiveArguments) {
                        AlgebraSubstitution sigma_i;
                        AlgebraSubstitution sigma_c_i;
                        final AlgebraTerm s_i = AlgebraFunctionApplication.create(this.functionSymbols.get(0), siArgs);
                        AlgebraTerm s_i_sigma_i;
                        List<Equation> cond_c_i;

                        // just for LA
                        ArrayList<LinearConstraint> c_c_i = null;

                        // we want to dissolve for the variables from the induction term
                        variableOrdering = new ArrayList<AlgebraVariable>(t.getVars());
                        las = new LASolver(variableOrdering);

                        // generate and add constraint equations
                        tArgs = t.getArguments();
                        size = tArgs.size();
                        for (int i = 0; i < size; i++) {
                            final AlgebraTerm ti = tArgs.get(i);
                            final AlgebraTerm si = siArgs.get(i);
                            final LinearConstraint ce = LinearConstraint.createEquation(ti, si, this.laProgram);
                            las.addConstraint(ce);
                        }

                        // add conditions
                        for (final Equation eq : cond_c) {
                            // because of the builder they have the form (linear condition = true)
                            // so we take only the left side
                            final AlgebraTerm left = eq.getLeft();
                            las.addConstraint(left, this.laProgram);
                        }

                        for (final Dissolving dissolving : mhyDissolving) {
                            final LinearConstraint eq = dissolving.toEquation();
                            las.addConstraint(eq);
                        }

                        satisfiable = las.solve();
                        if (!satisfiable) {
                            // no induction hypothesis
                            continue;
                        }

                        sigma_i = LinearIntegerHelper.toSubstitution(las.getDissolvings(), this.laProgram);
                        c_c_i = las.getAllConstraints();

                        sigma_c_i = sigma_i.restrictTo(t.getVars());

                        cstConditions = cst.getConditions();

                        // because of our LA solver algorithm
                        // we do not need to apply mhy to the constraints

                        cond_c_i = new ArrayList<Equation>(c_c_i.size());
                        for (final LinearConstraint constraint : c_c_i) {
                            final Equation eq = LinearIntegerHelper.toEquation(constraint, this.laProgram);
                            cond_c_i.add(eq);
                        }

                        s_i_sigma_i = s_i.apply(sigma_i);

                        final List<Pair<Position, AlgebraTerm>> replacement_i = new ArrayList<Pair<Position, AlgebraTerm>>(1);
                        replacement_i.add(new Pair<Position, AlgebraTerm>(pos, s_i_sigma_i));

                        InductionSchemeTupel hypothesis;
                        hypothesis = new InductionSchemeTupel(sigma_c_i, cond_c_i, replacement_i);
                        hypotheses.add(hypothesis);
                    }

                    final InductionSchemeComponent isc = new InductionSchemeComponent(conclusion, hypotheses);
                    inductionSchemeComponents.add(isc);
                }
            } else {
                // not LA

                try {
                    sigma = t.unifies(s);
                } catch (final UnificationException e) {
                    if (termIsConstructorTerm && this.isConstructorBased()) {
                        // no induction case is generated
                        continue cst;
                    } else {
                        return null;
                    }
                }

                sigma_c = sigma.restrictTo(t.getVars());

                cond_c = new ArrayList<Equation>(cstConditions.size());
                for (final Equation eq : cstConditions) {
                    final Equation eq_prime = (Equation) eq.apply(sigma);
                    cond_c.add(eq_prime);
                }

                s_sigma = s.apply(sigma);

                final List<Pair<Position, AlgebraTerm>> replacement_c = new ArrayList<Pair<Position, AlgebraTerm>>(1);
                replacement_c.add(new Pair<Position, AlgebraTerm>(pos, s_sigma));

                InductionSchemeTupel conclusion;
                conclusion = new InductionSchemeTupel(sigma_c, cond_c, replacement_c);

                /*
                 * generate induction hypotheses
                 */
                final List<List<AlgebraTerm>> allRecursiveArguments = cst.getAllRecursiveArguments();
                ArrayList<InductionSchemeTupel> hypotheses;
                hypotheses = new ArrayList<InductionSchemeTupel>(allRecursiveArguments.size());

                hypo: for (final List<AlgebraTerm> siArgs : allRecursiveArguments) {
                    AlgebraSubstitution sigma_i;
                    AlgebraSubstitution sigma_c_i;
                    final AlgebraTerm s_i = AlgebraFunctionApplication.create(this.functionSymbols.get(0), siArgs);
                    AlgebraTerm s_i_sigma_i;
                    List<Equation> cond_c_i;

                    try {
                        sigma_i = t.unifies(s_i);
                    } catch (final UnificationException e) {
                        if (termIsConstructorTerm && this.isConstructorBased()) {
                            // no induction hypothesis is generated
                            continue hypo;
                        } else {
                            return null;
                        }
                    }

                    sigma_c_i = sigma_i.restrictTo(t.getVars());

                    cstConditions = cst.getConditions();

                    cond_c_i = new ArrayList<Equation>(cstConditions.size());
                    for (final Equation eq : cstConditions) {
                        final Equation eq_prime = (Equation) eq.apply(sigma);
                        cond_c_i.add(eq_prime);
                    }

                    s_i_sigma_i = s_i.apply(sigma_i);

                    final List<Pair<Position, AlgebraTerm>> replacement_i = new ArrayList<Pair<Position, AlgebraTerm>>(1);
                    replacement_i.add(new Pair<Position, AlgebraTerm>(pos, s_i_sigma_i));

                    InductionSchemeTupel hypothesis;
                    hypothesis = new InductionSchemeTupel(sigma_c_i, cond_c_i, replacement_i);
                    hypotheses.add(hypothesis);
                }

                final InductionSchemeComponent isc = new InductionSchemeComponent(conclusion, hypotheses);
                inductionSchemeComponents.add(isc);
            }

        }

        return new InductionScheme(inductionSchemeComponents);

    }

    /**
     * Restricts a list of dissolvings to some variables.
     * Like the restriction of a sustitution.
     *
     * @param dissolvings The dissolvings to restrict
     * @param variables The new domain.
     * @return A list of dissolvings only for the given variables.
     */
    private static List<Dissolving> restrictTo(final List<Dissolving> dissolvings, final Set<AlgebraVariable> variables) {
        final List<Dissolving> restricted = new ArrayList<Dissolving>(dissolvings.size());

        for (final Dissolving dissolving : dissolvings) {
            if (variables.contains(dissolving.getVariable())) {
                restricted.add(dissolving);
            }
        }

        return restricted;
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();

        if (this.functionSymbols.size() == 1) {
            sb.append("CoverSet for ");
            sb.append(this.functionSymbols.get(0));
        } else {
            sb.append("Merged CoverSet for ");
            sb.append(this.functionSymbols);
        }

        for (final CoverSetTriple cst : this.coverSetTriples) {
            sb.append("\n");
            sb.append(cst);
        }

        return sb.toString();
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder sb = new StringBuilder();

        if (this.functionSymbols.size() == 1) {
            sb.append("CoverSet for ");
            sb.append(this.functionSymbols.get(0));
        } else {
            sb.append("Merged CoverSet for ");
            sb.append(o.set(this.functionSymbols, 0));
        }

        sb.append(o.set(this.coverSetTriples, 3));

        return sb.toString();
    }

    /**
     * Creates a cover for a function symbol from the program.
     * Certain variables will not be used.
     *
     * @param functionSymbol The function for which the cover set should be created
     * @param usedVars The used variables which must not be used in the cover set.
     * @param program
     *
     * @return The created cover set
     */
    public static CoverSet createCoverSet(final SyntacticFunctionSymbol functionSymbol,
        final Set<AlgebraVariable> usedVars,
        final Program program) {

        final List<CoverSetTriple> coverSetTriples = new ArrayList<CoverSetTriple>();

        for (final Rule r : program.getRules(functionSymbol)) {

            final Rule rule = r.replaceVariables(usedVars);

            final List<AlgebraTerm> argumentsL = rule.getLeft().getArguments();
            if (argumentsL == null) {
                return null;
            }

            final List<List<AlgebraTerm>> allArgumentsR = new ArrayList<List<AlgebraTerm>>();

            /*
             * get all arguments of recursive calls
             */
            for (final AlgebraTerm subTerm : rule.getRight().getAllSubterms()) {
                List<AlgebraTerm> argumentsR = null;
                final Symbol sts = subTerm.getSymbol();
                if (sts instanceof SyntacticFunctionSymbol && sts.equals(functionSymbol)) {
                    argumentsR = subTerm.getArguments();
                    if (argumentsR != null) {
                        allArgumentsR.add(argumentsR);
                    }
                }
            }

            final List<Rule> conds = rule.getConds();
            final List<Equation> condsEq = new ArrayList<Equation>(conds.size());

            for (final Rule condRule : conds) {
                final AlgebraTerm left = condRule.getLeft();
                final AlgebraTerm right = condRule.getRight();

                final Equation eq = Equation.create(left, right);

                condsEq.add(eq);
            }

            final CoverSetTriple cst = new CoverSetTriple(argumentsL, allArgumentsR, condsEq);
            coverSetTriples.add(cst);
        }

        return new CoverSet(functionSymbol, coverSetTriples, program.laProgramProperties);

    }

    public CoverSet deepcopy() {
        final List<CoverSetTriple> newCoverSetTriples = new ArrayList<CoverSetTriple>(this.coverSetTriples.size());
        for (final CoverSetTriple triple : this.coverSetTriples) {
            newCoverSetTriples.add(triple.deepcopy());
        }

        final List<SyntacticFunctionSymbol> newFunctionSymbols = new ArrayList<SyntacticFunctionSymbol>(this.functionSymbols.size());
        for (final SyntacticFunctionSymbol symbol : this.functionSymbols) {
            newFunctionSymbols.add((SyntacticFunctionSymbol) symbol.deepcopy());
        }

        return new CoverSet(newFunctionSymbols, newCoverSetTriples, this.laProgram);
    }

    @Override
    public String toLaTeX() {
        return this.export(new LaTeX_Util());
    }

    @Override
    public String toHTML() {
        return this.export(new HTML_Util());
    }

    @Override
    public String toPLAIN() {
        return this.export(new PLAIN_Util());
    }

    /**
     * Returns all Variables occuring in this cover set
     *
     * @return all Variables of this cover set
     */
    public Set<AlgebraVariable> getVariables() {
        final Set<AlgebraVariable> vars = new HashSet<AlgebraVariable>();

        for (final CoverSetTriple cst : this.coverSetTriples) {
            vars.addAll(cst.getVariables());
        }

        return vars;
    }

    /**
     * States whether the cover set is constructor based.
     *
     * @return true iff the cover set constructor LA based
     */
    public boolean isConstructorBased() {
        for (final CoverSetTriple cst : this.coverSetTriples) {

            final List<AlgebraTerm> args = cst.getLeftArguments();
            for (final AlgebraTerm term : args) {
                final Set<SyntacticFunctionSymbol> fss = term.getFunctionSymbols();
                for (final SyntacticFunctionSymbol symbol : fss) {
                    if (symbol instanceof DefFunctionSymbol) {
                        return false;
                    }
                }
            }

            for (final List<AlgebraTerm> recCalls : cst.getAllRecursiveArguments()) {
                for (final AlgebraTerm term : recCalls) {
                    final Set<SyntacticFunctionSymbol> fss = term.getFunctionSymbols();
                    for (final SyntacticFunctionSymbol symbol : fss) {
                        if (symbol instanceof DefFunctionSymbol) {
                            return false;
                        }
                    }
                }
            }

        }

        return true;
    }

    /**
     * States whether the cover set is LA based.
     * Iff the cover set for a function symbol is LA based
     * the function symbol has got an LA based function definition.
     *
     * @return true iff the cover set is LA based
     */
    public boolean isLABased() {
        for (final CoverSetTriple cst : this.coverSetTriples) {

            final List<AlgebraTerm> args = cst.getLeftArguments();
            for (final AlgebraTerm term : args) {

                final LinearTermNormalizer ltn = new LinearTermNormalizer(this.laProgram);
                term.apply(ltn);

                if (!ltn.isLinearTerm()) {
                    return false;
                }
            }

            for (final List<AlgebraTerm> recCalls : cst.getAllRecursiveArguments()) {
                for (final AlgebraTerm term : recCalls) {
                    final LinearTermNormalizer ltn = new LinearTermNormalizer(this.laProgram);
                    term.apply(ltn);

                    if (!ltn.isLinearTerm()) {
                        return false;
                    }
                }
            }

            for (final Equation eq : cst.getConditions()) {

                final LinearConstraint constraint = LinearConstraint.create(eq, this.laProgram);

                if (constraint == null) {
                    return false;
                }
            }

        }

        return true;
    }

    /**
     * States whether the cover set is semi LA based.
     * Iff the cover set for a function symbol is LA based
     * the function symbol has got an LA based function definition.
     *
     * @return true iff the cover set is LA based
     */
    public boolean isSemiLABased() {
        for (final CoverSetTriple cst : this.coverSetTriples) {

            final List<AlgebraTerm> args = cst.getLeftArguments();
            for (final AlgebraTerm term : args) {

                final LinearTermNormalizer ltn = new LinearTermNormalizer(this.laProgram);
                term.apply(ltn);

                if (!ltn.isLinearTerm()) {
                    return false;
                }
            }

            for (final Equation eq : cst.getConditions()) {

                final LinearConstraint constraint = LinearConstraint.create(eq, this.laProgram);

                if (constraint == null) {
                    return false;
                }
            }

        }

        return true;
    }

    /**
     * States whether the function corresponding to the cover set
     * uses plus in the left hand of a rule.
     *
     * @return true iff the function uses plus in the lhs
     */
    public boolean usesLA() {
        for (final CoverSetTriple cst : this.coverSetTriples) {

            final List<AlgebraTerm> args = cst.getLeftArguments();
            for (final AlgebraTerm term : args) {

                final Set<SyntacticFunctionSymbol> functSymbols = term.getFunctionSymbols();

                if (functSymbols.contains(this.laProgram.fsPlus)) {
                    return true;
                }
            }

        }

        return false;
    }

    public List<CoverSetTriple> getCoverSetTriples() {
        return this.coverSetTriples;
    }

    /**
     * Generates all contructor terms with a certain depth.
     * If all these can be rewritten, this cover set is completely defined.
     * If not, this doesn't we any thing.
     * This is just a sufficient criterion.
     *
     * @param program the program with which it shall be rewritten
     * @return true if the the cover set is completely defined
     */
    public boolean isComplete(final Program program) {

        if (this.functionSymbols.size() != 1) {
            return false;
        }

        final int arity = this.functionSymbols.get(0).getArity();
        final int maxPatternDepth[] = new int[arity];

        // heuristic
        for (int i = 0; i < arity; i++) {
            maxPatternDepth[i] = 1;
        }

        for (final CoverSetTriple cst : this.coverSetTriples) {
            final List<AlgebraTerm> leftArgs = cst.getLeftArguments();
            for (int i = 0; i < arity; i++) {
                final AlgebraTerm arg = leftArgs.get(i);

                final int depth = PatternMaxDepth.apply(arg);
                if (depth > maxPatternDepth[i]) {
                    maxPatternDepth[i] = depth;
                }
            }
        }

        final FreshVarGenerator freshVarGenerator = new FreshVarGenerator();

        final ArrayList<ArrayList<AlgebraTerm>> args = new ArrayList<ArrayList<AlgebraTerm>>(arity);

        for (int i = 0; i < arity; i++) {
            final Sort argsort = this.functionSymbols.get(0).getArgSort(i);
            final ArrayList<AlgebraTerm> argterms =
                (ArrayList<AlgebraTerm>) this.createConstructorTerms(argsort, maxPatternDepth[i], freshVarGenerator);
            args.add(argterms);
        }

        final ArrayList<AlgebraTerm> argtupel = args.get(0);
        final ArrayList<AlgebraTerm> emptyList = new ArrayList<AlgebraTerm>();
        ArrayList<ArrayList<AlgebraTerm>> fArgs = this.extendArgTupel(emptyList, argtupel);

        for (int i = 1; i < arity; i++) {
            final ArrayList<AlgebraTerm> toAdd = args.get(i);
            final ArrayList<ArrayList<AlgebraTerm>> fArgsNew = this.extendAllArgTupel(fArgs, toAdd);
            fArgs = fArgsNew;
        }

        final List<AlgebraTerm> terms = new ArrayList<AlgebraTerm>();

        for (final ArrayList<AlgebraTerm> list : fArgs) {
            final AlgebraFunctionApplication fApp = AlgebraFunctionApplication.create(this.functionSymbols.get(0), list);
            terms.add(fApp);
        }

        final List<AlgebraTerm> unevaluated = new ArrayList<AlgebraTerm>();

        final AlgebraVariable stupidVar = freshVarGenerator.getFreshVariable("stupid", this.functionSymbols.get(0).getSort(), false);

        for (final AlgebraTerm term : terms) {
            final Equation eq = Equation.create(term, stupidVar);
            final Formula newFormula = FormulaOutermostLAEvaluationVisitor.apply(eq, program);
            if (newFormula.equals(eq)) {
                // we couldn't rewrite anything
                unevaluated.add(term);
            }
        }

        final boolean ret = unevaluated.isEmpty();

        return ret;
    }

    /**
     * Creates all constructor terms of a sort with a given depth.
     * As Variables we use fresh variables.
     *
     * @param sort
     * @param depth
     * @param freshVarGenerator the FreshVarGenerator to generate fresh variables
     * @return all constructor terms of a sort with a given depth
     */
    private List<AlgebraTerm> createConstructorTerms(final Sort sort,
        final int depth,
        final FreshVarGenerator freshVarGenerator) {
        final List<AlgebraTerm> terms = new ArrayList<AlgebraTerm>();
        if (depth < 0) {
            // nothing to ensure termination
            return terms;
        } else if (depth == 0) {
            // a variable
            final AlgebraVariable var = freshVarGenerator.getFreshVariable(sort.getName() + "Variable", sort, false);
            terms.add(var);

            return terms;
        } else {
            final List<ConstructorSymbol> consSymbols = sort.getConstructorSymbols();

            for (final ConstructorSymbol symbol : consSymbols) {
                final int arity = symbol.getArity();

                if (arity == 0) {
                    final ConstructorApp cApp = ConstructorApp.create(symbol);
                    terms.add(cApp);
                    continue;
                }

                final ArrayList<ArrayList<AlgebraTerm>> args = new ArrayList<ArrayList<AlgebraTerm>>(arity);

                for (final Sort argsort : symbol.getArgSorts()) {
                    final ArrayList<AlgebraTerm> argterms =
                        (ArrayList<AlgebraTerm>) this.createConstructorTerms(argsort, depth - 1, freshVarGenerator);
                    args.add(argterms);
                }

                final ArrayList<AlgebraTerm> argtupel = args.get(0);
                final ArrayList<AlgebraTerm> emptyList = new ArrayList<AlgebraTerm>();
                ArrayList<ArrayList<AlgebraTerm>> cArgs = this.extendArgTupel(emptyList, argtupel);

                for (int i = 1; i < arity; i++) {
                    final ArrayList<AlgebraTerm> toAdd = args.get(i);
                    final ArrayList<ArrayList<AlgebraTerm>> cArgsNew = this.extendAllArgTupel(cArgs, toAdd);
                    cArgs = cArgsNew;
                }

                for (final ArrayList<AlgebraTerm> list : cArgs) {
                    final ConstructorApp cApp = ConstructorApp.create(symbol, list);
                    terms.add(cApp);
                }
            }
        }

        return terms;
    }

    /**
     * Each tupel from the initial list is extended by each term from the second list seperately.
     *
     * @param initials the initial argument tupels
     * @param toAdd a list terms which will extend the initial argument tupels
     * @return the extended inital argument tupels
     */
    private ArrayList<ArrayList<AlgebraTerm>> extendAllArgTupel(final ArrayList<ArrayList<AlgebraTerm>> initials,
        final ArrayList<AlgebraTerm> toAdd) {
        final ArrayList<ArrayList<AlgebraTerm>> res = new ArrayList<ArrayList<AlgebraTerm>>(initials.size() * toAdd.size());
        for (final ArrayList<AlgebraTerm> start : initials) {
            final ArrayList<ArrayList<AlgebraTerm>> extendedArgTupels = this.extendArgTupel(start, toAdd);
            res.addAll(extendedArgTupels);
        }
        return res;
    }

    /**
     * From one argument tupel we generate a list of other argument tupels
     * by extending the initial argument tupel by each term of the second list.
     *
     * @param initial the initial argument tupel
     * @param toAdd a list terms which will extend the initial argument tupel
     * @return a list of argument tupes which are in all positions except the last identical
     *      to the initial argument tupel and have as last position the terms from the second list
     *
     */
    private ArrayList<ArrayList<AlgebraTerm>> extendArgTupel(final ArrayList<AlgebraTerm> initial, final ArrayList<AlgebraTerm> toAdd) {
        final ArrayList<ArrayList<AlgebraTerm>> res = new ArrayList<ArrayList<AlgebraTerm>>(toAdd.size());

        for (final AlgebraTerm term : toAdd) {

            final ArrayList<AlgebraTerm> copylist = new ArrayList<AlgebraTerm>(initial.size() + 1);

            for (final AlgebraTerm old : initial) {
                copylist.add(old.deepcopy());
            }
            copylist.add(term.deepcopy());
            res.add(copylist);
        }

        return res;
    }

    /**
     * checks whether the function is completely defined
     *
     * @return true iff there is a complete function definition
     */
    public boolean isLAComplete() {

        if (this.functionSymbols.size() != 1) {
            return false;
        }

        final int arity = this.functionSymbols.get(0).getArity();

        final Set<AlgebraVariable> existentialVariables = this.getVariables();

        final FreshVarGenerator fvg = new FreshVarGenerator(existentialVariables);
        final VariableSymbol varSym = VariableSymbol.create("a", this.laProgram.sortNat);
        final AlgebraVariable var = AlgebraVariable.create(varSym);

        final ArrayList<AlgebraVariable> allquantifiedVariables = new ArrayList<AlgebraVariable>(arity);

        for (int i = 0; i < arity; i++) {
            final AlgebraVariable newVar = fvg.getFreshVariable(var, false);
            allquantifiedVariables.add(newVar);
        }

        final List<LinearFormula> conjunctions = new ArrayList<LinearFormula>(this.coverSetTriples.size());

        for (final CoverSetTriple cst : this.coverSetTriples) {

            final List<Equation> cstConditions = cst.getConditions();

            final List<LinearFormula> constraints = new ArrayList<LinearFormula>(arity + cstConditions.size());

            final List<AlgebraTerm> cstLeftArgs = cst.getLeftArguments();

            // generate and add constraint equations
            for (int i = 0; i < arity; i++) {
                final AlgebraTerm ti = allquantifiedVariables.get(i);
                final AlgebraTerm si = cstLeftArgs.get(i);

                final LinearConstraint ce = LinearConstraint.createEquation(ti, si, this.laProgram);

                if (ce == null) {
                    throw new RuntimeException("Not an LA Constraint");
                }

                constraints.add(ce);
            }

            // add conditions
            for (final Equation eq : cstConditions) {

                final LinearConstraint constraint = LinearConstraint.create(eq, this.laProgram);

                if (constraint == null) {
                    throw new RuntimeException("Not an LA Constraint");
                }

                constraints.add(constraint);
            }

            final LinearFormula and = AndLinearFormula.create(constraints);

            final LinearFormula exists = ExistentialQuantifiedLinearFormula.create(cst.getVariables(), and);

            conjunctions.add(exists);

        }

        final LinearFormula or = OrLinearFormula.create(conjunctions);

        final LinearFormula all = AllQuantifiedLinearFormula.create(allquantifiedVariables, or);

        final QuantifierEliminator qe = new QuantifierEliminator();

        final LinearFormula result = all.apply(qe);

        if (result.equals(TruthValueLinearFormula.TRUE)) {
            return true;
        } else {
            return false;
        }

    }

}

/**
 * Gets the depth of a pattern.
 * Each funktion symbol adds 1 to the maximal depth of its subterms.
 * Unlike GetMaxDepthVisitor we don't count variables.
 */
class PatternMaxDepth implements CoarseGrainedTermVisitor<Integer> {

    @Override
    public Integer caseVariable(final AlgebraVariable v) {
        return Integer.valueOf(0);
    }

    @Override
    public Integer caseFunctionApp(final AlgebraFunctionApplication f) {

        int maxD = 0;
        for (final Object element : f.getArguments()) {
            final AlgebraTerm t = (AlgebraTerm) element;
            final int currD = t.apply(this);
            if (currD > maxD) {
                maxD = currD;
            }
        }
        return Integer.valueOf(maxD + 1);
    }

    public static int apply(final AlgebraTerm t) {
        final PatternMaxDepth vis = new PatternMaxDepth();
        return t.apply(vis);
    }

}
