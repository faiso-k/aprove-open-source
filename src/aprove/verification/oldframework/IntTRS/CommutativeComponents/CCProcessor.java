package aprove.verification.oldframework.IntTRS.CommutativeComponents;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.solver.Engines.*;
import aprove.solver.Engines.SMTEngine.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.TerminationGraph.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * This processor calculates (an estimation of) the commutative components graph
 * of a given integer rewrite system & returns it SCCs.
 * @author Matthias Hoelzel
 */
public class CCProcessor extends Processor.ProcessorSkeleton {
    /** Constructor! */
    public CCProcessor() {
    }

    @Override
    public boolean isApplicable(final BasicObligation obl) {
        return obl instanceof IRSwTProblem && ((IRSwTProblem) obl).isIRS();
    }

    @Override
    public Result process(
        final BasicObligation obl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        assert obl instanceof IRSwTProblem : "Wrong obligation type!";
        final IRSProblem problem;
        if (obl instanceof IRSProblem) {
            problem = (IRSProblem) obl;
        } else {
            problem = new IRSProblem((IRSwTProblem) obl);
        }
        final FreshNameGenerator ng = new FreshNameGenerator(FreshNameGenerator.APPEND_NUMBERS);
        final RulePreparation rulePreparer = new RulePreparation(ng);
        final CCProof proof = new CCProof();

        final Set<IGeneralizedRule> oldRules = rulePreparer.prepare(problem.getRules());

        final TerminationGraph tg =
            TerminationGraph.buildGraph(
                oldRules,
                problem.getStartTerm(),
                new FullSharingFactory<SMTLIBTheoryAtom>(),
                aborter,
                ng,
                null);

        final LinkedList<Set<IGeneralizedRule>> newRuleSets = new LinkedList<>();
        for (final Set<IGeneralizedRule> scc : tg.getNTSCCs()) {
            final TerminationGraph subGraph = tg.getSubGraph(scc);
            this.removeUnnecessaryEdges(subGraph, aborter, ng);
            newRuleSets.addAll(subGraph.getSCCs());
        }

        if (newRuleSets.size() == 1 && newRuleSets.getFirst().equals(oldRules)) {
            return ResultFactory.unsuccessful();
        } else {
            final LinkedList<IRSProblem> newProblems = new LinkedList<>();
            for (final Set<IGeneralizedRule> rules : newRuleSets) {
                assert rules != null && !rules.isEmpty() : "Strange rule-set: " + rules;
                newProblems.add(new IRSProblem(ImmutableCreator.create(rules)));
            }

            return ResultFactory.provedAnd(newProblems, YNMImplication.EQUIVALENT, proof);
        }
    }

    /**
     * The graph might contain some edges, that are not necessary. This method
     * finds some of them and remove them.
     * @param tg some termination graph to be simplified
     * @param aborter some aborter
     * @param ng some name generator
     * @throws AbortionException
     */
    private void removeUnnecessaryEdges(final TerminationGraph tg, final Abortion aborter, final FreshNameGenerator ng)
        throws AbortionException
    {
        final LinkedList<Pair<IGeneralizedRule, IGeneralizedRule>> toDelete = new LinkedList<>();
        for (final IGeneralizedRule from : tg.getNodes()) {
            for (final IGeneralizedRule to : tg.getEdges(from)) {
                if (this.isUnnecessary(from, to, aborter, ng)) {
                    toDelete.add(new Pair<IGeneralizedRule, IGeneralizedRule>(from, to));
                }
            }
        }
        for (final Pair<IGeneralizedRule, IGeneralizedRule> p : toDelete) {
            tg.disconnect(p.x, p.y);
        }
    }

    /**
     * Calculates whether or not the edge it really necessary.
     * @param from some rule
     * @param to another rule
     * @param aborter some aborter
     * @param ng some name generator
     * @return boolean true, if not necessary
     * @throws AbortionException
     */
    private boolean isUnnecessary(
        final IGeneralizedRule from,
        final IGeneralizedRule to,
        final Abortion aborter,
        final FreshNameGenerator ng) throws AbortionException
    {

        final IGeneralizedRule r1 = new Chaining(from, to, ng).getResult();
        final IGeneralizedRule r2 = new Chaining(to, from, ng).getResult();

        // If the relation characterized by r1 is a subset of those from r2,
        // then we can remove the edge from rule "from" to rule "to".

        if (r1 == null
            || r2 == null
            || !r1.getLeft().getRootSymbol().equals(r2.getLeft().getRootSymbol())
            || !((TRSFunctionApplication) r1.getRight()).getRootSymbol().equals(
                ((TRSFunctionApplication) r2.getRight()).getRootSymbol()))
        {
            // The rules should have the form f(..) -> f(..) for some symbol f.
            // Because f(..) -> g(..) can only be a subset of g(..) -> f(..), if
            // the first object describes the empty relation, but this is exactly
            // what the termination graph already calculated!
            return false;
        }

        // Rename variables occurring in r2:
        final TRSSubstitution matcher = r2.getLeft().getMatcher(r1.getLeft());
        final IGeneralizedRule r2Prime =
            IGeneralizedRule.create(
                r2.getLeft().applySubstitution(matcher),
                r2.getRight().applySubstitution(matcher),
                r2.getCondTerm().applySubstitution(matcher));

        final Set<TRSVariable> variablesOfR1 = r1.getVariables();
        variablesOfR1.addAll(r1.getCondVariables());

        if (!variablesOfR1.containsAll(r2Prime.getVariables())
            || !variablesOfR1.containsAll(r2Prime.getCondVariables()))
        {
            // Ugly free variables ... -.-
            return false;
        }

        if (this.isSyntacticallyEqual(r1, r2Prime, variablesOfR1, aborter, ng)) {
            return true;
        }

        return this.askSMTSolver(aborter, ng, r1, r2Prime);
    }

    /**
     * If the rules are syntactically the same, then we do not have to ask the
     * SMT-Solver. This should be faster.
     * @param r1 first rule
     * @param r2 second rule with renamed variables
     * @param variablesOfR1 the variables occuring in R1
     * @param aborter some aborter
     * @param ng some name generator
     * @return boolean
     * @throws AbortionException can be aborted
     */
    private boolean isSyntacticallyEqual(
        final IGeneralizedRule r1,
        final IGeneralizedRule r2,
        final Set<TRSVariable> variablesOfR1,
        final Abortion aborter,
        final FreshNameGenerator ng) throws AbortionException
    {

        final Set<TRSVariable> variablesOfR2 = r2.getVariables();
        variablesOfR2.addAll(r2.getCondVariables());

        if (!variablesOfR1.equals(variablesOfR2)) {
            return false;
        }

        // 1. Check arguments:
        final Iterator<TRSTerm> argIter1 = ((TRSFunctionApplication) r1.getRight()).getArguments().iterator();
        final Iterator<TRSTerm> argIter2 = ((TRSFunctionApplication) r2.getRight()).getArguments().iterator();
        while (argIter1.hasNext()) {
            final TRSTerm arg1 = argIter1.next();
            final TRSTerm arg2 = argIter2.next();
            final VarPolynomial arg1Poly = ToolBox.intTermToPolynomial(arg1, ng);
            final VarPolynomial arg2Poly = ToolBox.intTermToPolynomial(arg2, ng);
            if (!arg1Poly.equals(arg2Poly)) {
                return false;
            }
        }

        // 2. Check conditions:
        final LinkedHashSet<PolynomialConstraint> constraints1 =
            new LinkedHashSet<>(ToolBox.boolTermToPolynomialConstraints(
                (TRSFunctionApplication) r1.getCondTerm(),
                ng,
                aborter));
        final LinkedHashSet<PolynomialConstraint> constraints2 =
            new LinkedHashSet<>(ToolBox.boolTermToPolynomialConstraints(
                (TRSFunctionApplication) r2.getCondTerm(),
                ng,
                aborter));
        final boolean result = constraints1.equals(constraints2);
        return result;
    }

    /**
     * Asks the SMT-Solver, whether or not R1 is subset of R2.
     * @param aborter some aborter
     * @param ng some name generator
     * @param r1 the first rule
     * @param r2Prime the second rule with renamed variables
     * @return boolean
     * @throws AbortionException can be aborted
     */
    private boolean askSMTSolver(
        final Abortion aborter,
        final FreshNameGenerator ng,
        final IGeneralizedRule r1,
        final IGeneralizedRule r2Prime) throws AbortionException
    {

        // canUseOtherRule = "we can use the other rule to obtain the same result"
        TRSTerm canUseOtherRule = r2Prime.getCondTerm();
        final Iterator<TRSTerm> arg1Iterator = ((TRSFunctionApplication) r1.getRight()).getArguments().iterator();
        final Iterator<TRSTerm> arg2Iterator = ((TRSFunctionApplication) r2Prime.getRight()).getArguments().iterator();
        while (arg1Iterator.hasNext() && arg2Iterator.hasNext()) {
            final TRSTerm arg1 = arg1Iterator.next();
            final TRSTerm arg2 = arg2Iterator.next();

            canUseOtherRule = ToolBox.buildAnd(canUseOtherRule, ToolBox.buildEq(arg1, arg2));
        }

        // If the following is not satisfiable, then the edge was not necessary:
        final TRSTerm toCheck = ToolBox.buildAnd(ToolBox.buildNot(canUseOtherRule), r1.getCondTerm());

        final Formula<SMTLIBTheoryAtom> formula =
            ToolBox.boolTermToSMT_QF_IA(toCheck, new FullSharingFactory<SMTLIBTheoryAtom>(), ng);
        final LinkedList<Formula<SMTLIBTheoryAtom>> formulaList = new LinkedList<>();
        formulaList.add(formula);

        final YicesEngine engine = new YicesEngine();

        YNM answer = null;
        try {
            answer = engine.satisfiable(formulaList, SMTLogic.QF_LIA, aborter);
        } catch (final WrongLogicException e) {
            e.printStackTrace();
        }

        return answer != null && answer.equals(YNM.NO);
    }

    /**
     * A very fine proof.
     * @author cotto (don't blame me)
     */
    public class CCProof extends DefaultProof {
        /** Constructor! */
        public CCProof() {
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "Constructed CCGraph and returned SCCs.";
        }
    }
}
