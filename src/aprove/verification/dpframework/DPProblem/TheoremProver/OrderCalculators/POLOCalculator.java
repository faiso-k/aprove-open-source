package aprove.verification.dpframework.DPProblem.TheoremProver.OrderCalculators;

import java.util.*;
import java.util.Map.*;

import aprove.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.TheoremProver.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.dpframework.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * "Suitably monotonic" polynomial orders for the QDPTheoremProverProvessor.
 *
 * @author fuhs
 * @version $Id$
 */
public class POLOCalculator implements OrderCalculator {

    private POLOFactory poloFactory;

    private POLOCalculator(POLOFactory poloFactory) {
        this.poloFactory = poloFactory;
    }

    public static POLOCalculator create(POLOFactory poloFactory) {
        return new POLOCalculator(poloFactory);
    }

    @Override
    public Triple<ImmutableSet<Rule>, MonotonicityConstraints, PartiallyMonotonicOrder> calculateStrictRulesAndMonotonicity(
            Set<Rule> orientThemWeakly,
            Set<Rule> someStrict,
            Set<Set<Rule>> strictnessCandidatesDNF,
            Map<FunctionSymbol, MonotonicityConstraints> monConstraintsForFRules,
            Abortion aborter) throws AbortionException {
        // build term constraints and get a POLOSolver for them (i.e.,
        // for their signature)
        Set<Constraint<TRSTerm>> weakConstraints = Constraint.fromRules(orientThemWeakly, OrderRelation.GE);
        POLOSolver solver = this.poloFactory.getSolver(weakConstraints);
        solver.setAllowWeakMonotonicity(false);
        aborter.checkAbortion();

        // encode term constraints
        FormulaFactory<Diophantine> ffactory = new FullSharingFactory<Diophantine>();
        Pair<Formula<Diophantine>, Collection<Formula<Diophantine>>> fmlAndSpecialSubfmlae =
            this.encodeQDPThmProverConstraintsDNF(ffactory, solver,
                weakConstraints, someStrict, strictnessCandidatesDNF,
                monConstraintsForFRules, aborter);
        aborter.checkAbortion();

        // solve the encoded constraints
        POLO polo = solver.solveMaxDioFormula(fmlAndSpecialSubfmlae.x,
                fmlAndSpecialSubfmlae.y, aborter);
        aborter.checkAbortion();
        if (polo == null) {
            return null;
        }

        if (Globals.useAssertions) {
            for (Constraint<TRSTerm> c : weakConstraints) {
                assert polo.solves(c);
            }
        }

        // which rules were oriented strictly with their monotonicity
        // constraints satisfied? (here, it does not matter whether these were
        // considered as candidates by the heuristic before)
        Set<Rule> protoResX = new LinkedHashSet<Rule>();
        candLoop: for (Rule rule : someStrict) {
            Constraint<TRSTerm> c = Constraint.fromRule(rule, OrderRelation.GR);
            if (polo.solves(c)) {
                // great. strict orientation worked. now check the
                // monotonicity conditions.
                FunctionSymbol g = rule.getRootSymbol();
                MonotonicityConstraints monConstraints = monConstraintsForFRules.get(g);
                if (monConstraints == null) {
                    // head symbols of P do not have any of those,
                    // and there is no monotonicity requirement for them
                    protoResX.add(rule);
                    continue candLoop;
                }

                // strictness alone is not enough.
                boolean monOkay = monConstraints.isSatisfiedBy(polo);
                if (! monOkay) {
                    continue candLoop;
                }
                // whoopee. excellent. all monotonicity conditions were fulfilled.
                protoResX.add(rule);
            }
        }


        if (Globals.useAssertions) {
            // assert: some rule oriented strictly with suitable monotonicity
            assert ! protoResX.isEmpty() : "No set of rules oriented strictly with suitably monotonic order!\nRules:\n" +
                orientThemWeakly + "\nCandidates in DNF:\n" +
                strictnessCandidatesDNF + "\nMonotonicity constraints:\n" +
                monConstraintsForFRules + "\nPOLO:\n" + polo;

            // assert: some set of considered candidates oriented strictly
            // with suitable monotonicity
            boolean strictMonOkay = false;
            disjunctLoop: for (Set<Rule> candidateForStrictness : strictnessCandidatesDNF) {
                strictMonOkay = true; // hope for the best ...
                for (Rule rule : candidateForStrictness) {
                    Constraint<TRSTerm> c = Constraint.fromRule(rule, OrderRelation.GR);
                    if (! polo.solves(c)) {
                        // Not these conjuncts.
                        strictMonOkay = false;
                        continue disjunctLoop;
                    }
                    FunctionSymbol g = rule.getRootSymbol();
                    MonotonicityConstraints monConstraints = monConstraintsForFRules.get(g);
                    if (monConstraints == null) {
                        // head symbols of P do not have any of those,
                        // and there is no monotonicity requirement for them
                        break disjunctLoop;
                    }

                    boolean monOkay = monConstraints.isSatisfiedBy(polo);
                    if (! monOkay) {
                        strictMonOkay = false;
                        continue disjunctLoop;
                    }
                }
                if (strictMonOkay) { // the previous conjunction held!
                    break disjunctLoop;
                }
            }
            assert strictMonOkay : "No set of candidate rules oriented strictly with suitably monotonic order!\nAll rules:\n" +
                orientThemWeakly + "\nCandidates in DNF:\n" +
                strictnessCandidatesDNF + "\nMonotonicity constraints:\n" +
                monConstraintsForFRules + "\nPOLO:\n" + polo;
        }

        if (protoResX.isEmpty()) {
            // better safe than sorry, even w/o assertions
            return null;
        }

        // now to all possible monotonicity constraints and the question whether
        // they hold (for y-component of the result)
        Map<FunctionSymbol, ImmutableSet<Integer>> protoResY = new LinkedHashMap<FunctionSymbol, ImmutableSet<Integer>>();
        Interpretation inter = polo.getInterpretation();
        for (FunctionSymbol f : inter.getPol().keySet()) {
            ImmutableSet<Integer> monArgs = inter.getMonotonicArgs(f);
            protoResY.put(f, monArgs);
        }
        aborter.checkAbortion();

        // assemble result
        Triple<ImmutableSet<Rule>, MonotonicityConstraints, PartiallyMonotonicOrder> result;
        ImmutableSet<Rule> resX = ImmutableCreator.create(protoResX);
        MonotonicityConstraints resY = MonotonicityConstraints.create(ImmutableCreator.create(protoResY));
        result = new Triple<ImmutableSet<Rule>, MonotonicityConstraints, PartiallyMonotonicOrder>(resX, resY, polo);
        return result;
    }



    /**
     * Encodes constraints for the QDPTheoremProverProcessor.
     *
     * @param ffactory - will be used internally to build result formula
     * @param orientAsSuch - will be encoded as such
     * @param someStrict - at least one of them will have to be oriented
     *  strictly in conformance to monConstraints
     * @param strictnessCandidatesDNF - encode that for one of the sets
     *  all rules have to be oriented strictly fulfilling certain
     *  monotonicity constraints that are induced by the root symbol of
     *  the corresponding LHSs of the rewrite rules
     * @param monConstraints - monotonicity constraints for rules for the
     *  corresponding function symbol for "suitably monotonic" strictness
     * @param aborter
     * @return constraints for the QDPTheoremProverProcessor
     * @throws AbortionException
     */
    private Pair<Formula<Diophantine>, Collection<Formula<Diophantine>>> encodeQDPThmProverConstraintsDNF(
            FormulaFactory<Diophantine> ffactory,
            POLOSolver solver,
            Set<Constraint<TRSTerm>> orientAsSuch,
            Set<Rule> someStrict,
            Set<Set<Rule>> strictnessCandidatesDNF,
            Map<FunctionSymbol, MonotonicityConstraints> monConstraints,
            Abortion aborter) throws AbortionException {

        Interpretation interpretation = solver.getInterpretation();

        // precompute mapping from FSyms to corresponding Diophantine
        // constraints for monotonicity
        final Map<FunctionSymbol, Formula<Diophantine>> fToDioMon;
        fToDioMon = this.computeDioMon(ffactory, solver, monConstraints, aborter);

        // ordinary top-level conjuncts for the final formula
        final Set<SimplePolyConstraint> spcsConjuncts = solver.createPoloConstraints(orientAsSuch, aborter);



        // orient >= 1 rule strictly (respecting monotonicity, of course)
        // and as many as possible of them (if the engine can do MaxSAT)
        List<Formula<Diophantine>> strictnessDisjunctsForMaxSAT = new ArrayList<Formula<Diophantine>>(someStrict.size());
        for (Rule rule : someStrict) {
            Constraint<TRSTerm> c = Constraint.fromRule(rule, OrderRelation.GE);
            VarPolyConstraint vpc = interpretation.getPolynomialConstraint(c, aborter);
            SimplePolynomial constPart = vpc.getPolynomial().getConstantPart();

            // add strictness requirement ...
            Formula<Diophantine> eqFml, neqFml;
            Diophantine eqDio = Diophantine.create(constPart, ConstraintType.EQ);
            eqFml = ffactory.buildTheoryAtom(eqDio);
            neqFml = ffactory.buildNot(eqFml);

            // ... and monotonicity requirement
            FunctionSymbol f = ((TRSFunctionApplication)c.x).getRootSymbol();
            Formula<Diophantine> strictAndMonFml = fToDioMon.get(f);
            strictnessDisjunctsForMaxSAT.add(ffactory.buildAnd(neqFml, strictAndMonFml));
        }

        // encode strictness demand with monotonicity in addition to the
        // contribution to the top-level conjuncts
        List<Formula<Diophantine>> disjunctsForStrictness = new ArrayList<Formula<Diophantine>>(strictnessCandidatesDNF.size());

        // orient >= 1 rule set (!) strictly
        // (respecting monotonicity, of course)
        for (Set<Rule> candRuleConjuncts : strictnessCandidatesDNF) {
            List<Formula<Diophantine>> dioConjuncts = new ArrayList<Formula<Diophantine>>(1 << candRuleConjuncts.size());
            for (Rule rule : candRuleConjuncts) {
                Constraint<TRSTerm> c = Constraint.fromRule(rule, OrderRelation.GE);
                VarPolyConstraint vpc = interpretation.getPolynomialConstraint(c, aborter);
                SimplePolynomial constPart = vpc.getPolynomial().getConstantPart();

                // add strictness requirement ...
                Formula<Diophantine> eqFml, neqFml;
                Diophantine eqDio = Diophantine.create(constPart, ConstraintType.EQ);
                eqFml = ffactory.buildTheoryAtom(eqDio);
                neqFml = ffactory.buildNot(eqFml);
                dioConjuncts.add(neqFml);

                // ... and monotonicity requirement
                FunctionSymbol f = ((TRSFunctionApplication)c.x).getRootSymbol();
                Formula<Diophantine> strictAndMonFml = fToDioMon.get(f);
                dioConjuncts.add(strictAndMonFml);
            }
            Formula<Diophantine> dioDisjunct = ffactory.buildAnd(dioConjuncts);
            disjunctsForStrictness.add(dioDisjunct);

            aborter.checkAbortion();
        }

        Formula<Diophantine> strictnessFml, maxFml, resultX;

        // build big result conjunction
        // TODO maybe apply SPC simplification on spcsConjuncts
        final List<Formula<Diophantine>> resultConjuncts = new ArrayList<Formula<Diophantine>>(spcsConjuncts.size()+2);
        for (SimplePolyConstraint spc : spcsConjuncts) {
            Diophantine dio = Diophantine.create(spc.getPolynomial(),
                    spc.getType());
            resultConjuncts.add(ffactory.buildTheoryAtom(dio));
        }

        // assemble the strictness formulae to a disjunction
        strictnessFml = ffactory.buildOr(disjunctsForStrictness);

        // put overall strictness formula into result conjunction
        resultConjuncts.add(strictnessFml);

        // ditto for max stuff
        maxFml = ffactory.buildOr(strictnessDisjunctsForMaxSAT);
        resultConjuncts.add(maxFml);

        resultX = ffactory.buildAnd(resultConjuncts);

        Pair<Formula<Diophantine>, Collection<Formula<Diophantine>>> result =
            new Pair<Formula<Diophantine>, Collection<Formula<Diophantine>>>(
                    resultX, strictnessDisjunctsForMaxSAT);

        ////System.err.println(result);

        return result;
    }

    /* the following two methods are mainly left for interface reasons
     * (and to allow for a sanity check of the previous ones)
     */

    @Override
    @Deprecated
    public Triple<ImmutableSet<Rule>, MonotonicityConstraints, PartiallyMonotonicOrder> calculateStrictRulesAndMonotonicity(
            Set<Rule> orientThemWeakly, Set<Rule> strictnessCandidates,
            Map<FunctionSymbol, MonotonicityConstraints> monConstraintsForFRules,
            boolean allFRulesStrict,
            Abortion aborter) throws AbortionException {

        // build term constraints and get a POLOSolver for them (i.e.,
        // for their signature)
        Set<Constraint<TRSTerm>> weakConstraints, strictnessConstraints,
            allConstraints;
        weakConstraints = Constraint.fromRules(orientThemWeakly, OrderRelation.GE);
        strictnessConstraints = Constraint.fromRules(strictnessCandidates, OrderRelation.GE);
        allConstraints = new LinkedHashSet<Constraint<TRSTerm>>();
        allConstraints.addAll(weakConstraints);
        allConstraints.addAll(strictnessConstraints);
        POLOSolver solver = this.poloFactory.getSolver(allConstraints);
        solver.setAllowWeakMonotonicity(false);

        // encode term constraints
        FormulaFactory<Diophantine> ffactory = new FullSharingFactory<Diophantine>();
        Formula<Diophantine> fml = this.encodeQDPThmProverConstraints(ffactory,
                solver, weakConstraints, strictnessConstraints,
                monConstraintsForFRules, allFRulesStrict, aborter);

        // solve the encoded constraints
        POLO polo = solver.solveDioFormula(fml, aborter);
        if (polo == null) {
            return null;
        }

        if (Globals.useAssertions) {
            for (Constraint<TRSTerm> c : allConstraints) {
                assert polo.solves(c);
            }
        }

        // which candidates were oriented strictly with their monotonicity
        // constraints satisfied?
        Set<Rule> protoResX = new LinkedHashSet<Rule>();
        candLoop : for (Rule candidate : strictnessCandidates) {
            Constraint<TRSTerm> c = Constraint.fromRule(candidate, OrderRelation.GR);
            if (polo.solves(c)) {
                // great. strict orientation worked. now check the
                // monotonicity conditions.
                FunctionSymbol g = candidate.getRootSymbol();
                MonotonicityConstraints monConstraints = monConstraintsForFRules.get(g);
                for (Entry<FunctionSymbol, ? extends Set<Integer>> fI : monConstraints.getConstraints().entrySet()) {
                    FunctionSymbol f = fI.getKey();
                    for (int i : fI.getValue()) {
                        if (! polo.fIsMonotonicInArg(f, i)) {
                            // strictness alone is not enough.
                            continue candLoop;
                        }
                    }
                }
                // whoopee. excellent. all monotonicity conditions were fulfilled.
                protoResX.add(candidate);
            }
        }

        if (Globals.useAssertions) {
            assert ! protoResX.isEmpty() : "No rule oriented strictly with suitably monotonic order!\n" +
                strictnessCandidates + "\nMonotonicity constraints:\n" +
                monConstraintsForFRules + "\nPOLO:\n" + polo;
        }

        if (protoResX.isEmpty()) {
            // better safe than sorry, even w/o assertions
            return null;
        }

        // now to all possible monotonicity constraints and the question whether
        // they hold (for y-component of the result)
        Map<FunctionSymbol, ImmutableSet<Integer>> protoResY = new LinkedHashMap<FunctionSymbol, ImmutableSet<Integer>>();
        Interpretation inter = polo.getInterpretation();
        for (FunctionSymbol f : inter.getPol().keySet()) {
            ImmutableSet<Integer> monArgs = inter.getMonotonicArgs(f);
            protoResY.put(f, monArgs);
        }

        // assemble result
        Triple<ImmutableSet<Rule>, MonotonicityConstraints, PartiallyMonotonicOrder> result;
        ImmutableSet<Rule> resX = ImmutableCreator.create(protoResX);
        MonotonicityConstraints resY = MonotonicityConstraints.create(ImmutableCreator.create(protoResY));
        result = new Triple<ImmutableSet<Rule>, MonotonicityConstraints, PartiallyMonotonicOrder>(resX, resY, polo);
        return result;
    }


    /**
     * Encodes constraints for the QDPTheoremProverProcessor.
     *
     * @param ffactory - will be used internally to build result formula
     * @param orientAsSuch - will be encoded as such
     * @param allGEsomeGT - all of them will be encoded to GE, at least one of
     *  them will need to be strictly greater with the interpretation
     *  fulfilling certain monotonicity constraints that are induced by the
     *  root symbol of the corresponding LHS of the rewrite rule
     * @param monConstraints - monotonicity constraints for rules for the
     *  corresponding function symbol for "suitably monotonic" strictness
     * @param aborter
     * @return constraints for the QDPTheoremProverProcessor
     * @throws AbortionException
     */
    @Deprecated
    private Formula<Diophantine> encodeQDPThmProverConstraints(FormulaFactory<Diophantine> ffactory,
            POLOSolver solver,
            Set<Constraint<TRSTerm>> orientAsSuch,
            Set<Constraint<TRSTerm>> allGEsomeGT,
            Map<FunctionSymbol, MonotonicityConstraints> monConstraints,
            boolean allFRulesStrict,
            Abortion aborter) throws AbortionException {

        Interpretation interpretation = solver.getInterpretation();

        // precompute mapping from FSyms to corresponding Diophantine
        // constraints for monotonicity
        final Map<FunctionSymbol, Formula<Diophantine>> fToDioMon;
        fToDioMon = this.computeDioMon(ffactory, solver, monConstraints, aborter);

        // ordinary top-level conjuncts for the final formula
        final Set<SimplePolyConstraint> spcsConjuncts = solver.createPoloConstraints(orientAsSuch, aborter);

        // encode strictness demand with monotonicity in addition to the
        // contribution to the top-level conjuncts
        List<Formula<Diophantine>> disjunctsForStrictness = new ArrayList<Formula<Diophantine>>(allGEsomeGT.size());
        if (allFRulesStrict) {
            // find an f such that all f-rules in the candidate set are
            // oriented strictly
            Map<FunctionSymbol, List<Constraint<TRSTerm>>> fToConstraints;
            fToConstraints = this.computeFtoConstraints(allGEsomeGT);
            for (Entry<FunctionSymbol, List<Constraint<TRSTerm>>> fToCons
                    : fToConstraints.entrySet()) {
                // require satisfaction of monotonicity constraint for f
                // and that available constraints with f at the root of
                // the LHS are oriented strictly
                List<Constraint<TRSTerm>> termConstraintsOfF = fToCons.getValue();

                FunctionSymbol f = fToCons.getKey();
                Formula<Diophantine> monFml = fToDioMon.get(f);
                List<Formula<Diophantine>> allFConstraintsStrictlyAndMon;
                allFConstraintsStrictlyAndMon
                    = new ArrayList<Formula<Diophantine>>(termConstraintsOfF.size()+1);
                allFConstraintsStrictlyAndMon.add(monFml);

                for (Constraint<TRSTerm> specialTermConstraint : termConstraintsOfF) {
                    VarPolyConstraint vpc
                        = interpretation.getPolynomialConstraint(specialTermConstraint, aborter);
                    Pair<Set<SimplePolyConstraint>, SimplePolyConstraint> sscPair;
                    sscPair = vpc.createSearchStrictCoefficientConstraints();
                    spcsConjuncts.addAll(sscPair.x);
                    spcsConjuncts.add(sscPair.y);

                    Formula<Diophantine> eqFml, neqFml;
                    Diophantine eqDio = Diophantine.create(sscPair.y.getPolynomial(),
                            ConstraintType.EQ);
                    eqFml = ffactory.buildTheoryAtom(eqDio);
                    neqFml = ffactory.buildNot(eqFml);
                    allFConstraintsStrictlyAndMon.add(neqFml);
                }

                Formula<Diophantine> disjunct
                        = ffactory.buildAnd(allFConstraintsStrictlyAndMon);
                disjunctsForStrictness.add(disjunct);
            }
        }
        else {
            // somewhat more ordinary: just orient >= 1 constraint strictly
            // (respecting monotonicity, of course)
            for (Constraint<TRSTerm> specialConstraint : allGEsomeGT) {
                VarPolyConstraint vpc = interpretation.getPolynomialConstraint(specialConstraint, aborter);
                Pair<Set<SimplePolyConstraint>, SimplePolyConstraint> sscPair;
                sscPair = vpc.createSearchStrictCoefficientConstraints();
                spcsConjuncts.addAll(sscPair.x);
                spcsConjuncts.add(sscPair.y);

                Formula<Diophantine> eqFml, neqFml, disjunct;
                Diophantine eqDio = Diophantine.create(sscPair.y.getPolynomial(), ConstraintType.EQ);
                eqFml = ffactory.buildTheoryAtom(eqDio);
                neqFml = ffactory.buildNot(eqFml);

                FunctionSymbol f = ((TRSFunctionApplication)specialConstraint.x).getRootSymbol();
                Formula<Diophantine> strictAndMonFml = fToDioMon.get(f);
                disjunct = ffactory.buildAnd(strictAndMonFml, neqFml);
                disjunctsForStrictness.add(disjunct);
                aborter.checkAbortion();
            }
        }

        Formula<Diophantine> strictnessFml, result;

        // build big result conjunction
        // TODO maybe apply SPC simplification on spcsConjuncts
        final List<Formula<Diophantine>> resultConjuncts = new ArrayList<Formula<Diophantine>>(spcsConjuncts.size());
        for (SimplePolyConstraint spc : spcsConjuncts) {
            Diophantine dio = Diophantine.create(spc.getPolynomial(),
                    spc.getType());
            resultConjuncts.add(ffactory.buildTheoryAtom(dio));
        }

        // assemble the strictness formulae to a disjunction
        strictnessFml = ffactory.buildOr(disjunctsForStrictness);

        // put overall strictness formula into result conjunction
        resultConjuncts.add(strictnessFml);
        result = ffactory.buildAnd(resultConjuncts);
        return result;
    }

    /**
     *
     * @param cs - some term constraints
     * @return map that maps function symbols f to those constraints in
     *  cs whose LHS has f as root
     */
    private Map<FunctionSymbol, List<Constraint<TRSTerm>>> computeFtoConstraints(
            Iterable<Constraint<TRSTerm>> cs) {
        Map<FunctionSymbol, List<Constraint<TRSTerm>>> result =
            new LinkedHashMap<FunctionSymbol, List<Constraint<TRSTerm>>>();
        for (Constraint<TRSTerm> c : cs) {
            TRSFunctionApplication fAppLhs = (TRSFunctionApplication) c.getLeft();
            FunctionSymbol f = fAppLhs.getRootSymbol();
            List<Constraint<TRSTerm>> constraintsForF = result.get(f);
            if (constraintsForF == null) {
                constraintsForF = new ArrayList<Constraint<TRSTerm>>();
                result.put(f, constraintsForF);
            }
            constraintsForF.add(c);
        }
        return result;
    }

    /**
     * @param ffactory - will be used to construct the resulting formula
     * @param monConstraints - maps function symbols to (abstract) monotonicity
     *  constraints
     * @param aborter
     * @return map from function symbols to corresponding polynomial
     *  monotonicity constraints - default is TRUE (e.g., for tuple symbols)
     * @throws AbortionException
     */
    private DefaultValueMap<FunctionSymbol, Formula<Diophantine>> computeDioMon(FormulaFactory<Diophantine> ffactory,
            POLOSolver solver,
            Map<FunctionSymbol, MonotonicityConstraints> monConstraints,
            Abortion aborter) throws AbortionException {

        Interpretation interpretation = solver.getInterpretation();

        Map<Pair<FunctionSymbol, Integer>, Diophantine> memory =
            new HashMap<Pair<FunctionSymbol, Integer>, Diophantine>();
        DefaultValueMap<FunctionSymbol, Formula<Diophantine>> result =
            new DefaultValueMap<FunctionSymbol, Formula<Diophantine>>(ffactory.buildConstant(true));
        for (Entry<FunctionSymbol, MonotonicityConstraints> fToMon : monConstraints.entrySet()) {
            MonotonicityConstraints monConstr = fToMon.getValue();
            List<Formula<Diophantine>> conjuncts =
                new ArrayList<Formula<Diophantine>>(monConstr.size()+1);
            Map<FunctionSymbol, ImmutableSet<Integer>> gToMonArgsMap = monConstr.getConstraints();
            for (Entry<FunctionSymbol, ImmutableSet<Integer>> gToMonArgs : gToMonArgsMap.entrySet()) {
                FunctionSymbol g = gToMonArgs.getKey();
                Set<Integer> args = gToMonArgs.getValue();
                for (Integer i : args) {
                    Pair<FunctionSymbol, Integer> gI =
                        new Pair<FunctionSymbol, Integer>(g, i);
                    Diophantine dio = memory.get(gI);
                    if (dio == null) {
                        dio = interpretation.getStrongMonotonicityConstraint(g, i);
                        memory.put(gI, dio);
                    }
                    conjuncts.add(ffactory.buildTheoryAtom(dio));
                }
            }
            Formula<Diophantine> fFormula = ffactory.buildAnd(conjuncts);
            result.put(fToMon.getKey(), fFormula);
            aborter.checkAbortion();
        }
        return result;
    }
}
