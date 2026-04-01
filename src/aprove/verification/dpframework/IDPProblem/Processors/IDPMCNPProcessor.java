package aprove.verification.dpframework.IDPProblem.Processors;

import java.io.*;
import java.util.*;
import java.util.concurrent.atomic.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.Solvers.*;
import aprove.verification.dpframework.IDPProblem.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.*;
import aprove.verification.dpframework.IDPProblem.idpGraph.*;
import aprove.verification.dpframework.IDPProblem.itpf.*;
import aprove.verification.dpframework.IDPProblem.itpf.IItpfRule.*;
import aprove.verification.dpframework.IDPProblem.itpf.rules.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Monoids.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Rings.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * For now, all we want to accomplish here is to synthesize monotonicity
 * constraints (a variation of size-change graphs for integer problems)
 * from a given IDP problem such that termination of the monotonicity
 * constraints should imply finiteness of the IDP problem. These monotonicity
 * constraints (MCs) are then exported as a side effect, and the processor as
 * such never succeeds (yet).
 *
 * Here we introduce fresh variables instead of calls to usable rules or
 * div/mod/times in P. If the times operator is invoked on two identical
 * terms, we additionally know that the result will be positive (and we
 * export this knowledge).
 *
 * If at least one of the arguments to times is ground (e.g. in "2*x"), we
 * need not abstract this call at all - linearity of the resulting proto-MCs
 * (which is required by post-processing) is ensured.
 *
 * Then the result for the monotonicity constraints found by external tools
 * (which know nothing about rewriting and usable rules) should actually entail
 * finiteness of the IDP problem.
 *
 * Abstractions (integer polynomial interpretations) for ...
 * - integers (and their operations)
 *   -> as in the IDP paper published at RTA'09
 * - "tuple symbols"
 *   -> minimal arg filter that still eliminates all usable rules
 *      (could be improved later for abstraction search a la LPAR-17
 *      where the constraints for usable rules are encoded into the
 *      same SAT instance) -- apart from that, no interpretation is done
 * - non-predefined symbols (and booleans)
 *    -> sum of their args + 1
 *       (could be improved later for abstraction search a la LPAR-17)
 *
 * Since we abstract from usable rules, we can conveniently ignore the rules
 * in R as far as export is concerned.
 *
 * [Beware: Significant parts of this code have been written shortly before
 * a paper deadline.]
 *
 * @author fuhs
 */
public class IDPMCNPProcessor extends Processor.ProcessorSkeleton {

    private static final Logger log = Logger.getLogger("aprove.verification.dpframework.IDPProblem.Processors.IDPMCNPProcessor");

    // true: always say yellow; false: always say green!
    private static final boolean HONEST = true;

    // Prolog likes constructors to start with non-capital letters
    private static final String PROGRAM_POINT_PREFIX = "p";

    // Prolog likes variables to start with capital letters
    private static final String FRESH_VAR_PREFIX = "A";

    private static AtomicInteger counter = new AtomicInteger(1);

    // for export
    public enum Relation {
        GT(">"), GE(">="), LT("<"), LE("=<"), EQ("="), NEQ("!=");

        private final String prologString;
        private Relation(String prologString) {
            this.prologString = prologString;
        }

        @Override
        public String toString() {
            return this.prologString;
        }
    }

    private final boolean dropBooleanSymbols;
    private final boolean dropContextSensitiveSymbols;
    private final boolean toStdOut; // true: output to stdout, false: output to file
    private final String dumpPath;


    @ParamsViaArgumentObject
    public IDPMCNPProcessor(Arguments arguments) {
        this.dropBooleanSymbols = arguments.dropBooleanSymbols;
        this.dropContextSensitiveSymbols = arguments.dropContextSensitiveSymbols;
        this.toStdOut = arguments.toStdOut;
        this.dumpPath = arguments.dumpPath;
    }

    @Override
    public boolean isApplicable(BasicObligation o) {
        if (o instanceof IDPProblem) {
            return this.isIDPApplicable((IDPProblem) o);
        }
        return false;
    }

    public boolean isIDPApplicable(IDPProblem idp) {

        // for now require to be at least as restrictive as innermost and
        // at most the domains of Integers (and Booleans)
        Set<Domain> allowedDomains = new LinkedHashSet<Domain>();
        allowedDomains.add(DomainFactory.INTEGERS);
        allowedDomains.add(DomainFactory.BOOLEAN);
        return idp.getRuleAnalysis().isNfQSubsetEqNfR() && (allowedDomains.containsAll(idp.getRuleAnalysis().getDomains()));
    }

    @Override
    public Result process(BasicObligation o, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        IDPProblem problem = (IDPProblem) o; // this cast will succeed (see isApplicable)
        String filename = (String) rti.getMetadata(Metadata.PROBLEM_PATH_NAME);
        filename = filename.replace("/", "SLASH");
        filename = filename + "_" + IDPMCNPProcessor.counter.getAndIncrement() + ".clpq";
        return this.processIDPProblem(problem, filename, aborter);
    }


    protected Result processIDPProblem(IDPProblem origIdp, String filename, Abortion aborter) throws AbortionException {

        IDPGInterpretation interpretation = IDPMCNPProcessor.prepareInterpretation(origIdp, aborter);
        String exportedProblem = this.exportMC(origIdp, interpretation, aborter);
        if (this.toStdOut) {
            System.out.println(exportedProblem);
            System.out.println("###########################");
        }
        else {
            this.exportToDisk(exportedProblem, filename);
        }


        // (2) interpret the arguments in the filtered problem.
        // Be careful with / and %, i.e., anything with infinitely
        // many rules where we only have approximations. Also anything Boolean
        // could be nasty (and is most likely not to be useful).

        // - Easy:
        // Just refuse anything that contains context-sensitive symbols. ;)
        // That's why we'll eliminate them already via the Afs for now.
        //
        // MC recommends: Don't filter them, just replace them by a fresh
        // variable. Then we do not get any arcs to the nasty argument for
        // *this* call, but maybe for others.

        // - Medium:
        // Export div and mod "as is". May be more challenging in practice
        // than it looks at first glance since interpreted terms are required
        // to be max-polynomials (which do not contain DIV or MOD).

        // - Hard (IDP style):
        // Keep /two/ interpretations for context-sensitive things:
        // * an underapproximation p_under, which induces arcs "p_under >=/> ..."
        // * an overapproximation  p_over,  which induces arcs "p_over  <=/< ..."
        // (actually just keeping two interpretations in general is
        // probably a good idea -- should keep things sufficiently general)


        // example (without explicit approximations):
        /*
        F(x0, cons(y0, z0), TRUE) -> G(x0 + y0, z0) :|: y0 >= 0

        (where the condition has been taken from the edge labels on the IDP
        graph) is abstracted to:

          F(x0, y0 + z0 + 1, 1) -> G(x0 + y0, z) :|: y0 >= 0

        (a) We could now export this "as is" (it's linear) and let Prolog's clpq
            library do the deductions for the arrows.
        OR
        (b) We deduce the arrows ourselves.
        This now allows us to synthesize the following monotonicity constraint
        (by exploiting that adding a non-negative number is a weakly monotonic
        unary operation on Z):

          F(x, y, z, zero) :- [x' >= x, y' > y, y >= zero, zero = zero'],
                                  G(x', y', zero').

        Of course, we need to make sure that any occurrence of a tuple symbol F
        is equipped with all needed constants (this DP contributes "zero", a DP
        F(...) -> H(...) :|: x0 >= 7 would additionally contribute "seven",
        where "seven > zero" will obviously hold).
        */

        // (3) possible improvement: consider (backward) chains of length > 1,
        //     represent the restriction to these call sequences by suitably
        //     renamed copies of the tuple symbols

        aborter.checkAbortion();
        if (IDPMCNPProcessor.HONEST) {
            return ResultFactory.unsuccessful("We currently only export MC problems, we do not solve them.");
        }
        else {
            return ResultFactory.proved(new IDPMCNPProof());
        }
    }

    private void exportToDisk(String mc, String filename) {
        String filenameWithPath = this.dumpPath + "/" + filename;
        try {
            File fileWithPath = new File(filenameWithPath);
            Writer inputWriter = new OutputStreamWriter(new FileOutputStream(fileWithPath));
            inputWriter.write(mc);
            inputWriter.close();
        }
        catch (IOException e) {
            System.err.println("Unable to dump MC to " + filenameWithPath);
            System.err.println(e.getMessage());
            e.printStackTrace();
        }
    }

    /**
     * Given an IDPProblem, returns an interpretation that interprets every
     * non-predefined function symbol as x_1 + ... + x_n + 1.
     *
     * @param origIdp
     * @return
     */
    private static IDPGInterpretation prepareInterpretation(IDPProblem origIdp,
            Abortion aborter) throws AbortionException {
        IDPRuleAnalysis ruleAnalysis = origIdp.getRuleAnalysis();
        //ImmutableSet<FunctionSymbol> defSyms = ruleAnalysis.getRAnalysis().getDefinedSymbols();


        CoeffOrder<BigIntImmutable> coeffOrder = new BigIntImmutableOrder();
        ConstraintFactory<BigIntImmutable> constraintFactory =
            new SimpleFactory<BigIntImmutable>();
        GPolyFactory<BigIntImmutable, GPolyVar> coeffFactory =
            new FullSharingFactory<BigIntImmutable, GPolyVar>();

        List<Citation> citations = java.util.Collections.<Citation>singletonList(Citation.POLO); // TODO, obviously

        Ring<BigIntImmutable> ring = new BigIntImmutableRing();
        CMonoid<GMonomial<GPolyVar>> monoid = new GMonomialMonoid<GPolyVar>();
        GPolyFactory<BigIntImmutable, GPolyVar> innerPolyFactory = new FullSharingFactory<BigIntImmutable, GPolyVar>();
        GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> outerPolyFactory = new FullSharingFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>();
        GPolyFlatRing<BigIntImmutable, GPolyVar> flatRing =
            new SimpleGPolyFlatRing<BigIntImmutable, GPolyVar>(ring, monoid);
        FlatteningVisitor<BigIntImmutable, GPolyVar> fvInner = new FlatteningVisitor<BigIntImmutable, GPolyVar>(flatRing);

        GPolyFlatRing<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> flatRing2 = new SimpleGPolyFlatRing<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>(innerPolyFactory, monoid);
        FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> fvOuter = new FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>(flatRing2);

        IDPGInterpretation interpretation =
            IDPGInterpretation.create(false, false,
                ruleAnalysis, new IdpDefaultShapeHeuristic(),
                outerPolyFactory, innerPolyFactory, constraintFactory,
                fvInner, fvOuter, coeffOrder, citations,
                new OPCRange<BigIntImmutable>(BigIntImmutable.MINUS_ONE, BigIntImmutable.TWO), // TODO
                BigIntImmutable.ONE, aborter);

        GInterpretationMode<BigIntImmutable> interMode = new GInterpretationModeStronglyLinear<BigIntImmutable>(GInterpretationModeStronglyLinear.ConstantPart.ONE);
        for (FunctionSymbol f : ruleAnalysis.getPAnalysis().getFunctionSymbols()) {
            // maybe ignore those DP head symbols - we don't interpret them anyway
            interpretation.extend(f, interMode, aborter); // x_1 + ... + x_n + 1
        }
        return interpretation;
    }

    private String exportMC(IDPProblem origIdp, IDPGInterpretation interpretation,
            Abortion aborter) throws AbortionException {
        StringBuilder result = new StringBuilder();

        // symbols that stand for function calls in args which are to be
        // replaced by fresh variables
        Set<FunctionSymbol> callSyms = IDPMCNPProcessor.getCallSyms(origIdp, this.dropContextSensitiveSymbols, this.dropBooleanSymbols);

        Set<FunctionSymbol> callSymsNonBool = IDPMCNPProcessor.getCallSyms(origIdp, this.dropContextSensitiveSymbols, false);

        IDPPredefinedMap predefinedMap = origIdp.getRuleAnalysis().getPreDefinedMap();

        // pre-defined times symbol
        FunctionSymbol times = predefinedMap.getSym(Func.Mul, DomainFactory.INTEGERS);

        // For all edges "<..., (F(t1,...,tn) -> G(u1,...,uk))> if cond"
        // in the DP graph:
        // -  gather info from cond (for the edges),
        //    requires looking at the source node of the edge (?)
        // -  export "F(A1, ..., An) :- [the gathered info from cond,
        //              A1 = Pol(t1), ..., An = Pol(tn),
        //              B1 = Pol(u1), ..., Bk = Pol(uk)], G(B1, ..., Bk).
        IIDependencyGraph graph = origIdp.getIdpGraph();
        ImmutableSet<IdpEdge> edges = graph.getEdges();

        // gather used variable names in a first pass ...
        Set<TRSVariable> usedVars = new LinkedHashSet<TRSVariable>();
        for (IdpEdge edge : edges) {
            Node sink = edge.getTo();
            usedVars.addAll(edge.getItpf().getFreeVariables());
            GeneralizedRule dp = sink.getRule();
            dp.getLeft().collectVariables(usedVars);
            dp.getRight().collectVariables(usedVars);
        }

        // ... so we can initialize a single name generator for later use,
        // allowing e.g. for "global names" for variables denoting constants
        MCNPNameGenerator nameGen = MCNPNameGenerator.createForForbiddenNames(IDPMCNPProcessor.FRESH_VAR_PREFIX, usedVars);
        MCNPPolyHelper polyHelper = MCNPPolyHelper.create(interpretation);

        for (IdpEdge edge : edges) {

            // first compute the arg interpretations and export the program points
            Node sink = edge.getTo();
            GeneralizedRule dp = sink.getRule();
            TRSFunctionApplication left = dp.getLeft();
            TRSTerm rightTerm = dp.getRight();
            if (rightTerm.isVariable()) {
                throw new MCNPException("MCNP does not do collapsing DPs!");
            }
            TRSFunctionApplication right = (TRSFunctionApplication) rightTerm;

            // "abstract" the terms to have fresh variables in all root args
            // that contain user-defined defined symbols or DIV / MOD
            TRSFunctionApplication leftCallsAbstracted = IDPMCNPProcessor.replaceCallsByFreshVars(left, callSyms, nameGen);
            TRSFunctionApplication rightCallsAbstracted = IDPMCNPProcessor.replaceCallsByFreshVars(right, callSyms, nameGen);

            List<TRSVariable> squareVars = new ArrayList<TRSVariable>();
            TRSFunctionApplication leftAbstracted;
            TRSFunctionApplication rightAbstracted;
            if (times == null) {
                leftAbstracted = leftCallsAbstracted;
                rightAbstracted = rightCallsAbstracted;
            }
            else {
                leftAbstracted = IDPMCNPProcessor.replaceTimesByFreshVarsInDP(leftCallsAbstracted, times, squareVars, nameGen);
                rightAbstracted = IDPMCNPProcessor.replaceTimesByFreshVarsInDP(rightCallsAbstracted, times, squareVars, nameGen);
            }

            List<OrderPoly<BigIntImmutable>> lArgInter = IDPMCNPProcessor.interpretArgs(interpretation, leftAbstracted, aborter);
            List<OrderPoly<BigIntImmutable>> rArgInter = IDPMCNPProcessor.interpretArgs(interpretation, rightAbstracted, aborter);

            List<Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>>> lArgInterWithVar =
                polyHelper.zipWithFreshVars(lArgInter, nameGen, aborter);
            List<Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>>> rArgInterWithVar =
                polyHelper.zipWithFreshVars(rArgInter, nameGen, aborter);

            // gather program points
            String leftProgramPoint, rightProgramPoint;
            leftProgramPoint = IDPMCNPProcessor.toProtoProgramPoint(left.getRootSymbol(), lArgInterWithVar, interpretation);
            rightProgramPoint = IDPMCNPProcessor.toProtoProgramPoint(right.getRootSymbol(), rArgInterWithVar, interpretation);

            // There are two kinds of useful infos in edgeFormulas
            // (after some massaging, that is):
            //  (i) u >= v (something similar to that, anyway):
            //      arithmetic info with the variables of n1
            // (ii) s ->^* t:
            //      relates expressions with variables of n1 to variables of n2
            //          -> we care about the latter, so we must do some reverse computation
            //             or allow additional variables
            final Itpf edgeFormula1 = edge.getItpf();
            final IItpfRule itpfBoolOpRule = new ItpfBoolOp();
            if (Globals.useAssertions) {
                assert itpfBoolOpRule.isApplicable(origIdp, edgeFormula1, ApplicationMode.Multistep);
            }
            final Itpf edgeFormula2 = itpfBoolOpRule.process(origIdp, edgeFormula1, ApplicationMode.Multistep, aborter);
            final IItpfRule ccRelOpRule = new CCRelOp();
            if (Globals.useAssertions) {
                assert ccRelOpRule.isApplicable(origIdp, edgeFormula2, ApplicationMode.Multistep);
            }

            final Itpf edgeFormula3 = ccRelOpRule.process(origIdp, edgeFormula2, ApplicationMode.Multistep, aborter);
            final Itpf edgeFormula4 = edgeFormula3.toDnf();
            ItpExtractVisitor itpExtractor = new ItpExtractVisitor(origIdp.getRuleAnalysis(), ApplicationMode.Multistep);
            edgeFormula4.visit(itpExtractor);

            MCNPItpfAtomHelper atomHelper = MCNPItpfAtomHelper.create(predefinedMap);
            List<List<ItpfAtom>> itpAtoms = itpExtractor.getItpDNF();
            List<List<ItpfItp>> itpDNF1 = atomHelper.removeConstantsFromItpfDNF(itpAtoms);
            List<List<ItpfItp>> itpDNF2 = atomHelper.removeNEQ(itpDNF1);
            List<ItpfItp> dpSquareVarsItps = atomHelper.getVarsGeqZero(squareVars);
            List<List<ItpfItp>> itpDNF3 = atomHelper.conjoinToDNF(dpSquareVarsItps, itpDNF2);

            for (List<ItpfItp> itpConjuncts : itpDNF3) {
                squareVars = new ArrayList<TRSVariable>();
                List<Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>>> polyConjuncts =
                          new ArrayList<Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>>>();
                for (ItpfItp itpAtom : itpConjuncts) {
                    ItpfItp itp = (ItpfItp) itpAtom;
                    Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>> exportee =
                        IDPMCNPProcessor.itpToExportee(itp, predefinedMap, callSymsNonBool,
                                times, squareVars, nameGen, interpretation, aborter);
                    if (exportee != null) {
                        polyConjuncts.add(exportee);
                    }
                    // in case of doubt, over-approximate the condition by omitting the conjunct
                }
                // also deal with the knowledge in the square variables from the ItpfItps
                for (TRSVariable squareVar : squareVars) {
                    Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>> sqGEzero =
                            IDPMCNPProcessor.exportSquareVar(squareVar, interpretation, predefinedMap, aborter);
                    polyConjuncts.add(sqGEzero);
                }
                // and connect program point argument vars with the interpretations
                polyConjuncts.addAll(lArgInterWithVar);
                polyConjuncts.addAll(rArgInterWithVar);

                IDPMCNPProcessor.dump(leftProgramPoint, result);
                IDPMCNPProcessor.dump(" :- ", result);
                IDPMCNPProcessor.dump("[", result);
                {
                    boolean first = true;
                    for (Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>> cond : polyConjuncts) {
                        if (first) {
                            first = false;
                        }
                        else {
                            IDPMCNPProcessor.dump(", ", result);
                        }
                        IDPMCNPProcessor.dump(IDPMCNPProcessor.polyToExportedPoly(cond.x, interpretation), result);
                        IDPMCNPProcessor.dump(" ", result);
                        IDPMCNPProcessor.dump(cond.y.toString(), result);
                        IDPMCNPProcessor.dump(" ", result);
                        IDPMCNPProcessor.dump(IDPMCNPProcessor.polyToExportedPoly(cond.z, interpretation), result);
                    }
                }
                IDPMCNPProcessor.dump("]; ", result);
                IDPMCNPProcessor.dump(rightProgramPoint, result);
                IDPMCNPProcessor.dump(".\n", result);
                // assemble them interpreted args to an output in
                // Prolog clause style format

                // for now just dump the interpreted DPs;
                // TODO deductions like "x+1 > x" (or more sophisticated ones,
                // of course) and inclusion of constants as arguments in export
            }

            // TODO these exist for a breakpoint to be possible
            List<Object> foo = new LinkedList<Object>();
            foo.clear();

            // TODO integrate Theorem: x^2 >= x holds for all x in Z
        }
        //throw new RuntimeException("MCNP export Not Yet Implemented");
        //dump("#################################\n");
        String resultString = result.toString();
        return resultString;
    }

    /**
     * @param fApp
     * @param callSyms
     * @param nameGen
     * @return a variant of fApp where all arguments which contain symbols
     *  from callSyms have been replaced by fresh variables as generated by
     *  nameGen
     */
    private static TRSFunctionApplication replaceCallsByFreshVars(TRSFunctionApplication fApp,
            Set<FunctionSymbol> callSyms, MCNPNameGenerator nameGen) {
        ImmutableList<TRSTerm> args = fApp.getArguments();
        int size = args.size();
        ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(size);
        boolean changed = false;
        for (int i = 0; i < size; ++i) {
            TRSTerm arg = args.get(i);
            Set<FunctionSymbol> argSyms = arg.getFunctionSymbols();
            if (java.util.Collections.disjoint(callSyms, argSyms)) {
                newArgs.add(arg);
            }
            else {
                String newName = nameGen.getNextName();
                TRSVariable newVar = TRSTerm.createVariable(newName);
                newArgs.add(newVar);
                changed = true;
            }
        }
        TRSFunctionApplication res;
        if (changed) {
            FunctionSymbol f = fApp.getRootSymbol();
            res = TRSTerm.createFunctionApplication(f, newArgs);
        }
        else {
            res = fApp;
        }
        return res;
    }

    /**
     * @param fApp - to have its products abstracted; we assume that all
     *  terms of the shape "t*t" may be abstracted to a non-negative
     *  number (if t can be rewritten by non-confluent rules, this need not
     *  be the case!); a safe condition is that these t do not contain any
     *  user-defined defined symbols
     * @param times - predefined function symbol for the multiplication
     *  operator (non-null)
     * @param squareVars - non-null; here the variables that are known
     *  to be >= 0 (obtained from abstracting t*t) will be added
     * @param nameGen - to be used for the fresh vars
     * @return the term where products have been abstracted
     */
    private static TRSFunctionApplication replaceTimesByFreshVarsInDP(TRSFunctionApplication fApp,
            FunctionSymbol times, List<TRSVariable> squareVars, MCNPNameGenerator nameGen) {
        ImmutableList<TRSTerm> args = fApp.getArguments();
        int size = args.size();
        ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(size);
        for (int i = 0; i < size; ++i) {
            TRSTerm arg = args.get(i);
            TRSTerm newArg = IDPMCNPProcessor.replaceTimesByFreshVars(arg, times, squareVars, nameGen);
            newArgs.add(newArg);
        }
        FunctionSymbol f = fApp.getRootSymbol();
        TRSFunctionApplication res = TRSTerm.createFunctionApplication(f, newArgs);
        return res;
    }

    /**
     *
     * @param t
     * @param times non-null
     * @param squareVars
     * @param nameGen
     * @return
     */
    private static TRSTerm replaceTimesByFreshVars(TRSTerm t,
            FunctionSymbol times, List<TRSVariable> squareVars, MCNPNameGenerator nameGen) {
        List<Position> timesPositions = IDPMCNPProcessor.getTopmostPositionsWithTwoNonGroundArgs(times, t);
        // - replace by a fresh variable x
        for (Position pos : timesPositions) {
            // the substitute!
            TRSVariable x = nameGen.getNextTermVariable();

            // the substituee
            TRSTerm timesTerm = t.getSubterm(pos);
            if (Globals.useAssertions) {
                assert ! timesTerm.isVariable();
            }
            TRSFunctionApplication timesApp = (TRSFunctionApplication) timesTerm;
            if (Globals.useAssertions) {
                assert timesApp.getRootSymbol().getArity() == 2;
            }
            // - if the corresponding two args are equal,
            //   we know that X will always be >= 0
            TRSTerm arg0 = timesApp.getArgument(0);
            TRSTerm arg1 = timesApp.getArgument(1);
            if (arg0.equals(arg1)) {
                squareVars.add(x);
            }
            t = t.replaceAt(pos, x);
        }
        return t;
    }

    /**
     * @param f
     * @param t
     * @return those positions p in t such that t|p = f(...) and for all
     *  proper prefixes p' of p we have t|p' = g(...) for g != f
     */
    private static List<Position> getTopmostPositionsWithTwoNonGroundArgs(FunctionSymbol f,
            TRSTerm t) {
        List<Position> positions = new ArrayList<Position>();
        IDPMCNPProcessor.collectTopmostPositionsWithTwoNonGroundArgs(f, t, Position.create(), positions);
        return positions;
    }

    /**
     * @param g - the symbol we are looking for
     * @param t
     * @param pos - assumed position of (sub-)term t in the term of interest
     * @param positions - results shall be added here
     */
    private static void collectTopmostPositionsWithTwoNonGroundArgs(FunctionSymbol g,
            TRSTerm t, Position pos, List<Position> positions) {
        if (! t.isVariable()) {
            TRSFunctionApplication fApp = (TRSFunctionApplication) t;
            FunctionSymbol rootSym = fApp.getRootSymbol();
            List<TRSTerm> args = fApp.getArguments();
            int size = args.size();
            boolean positionFound = false;
            if (g.equals(rootSym)) { // this position could be interesting
                int nonGroundFound = 0;
                for (int i = 0; i < size; i++) {
                    TRSTerm arg = args.get(i);
                    if (!arg.isGroundTerm()) {
                        ++nonGroundFound;
                    }
                }
                if (nonGroundFound >= 2) {
                    positionFound = true; // this position /is/ interesting
                    positions.add(pos); // no recursive calls below this position!
                }
            }
            if (! positionFound) { // keep going, the current position is not interesting
                for (int i = 0; i < size; i++) {
                    TRSTerm arg = args.get(i);
                    if (!arg.isGroundTerm()) { // ground terms are not interesting
                        Position posArg = pos.append(i);
                        IDPMCNPProcessor.collectTopmostPositionsWithTwoNonGroundArgs(g, arg, posArg, positions);
                    }
                }
            }
        }
    }

    private static Set<FunctionSymbol> getCallSyms(IDPProblem origIdp,
            boolean dropContextSensitiveSymbols,
            boolean dropBooleanSymbols) {
        Set<FunctionSymbol> res = new LinkedHashSet<FunctionSymbol>();
        res.addAll(origIdp.getRuleAnalysis().getDefinedSymbols());
        if (dropBooleanSymbols || dropContextSensitiveSymbols) {
            IDPRuleAnalysis ruleAnalysis = origIdp.getRuleAnalysis();
            IDPPredefinedMap predefMap = ruleAnalysis.getPreDefinedMap();
            Collection<FunctionSymbol> predefDefSyms = predefMap.getPredefinedFunctionSymbols();
            for (FunctionSymbol f : predefDefSyms) {
                if (dropContextSensitiveSymbols && predefMap.isDivOrMod(f)) {
                    // context-sensitive syms DIV and MOD become important
                    res.add(f);
                }
                if (dropBooleanSymbols) {
                    // drop anything Boolean - we get the info from
                    // the graph anyway
                    PredefinedFunction<? extends Domain> pf = predefMap.getPredefinedFunction(f);
                    if (pf.isRelation()) {
                        res.add(f);
                    }
                }
            }

            if (dropBooleanSymbols) {
                // still missing: the two constructors
                // (if we have predefined Booleans in our problem, that is)
                PfBoolean pfTrue = predefMap.getBooleanTrue();
                PfBoolean pfFalse = predefMap.getBooleanFalse();
                if (pfTrue != null) {
                    res.add(pfTrue.getSym());
                }
                if (pfFalse != null) {
                    res.add(pfFalse.getSym());
                }
            }
        }
        return res;
    }

    /**
     *
     * @param itp - to be exported
     * @param predefinedMap
     * @param callSyms
     * @param times - the FunctionSymbol for pre-defined '*'
     * @param squareVars - will have fresh variables added to it
     *  where we know that their value is >= 0
     * @param nameGen - used for generating the fresh vars
     * @return null if there's some symbol from callSyms in itp,
     *  otherwise (p rel q) which we will want to export.
     */
    private static Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>> itpToExportee(ItpfItp itp,
            IDPPredefinedMap predefinedMap, Set<FunctionSymbol> callSyms,
            FunctionSymbol times, List<TRSVariable> squareVars,
            MCNPNameGenerator nameGen, IDPGInterpretation interpretation,
            Abortion aborter) throws AbortionException {
        TRSTerm itpLeft = itp.getL();
        TRSTerm itpRight = itp.getR();

        // post-process itpLeft, itpRight
        // - may contain /, %, user-defined defined syms -> ignore them altogether (DONE)
        // - may contain * -> ignore it unless we can deduce that this
        //   occurrence of * will always be applied on two equal normal forms;
        //   then we introduce a fresh variable at these positions and remember
        //   that it is >= 0

        Set<FunctionSymbol> leftSyms = itpLeft.getFunctionSymbols();
        Set<FunctionSymbol> rightSyms = itpRight.getFunctionSymbols();
        // don't use conditions with pre-defined defined symbols or / or %
        // for now - avoid looking at those nasty (General) Usable Rules
        if (! java.util.Collections.disjoint(callSyms, leftSyms)) {
            return null;
        }
        if (! java.util.Collections.disjoint(callSyms, rightSyms)) {
            return null;
        }
        if (times != null) {
            itpLeft = IDPMCNPProcessor.replaceTimesByFreshVars(itpLeft, times, squareVars, nameGen);
            itpRight = IDPMCNPProcessor.replaceTimesByFreshVars(itpRight, times, squareVars, nameGen);
        }
        ItpRelation rel = itp.getRelation();
        if (rel.isRewriteRel()) { // exportable as such, that's equality here
            OrderPoly<BigIntImmutable> polyLeft = interpretation.interpretTerm(itpLeft, aborter);
            OrderPoly<BigIntImmutable> polyRight = interpretation.interpretTerm(itpRight, aborter);
            return new Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>>(polyLeft, Relation.EQ, polyRight);
        }
        // use Thm. 6.48 of DA Pluecker in the other case
        Relation relString = IDPMCNPProcessor.computeRelationString(rel, predefinedMap);
        OrderPoly<BigIntImmutable> polyLeft = interpretation.interpretTerm(itpLeft, aborter);
        OrderPoly<BigIntImmutable> polyRight = interpretation.interpretTerm(itpRight, aborter);

        return new Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>>(polyLeft, relString, polyRight);
    }


    /**
     * @param squareVar
     * @param interpretation
     * @param predefinedMap
     * @return "squareVar >= 0"
     */
    private static Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>>
            exportSquareVar(TRSVariable squareVar, IDPGInterpretation interpretation,
                    IDPPredefinedMap predefinedMap,
                    Abortion aborter) throws AbortionException {
        OrderPoly<BigIntImmutable> squareVarPoly = interpretation.interpretTerm(squareVar, aborter);
        TRSTerm zeroTerm = predefinedMap.getInt(BigIntImmutable.ZERO, DomainFactory.INTEGERS).getTerm();
        OrderPoly<BigIntImmutable> zeroPoly = interpretation.interpretTerm(zeroTerm, aborter);
        return new Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>>
            (squareVarPoly, Relation.GE, zeroPoly);
    }

    private static Relation computeRelationString(ItpRelation itpRel,
            IDPPredefinedMap predefinedMap) {
        assert ! itpRel.isRewriteRel();
        switch (itpRel) {
        case EQ : return Relation.EQ;
        case ABSTRACT_GE : return Relation.GE;
        case ABSTRACT_GT : return Relation.GT;
        default : throw new MCNPException("Unexpected ITP relation " + itpRel + "!");
        }
    }

    private static String polyToExportedPoly(OrderPoly<BigIntImmutable> poly,
            IDPGInterpretation interpretation) {
        FlatteningVisitor<BigIntImmutable, GPolyVar> fvInner = interpretation.getFvInner();
        FlatteningVisitor<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> fvOuter = interpretation.getFvOuter();
        PLAIN_Util eu = new PLAIN_Util();
        String exportedPoly = poly.exportFlatDeep(fvInner, fvOuter, eu);
        return exportedPoly;
    }

    /**
     * @param f - name of a "program point" (here: a tuple symbol)
     * @param argPol - [(var_0 = p_0), ..., (var_{n-1} = p_{n-1})]
     * @return "pf(var_0, ..., var_{n-1})"
     */
    private static String toProtoProgramPoint(FunctionSymbol f,
            List<Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>>> argPol,
            IDPGInterpretation interpretation) {
        StringBuilder res = new StringBuilder();
        res.append(IDPMCNPProcessor.PROGRAM_POINT_PREFIX);
        res.append(f); // arity export is intentional to avoid clashes
        if (! argPol.isEmpty()) { // nullary predicates do not take parenthesis
            res.append('(');
            boolean first = true;
            for (Triple<OrderPoly<BigIntImmutable>, Relation, OrderPoly<BigIntImmutable>> varEQpoly : argPol) {
                if (first) {
                    first = false;
                }
                else {
                    res.append(", ");
                }
                String exportedVar = IDPMCNPProcessor.polyToExportedPoly(varEQpoly.x, interpretation);
                res.append(exportedVar);
            }
            res.append(')');
        }
        return res.toString();
    }

    /**
     * @param interpretation
     * @param fApp - f(t_1, ..., t_n)
     * @return [interpretation(t_1), ..., interpretation(t_n)],
     *  list may be modified
     */
    private static List<OrderPoly<BigIntImmutable>> interpretArgs(
            IDPGInterpretation interpretation, TRSFunctionApplication fApp,
            Abortion aborter) throws AbortionException {
        List<TRSTerm> args = fApp.getArguments();
        int argsSize = args.size();
        List<OrderPoly<BigIntImmutable>> res = new ArrayList<OrderPoly<BigIntImmutable>>();
        for (int i = 0; i < argsSize; ++i) {
            OrderPoly<BigIntImmutable> argPoly = interpretation.interpretTerm(args.get(i), aborter);
            res.add(argPoly);
        }
        return res;
    }

    private static void dump(String s, StringBuilder sb) {
        sb.append(s);
    }

    /**
     * Reads off the relations (stored in Itps) from the edges of the
     * IDP graph in such a way that we can use them for (exporting)
     * monotonicity constraints. To be used on a DNF, so only a single "or"
     * is allowed.
     */
    protected static class ItpExtractVisitor extends IItpfVisitor.ItpfVisitorSkeleton<Object> {

        private final IDPRuleAnalysis ruleAnalysis;
        private final List<List<ItpfAtom>> itpDNF;
        private boolean orSeen;

        public ItpExtractVisitor(IDPRuleAnalysis ruleAnalysis, ApplicationMode mode) {
            super(ItpfMark.MCNPRelExtract, mode);
            this.ruleAnalysis = ruleAnalysis;
            this.itpDNF = new ArrayList<List<ItpfAtom>>();
            this.orSeen = false;
        }

        @Override
        public boolean fcaseAnd(ItpfAnd and) {
            this.itpDNF.add(new ArrayList<ItpfAtom>());
            return true;
        }

        @Override
        public boolean fcaseNeg(ItpfNeg neg) {
            throw new MCNPException(neg + " cannot be used for MCNP!");
        }

        @Override
        public boolean fcaseOr(ItpfOr or) {
            if (! this.orSeen) {
                this.orSeen = true;
                return true;
            }
            else {
                throw new MCNPException(or + " cannot be used for MCNP!");
            }
        }

        @Override
        public boolean fcaseExists(ItpfExists exists) {
            throw new MCNPException(exists + " cannot be used for MCNP!");
        }

        @Override
        public boolean fcaseAll(ItpfAll all) {
            throw new MCNPException(all + " cannot be used for MCNP!");
        }

        @Override
        public boolean fcaseUra(ItpfUra ura) {
            Set<FunctionSymbol> uraSyms = ura.getFunctionSymbols();
            // URAs may contain predefined defined (sic!) symbols and
            // constructor symbols (predefined or not), but no
            // user-defined defined (sic again!) symbols
            if (java.util.Collections.disjoint(uraSyms, this.ruleAnalysis.getDefinedSymbols())) {
                return true;
            }
            throw new MCNPException(ura + " contains user-defined defined symbols!");
        }

        @Override
        public boolean fcaseItp(ItpfItp tp) {
            return true; // enter shared Itps multiple times
        }

        @Override
        public Itpf caseItp(ItpfItp tp) {
            int size = this.itpDNF.size();
            List<ItpfAtom> conjuncts;
            if (size == 0) { // no "and" encountered, so we have just an atom
                conjuncts = new ArrayList<ItpfAtom>();
                conjuncts.add(tp);
                this.itpDNF.add(conjuncts);
            }
            else {
                conjuncts = this.itpDNF.get(size-1);
                conjuncts.add(tp);
            }
            return this.mark(tp, tp);
        }

        @Override
        public Itpf caseTrue(ItpfTrue tru) {
            int size = this.itpDNF.size();
            List<ItpfAtom> conjuncts;
            if (size == 0) { // no "and" encountered, so we have just an atom
                conjuncts = new ArrayList<ItpfAtom>();
                conjuncts.add(tru);
                this.itpDNF.add(conjuncts);
            }
            else {
                conjuncts = this.itpDNF.get(size-1);
                conjuncts.add(tru);
            }
            return this.mark(tru, tru);
        }

        @Override
        public Itpf caseFalse(ItpfFalse fals) {
            int size = this.itpDNF.size();
            List<ItpfAtom> conjuncts;
            if (size == 0) { // no "and" encountered, so we have just an atom
                conjuncts = new ArrayList<ItpfAtom>();
                conjuncts.add(fals);
                this.itpDNF.add(conjuncts);
            }
            else {
                conjuncts = this.itpDNF.get(size-1);
                conjuncts.add(fals);
            }
            return this.mark(fals, fals);
        }

        public List<List<ItpfAtom>> getItpDNF() {
            return this.itpDNF;
        }
    }


    private static final class IDPMCNPProof extends Proof.DefaultProof {
        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return "Nothing to see here yet.";
        }
    }

    /**
     * To be thrown whenever one of the underlying assumptions in MCNP
     * processing is violated.
     */
    public static final class MCNPException extends RuntimeException {

        private static final long serialVersionUID = -3090382991290996064L;

        public MCNPException() {
            super();
        }

        public MCNPException(String message) {
            super(message);
        }
    }

    public static class Arguments {
        public boolean dropBooleanSymbols = true;
        public boolean dropContextSensitiveSymbols = true;
        public boolean toStdOut = false;
        public String dumpPath = "/tmp";
    }
}
