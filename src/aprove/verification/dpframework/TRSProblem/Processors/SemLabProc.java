package aprove.verification.dpframework.TRSProblem.Processors;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.Parameters.*;
import aprove.strategies.UserStrategies.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.MaxMinPolynomials.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Rewriting.SemanticLabelling.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

public class SemLabProc extends Processor.ProcessorSkeleton {

    private final static Logger log = Logger.getLogger("aprove.verification.dpframework.TRSProblem.Processors.SemLabProc");

    private final static Set<Integer> primes = SemLabProc.fillPrimes();
    private final static UserStrategy strategy =
        StrategyTranslator
            .strategyFragment("QTRSDependencyPairs:RepeatS(1,*,First(QDPDependencyGraph, QDPMNOC, QDPUsableRules , QDPQReduction, First(QDPSizeChange[Subterm = True], Timer(8000,QDPUsableRulesRP[Range = 2]), Timer(8000, QDPRuleRemoval[Range = 2])), Any(Timer(20000, QDPPolo[Engine=SAT4J]) , Timer(8000, QDPNegPolo[Range=-1]), Timer(12000, QDPReductionPair[Order=LPO[Quasi=True]])), QDPReductionPair[Order=POLO]))");

    private final int carrierSetSize; // Convention: If cSS = -1 use the natural numbers as carrier!
    private final boolean allowQuasi;
    private final Engine engine;

    @ParamsViaArgumentObject
    public SemLabProc(final Arguments arguments) {
        this.allowQuasi = arguments.allowQuasi;
        this.carrierSetSize = arguments.carrierSetSize;
        this.engine = arguments.engine;
    }

    @Override
    public boolean isApplicable(final BasicObligation bobl) {
        return ((bobl instanceof QTRSProblem) && !((QTRSProblem) bobl).getR().isEmpty());
    }

    @Override
    public Result process(
        final BasicObligation bobl,
        final BasicObligationNode oblNode,
        final Abortion aborter,
        final RuntimeInformation rti) throws AbortionException
    {
        int droppedByLabelConditions = 0;
        final QTRSProblem qtrs = (QTRSProblem) bobl;
        final Set<Rule> rules = qtrs.getR();
        Set<Rule> decrRules = null;
        Set<TRSFunctionApplication> labQTerms = null;
        final LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap =
            new LinkedHashMap<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>>();

        if (this.carrierSetSize < 2) {
            final FuncArityTransformer transformer = new FuncArityTransformer();
            final Quadruple<Set<TRSFunctionApplication>, Set<Rule>, Pair<Pair<Set<FunctionSymbol>, Set<FunctionSymbol>>, Boolean>, Map<TRSFunctionApplication, TRSFunctionApplication>> transformInformation =
                transformer.transform(qtrs);
            final MyLabeller labeller = new MyLabeller(rules, transformInformation.z);
            final Set<Rule> labelRules = new LinkedHashSet<Rule>(labeller.calculateLabelRules());
            final long sysnanosearchstart = System.nanoTime();
            final ModelSearch modelSearch =
                new ModelSearch(transformInformation.x, -1, this.allowQuasi, transformInformation.y.y);
            final LinkedList<MyModel> modelList = modelSearch.getAllModels();
            final long sysnanosearchend = System.nanoTime();
            if (Globals.DEBUG_PATWIE) {
                System.out.println("\n******************");
                System.out
                    .println("Komplette Modelsuche: " + (sysnanosearchend - sysnanosearchstart) / 1000000 + "ms.");
            }
            /*
            log.log(Level.INFO, "Anzahl der (Quasi-)Modelle: " + modelList.size());
            for (MyModel model : modelList) {
                log.log(Level.INFO, "\n"+model);
            }
            */
            /*
            if(Globals.DEBUG_PATWIE) {
                System.out.println("\nNumber of (Quasi-) Models: "+ modelList.size());
                printOnScreen(2, modelList.subList(0, 1), transformInformation.x, qtrs.getR());
                int i = 0;
                while(i<modelList.size() && modelList.get(i).getStatus() != InterpretationStatus.Quasi) {
                    i++;
                }
                if(i<modelList.size()){
                    LinkedHashSet<Rule> labelRules = labeller.labelRules(modelList.get(i));
                    System.out.println("\nRules and labelled rules:");
                    for (Rule r : rules) {
                        System.out.println(r.toString());
                    }
                    System.out.println();

                    for(Rule lr : labelRules) {
                        System.out.println(lr.toString());
                    }
               }
            }
            */
            if (this.allowQuasi) {
                if (Globals.useAssertions) {
                    assert (decrRules == null);
                }
                decrRules = labeller.calculateDecreasingRules();
            }
            if (Globals.useAssertions) {
                assert (labQTerms == null);
            }
            labQTerms = labeller.labelQTerms(transformInformation.w);

            for (final MyModel m : modelList) {
                LinkedHashSet<Rule> labelledRules;
                final boolean quasi = (m.getStatus() == InterpretationStatus.Quasi);
                labelledRules = labeller.labelRules(m);
                if (labelledRules.isEmpty()) {
                    droppedByLabelConditions++;
                    continue;
                }
                final LinkedHashSet<Rule> allRules = new LinkedHashSet<Rule>(labelledRules);
                if (m.getStatus() == InterpretationStatus.Quasi) {
                    allRules.addAll(decrRules);
                }
                allRules.addAll(labelRules);
                final QTRSProblem labelledTRS =
                    QTRSProblem.create(ImmutableCreator.create(allRules), ImmutableCreator.create(labQTerms));

                final BasicObligationNode labelledTRSNode = new BasicObligationNode(labelledTRS);
                final long sysnanoproofstart = System.nanoTime();
                final StrategyExecutionHandle handle =
                    Machine.theMachine.startSubMachine(
                        SemLabProc.strategy,
                        null,
                        labelledTRSNode,
                        null,
                        aborter.getClocks(),
                        false);

                HandleChecker.check(handle, aborter);

                final long sysnanoproofend = System.nanoTime();
                if (Globals.DEBUG_PATWIE) {
                    System.out.println("\n******************");
                    System.out.println("Komplette Modelsuche: "
                        + (sysnanosearchend - sysnanosearchstart)
                        / 1000000
                        + "ms.");
                    System.out.println("Beweissuche : " + (sysnanoproofend - sysnanoproofstart) / 1000000 + "ms.");
                    System.out.println("******************");
                }
                // okay, we have the result after the strategy
                final ExecutableStrategy result = handle.getResult();
                if (result.isFail()) {
                    continue; // we have not performed one step, so unlabelling will result in the original TRS.
                } else {

                    Set<Rule> finalRRules;
                    final List<BasicObligationNode> newProblems = ((Success) result).getPositions();
                    if (newProblems.isEmpty()) {
                        // hooray, we have proven it completely.
                        finalRRules = null;
                    } else {
                        // collect new P and R
                        finalRRules = new LinkedHashSet<Rule>(allRules.size());
                        for (final BasicObligationNode resOblNode : newProblems) {
                            final QDPProblem labelledQDPAfterProc = (QDPProblem) resOblNode.getBasicObligation();
                            for (final Rule rule : labelledQDPAfterProc.getR()) {
                                if (!allRules.contains(rule)) {
                                    if (Globals.useAssertions) {
                                        assert (false) : "semlab used with rule modyfying processor";
                                    } else {
                                        return ResultFactory
                                            .unsuccessful("semlab was invoked with a strategy changing rules!");
                                    }
                                }
                            }
                            //to get rid of decr rules
                            if (quasi) {
                                allRules.removeAll(decrRules);
                            }
                            allRules.removeAll(labelRules);
                            finalRRules = labeller.unlabelRules(allRules);
                        }

                        if (finalRRules.size() == rules.size()) {
                            continue; // we have gained nothing
                        }
                    }

                    SemLabProc.log.log(Level.INFO, "\n\nDropped "
                        + droppedByLabelConditions
                        + " of "
                        + modelList.size()
                        + " models by labelling conditions\n");
                    // okay, we have successfully applied semlab.
                    // now build final result
                    if (finalRRules == null) {
                        final Proof proof = new SemLabProof(labelledTRS, quasi, m, xmlLabelMap, qtrs);
                        final ExecutableStrategy succStrategy = Success.EMPTY;
                        return ResultFactory.provedWithNewStrategy(
                            labelledTRSNode,
                            YNMImplication.SOUND,
                            proof,
                            succStrategy);
                    } else {
                        final QTRSProblem finalQTRS = qtrs.createSubProblem(ImmutableCreator.create(finalRRules));
                        final Proof proof2 = new SemLabProof2(qtrs, finalQTRS);
                        final Processor proc = new Processor.ProcessorSkeleton() {

                            @Override
                            public Result process(
                                final BasicObligation obl,
                                final BasicObligationNode oblNode,
                                final Abortion aborter,
                                final RuntimeInformation rti) throws AbortionException
                            {
                                return ResultFactory.proved(finalQTRS, YNMImplication.EQUIVALENT, proof2);
                            }

                            @Override
                            public boolean isApplicable(final BasicObligation obl) {
                                return true;
                            }

                        };
                        final Proof proof = new SemLabProof(labelledTRS, quasi, m, xmlLabelMap, qtrs);
                        final ExecutableStrategy exStr =
                            new ExecProcessorStrategy(proc, oblNode, rti, "SemLabInt", "<internal>");
                        return ResultFactory.provedWithNewStrategy(labelledTRSNode, YNMImplication.SOUND, proof, exStr);
                    }
                }
            } // end of model-iteration
            SemLabProc.log.log(Level.INFO, "\n\nDropped "
                + droppedByLabelConditions
                + " of "
                + modelList.size()
                + " models by labelling conditions\n");
            return ResultFactory.unsuccessful();

        }

        else {
            //Work on finite carrier
            if (SemLabProc.isPrime(this.carrierSetSize)) {
                final FuncArityTransformerFiniteCarrier transformer = new FuncArityTransformerFiniteCarrier();
                final Quadruple<Set<TRSFunctionApplication>, Set<Rule>, Pair<Set<FunctionSymbol>, Boolean>, Map<TRSFunctionApplication, TRSFunctionApplication>> transformInformation =
                    transformer.transform(qtrs);

                final long sysnanosearchfinitestart = System.nanoTime();
                final ModelSearch modelSearch =
                    new ModelSearch(
                        transformInformation.x,
                        this.carrierSetSize,
                        this.allowQuasi,
                        transformInformation.y.y);
                final LinkedList<MyModel> modelList = modelSearch.getAllModels();
                final long sysnanosearchfiniteend = System.nanoTime();
                final Iterator<MyModel> modelIter = modelList.iterator();
                int dropped = 0;
                int count = 0;
                while (modelIter.hasNext()) {
                    count++;
                    final MyModel m = modelIter.next();
                    final MyFiniteLabeller labeller = new MyFiniteLabeller(rules, transformInformation.z, m);
                    if (decrRules == null && this.allowQuasi) {
                        decrRules = labeller.getDecreasingRules(xmlLabelMap);
                    }
                    labQTerms = labeller.labelQterms(qtrs.getQ().getTerms());
                    final Collection<Pair<Rule, Collection<Rule>>> labelledR =
                        new ArrayList<Pair<Rule, Collection<Rule>>>(rules.size());
                    final LinkedHashSet<Rule> labelledRules = new LinkedHashSet<Rule>();
                    for (final Rule rule : rules) {
                        final Collection<Rule> lRules = new ArrayList<Rule>();
                        labeller.addLabeled(rule, lRules, xmlLabelMap);
                        labelledR.add(new Pair<Rule, Collection<Rule>>(rule, lRules));
                        labelledRules.addAll(lRules);
                    }

                    //check effective labelling
                    if (Labeller.EffectiveChecker.checkIneffective(labelledR, labeller, this.engine, aborter)) {
                        dropped++;
                        continue;
                    }
                    final boolean quasi = (m.getStatus() == InterpretationStatus.Quasi);
                    if (quasi) {
                        final boolean bugfixbool = MyModel.weaklyCheck(m.getInterpretation());
                        if (bugfixbool) {
                            labelledRules.addAll(decrRules);
                        } else {
                            continue;
                        }
                    }
                    final QTRSProblem labelledTRS =
                        QTRSProblem.create(ImmutableCreator.create(labelledRules), ImmutableCreator.create(labQTerms));

                    final BasicObligationNode labelledTRSNode = new BasicObligationNode(labelledTRS);
                    final StrategyExecutionHandle handle =
                        Machine.theMachine.startSubMachine(
                            SemLabProc.strategy,
                            rti.getProgram(),
                            labelledTRSNode,
                            null,
                            aborter.getClocks(),
                            false);
                    final long sysnanoprooffinitestart = System.nanoTime();
                    // this waiting loop may be improved, but it should be okay in the first run
                    while (true) {
                        try {
                            handle.waitForFinish(100); // check every 100 ms
                        } catch (final InterruptedException e) {
                            throw new AbortionException("Interrupted");
                        }
                        if (handle.isFinished()) {
                            break;
                        } else {
                            try {
                                aborter.checkAbortion();
                            } catch (final AbortionException e) {
                                handle.stop("SemLab aborted: " + e.getMessage());
                                throw e;
                            }
                        }
                    }
                    final long sysnanoprooffiniteend = System.nanoTime();
                    if (Globals.DEBUG_PATWIE) {
                        System.out.println("\n******************");
                        System.out.println("Komplette Modelsuche: "
                            + (sysnanosearchfiniteend - sysnanosearchfinitestart)
                            / 1000000
                            + "ms.");
                        System.out.println("Beweissuche : "
                            + (sysnanoprooffiniteend - sysnanoprooffinitestart)
                            / 1000000
                            + "ms.");
                        System.out.println("******************");
                    }

                    // okay, we have the result after the strategy
                    final ExecutableStrategy result = handle.getResult();
                    if (result.isFail()) {
                        continue; // we have not performed one step, so unlabelling will result in the original TRS.
                    } else {

                        Set<Rule> finalRRules;
                        final Set<Rule> finalPRules;
                        final List<BasicObligationNode> newProblems = ((Success) result).getPositions();
                        if (newProblems.isEmpty()) {
                            // hooray, we have proven it completely.
                            finalRRules = null;
                        } else {
                            continue;
                        }

                        // okay, we have successfully applied semlab.
                        // now build final result
                        SemLabProc.log.log(Level.INFO, "\n\nDropped "
                            + dropped
                            + " of "
                            + count
                            + " models by effective labelling\n\n\n");
                        if (finalRRules == null) {
                            final Proof proof = new SemLabProof(labelledTRS, quasi, m, xmlLabelMap, qtrs);
                            final ExecutableStrategy succStrategy = Success.EMPTY;
                            return ResultFactory.provedWithNewStrategy(
                                labelledTRSNode,
                                YNMImplication.SOUND,
                                proof,
                                succStrategy);
                        } else {
                            final QTRSProblem finalQTRS = qtrs.createSubProblem(ImmutableCreator.create(finalRRules));
                            final Proof proof2 = new SemLabProof2(qtrs, finalQTRS);
                            final Processor proc = new Processor.ProcessorSkeleton() {

                                @Override
                                public Result process(
                                    final BasicObligation obl,
                                    final BasicObligationNode oblNode,
                                    final Abortion aborter,
                                    final RuntimeInformation rti) throws AbortionException
                                {
                                    return ResultFactory.proved(finalQTRS, YNMImplication.EQUIVALENT, proof2);
                                }

                                @Override
                                public boolean isApplicable(final BasicObligation obl) {
                                    return true;
                                }

                            };
                            final Proof proof = new SemLabProof(labelledTRS, quasi, m, xmlLabelMap, qtrs);
                            final ExecutableStrategy exStr =
                                new ExecProcessorStrategy(proc, oblNode, rti, "SemLabInt", "<internal>");
                            return ResultFactory.provedWithNewStrategy(
                                labelledTRSNode,
                                YNMImplication.SOUND,
                                proof,
                                exStr);
                        }
                    }
                }

            } else {
                return ResultFactory.notApplicable("Carrier size ist not a prime number!");
            }

            return ResultFactory.unsuccessful();
        }
    }

    /**
     * Proof which prints out the resulting QTRSProblem
     */
    private class SemLabProof extends QTRSProof {

        QTRSProblem labelledTRS;
        boolean quasi;
        MyModel actModel;
        private final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap;
        private final QTRSProblem origObl;

        private SemLabProof(
            final QTRSProblem labelledTRS,
            final boolean quasi,
            final MyModel m,
            final Map<FunctionSymbol, Pair<FunctionSymbol, FunctionSymbolAnnotator>> xmlLabelMap,
            final QTRSProblem origObl)
        {
            this.labelledTRS = labelledTRS;
            this.quasi = quasi;
            this.actModel = m;
            this.xmlLabelMap = xmlLabelMap;
            this.origObl = origObl;
        }

        @Override
        public String export(final Export_Util eu, final VerbosityLevel level) {
            final StringBuilder s = new StringBuilder();
            s.append("We found the following " + (this.quasi ? "quasi-" : "") + "model for the rules of the TRS.\n");
            s.append(eu.linebreak());
            s.append(this.actModel.exportInterpretation(eu));
            s.append("By semantic labelling " + eu.cite(Citation.SEMLAB) + " we result in the following labelled TRS.");
            return s.toString();
        }

        @Override
        public XMLMetaData adaptMetaData(final XMLMetaData preData) {
            return new XMLMetaData(this.xmlLabelMap, preData);
        }

    }

    private class SemLabProof2 extends QTRSProof {

        private final QTRSProblem origTrs, resultTrs;

        private SemLabProof2(final QTRSProblem origTrs, final QTRSProblem resultTrs) {
            this.origTrs = origTrs;
            this.resultTrs = resultTrs;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            return "As can be seen after transforming the TRS by semantic labelling "
                + o.cite(Citation.SEMLAB)
                + " and then some rule deleting processors, only certain labelled rules can be used.\n"
                + "Hence, we only have to consider all unlabelled rules (without the decreasing rules for quasi-models).\n";
        }

    }

    private static void printOnScreen(
        final int i,
        final List<MyModel> resultList,
        final Set<Rule> transformedRules,
        final Set<Rule> rules)
    {
        System.out.println();
        if (i == 1) {
            for (final Rule r : transformedRules) {
                System.out.println(r.toString());
            }

            for (final MyModel model : resultList) {
                System.out.println();
                System.out.print(model.toString());

                Pair<MaxMinPolynomial, FunctionSymbol> dPairLeft =
                    new Pair<MaxMinPolynomial, FunctionSymbol>(null, null);
                Pair<MaxMinPolynomial, FunctionSymbol> dPairRight =
                    new Pair<MaxMinPolynomial, FunctionSymbol>(null, null);
                for (final Rule rule : transformedRules) {
                    dPairLeft = model.calculateMMpolyOfTerm(rule.getLeft());
                    System.out.print(dPairLeft.x.toString() + "\t >= ");
                    dPairRight = model.calculateMMpolyOfTerm(rule.getRight());
                    System.out.println(dPairRight.x.toString());
                    //System.out.print(dPairRight.x.toString()+ "\t : ");
                    //System.out.println(dPairLeft.x.monos(dPairRight.x));
                }
                /*
                System.out.println();
                Set<Rule> labelledRules = MyLabeller.labelRules(rules, model);
                for(Rule rule : labelledRules) {
                    System.out.println(rule.toString());
                }
                System.out.println();
                */
            }
        } else {
            for (final Rule r : transformedRules) {
                System.out.println(r.toString());
            }
            for (final MyModel model : resultList) {
                //System.out.print(model.toString());
                Pair<MaxMinPolynomial, FunctionSymbol> dPair1 = new Pair<MaxMinPolynomial, FunctionSymbol>(null, null);
                Pair<MaxMinPolynomial, FunctionSymbol> dPair2 = new Pair<MaxMinPolynomial, FunctionSymbol>(null, null);

                for (final Rule rule : transformedRules) {
                    dPair1 = model.calculateMMpolyOfTerm(rule.getLeft());
                    //System.out.print(dPair1.x.toString() + "\t >= ");
                    dPair2 = model.calculateMMpolyOfTerm(rule.getRight());
                    //System.out.println(dPair2.x.toString());
                    if (!(dPair1.x.monos(dPair2.x).equals(MaxMinPolynomial.ZERO))) {
                        System.out.print("\n" + model.toString());
                        System.out.println(rule.toString());
                        System.out.print(dPair1.x.toString() + "\t >= ");
                        System.out.print(dPair2.x.toString() + "\t >= ");
                        System.out.println(dPair1.x.monos(dPair2.x));
                    }
                }

                // System.out.println();
            }
            System.out.println("\n\nDone!");
        }
    }

    /**
     * private convenience method!
     * Only efficient if number<100!
     * @param number, the prime number candidat
     * @return true if number really is a prime number, false otherwise
     */
    private static boolean isPrime(final int number) {
        if (number < 100) {
            return SemLabProc.primes.contains(number);
        } else {
            final int upperboundary = (int) Math.ceil(Math.sqrt(number));
            boolean stillPrime = true;
            int divisor = 2;
            while (stillPrime && (divisor < upperboundary)) {
                stillPrime = ((number % divisor) == 0);
                divisor++;
            }
            return stillPrime;
        }
    }

    private static Set<Integer> fillPrimes() {
        final HashSet<Integer> dummySet = new HashSet<Integer>();
        dummySet.add(2);
        dummySet.add(3);
        dummySet.add(5);
        dummySet.add(7);
        dummySet.add(11);
        dummySet.add(13);
        dummySet.add(17);
        dummySet.add(19);
        dummySet.add(23);
        dummySet.add(29);
        dummySet.add(31);
        dummySet.add(37);
        dummySet.add(41);
        dummySet.add(43);
        dummySet.add(47);
        dummySet.add(53);
        dummySet.add(59);
        dummySet.add(61);
        dummySet.add(67);
        dummySet.add(71);
        dummySet.add(73);
        dummySet.add(79);
        dummySet.add(83);
        dummySet.add(89);
        dummySet.add(97);
        return Collections.unmodifiableSet(dummySet);
    }

    private class FuncArityTransformer {

        private Pair<Set<FunctionSymbol>, Set<FunctionSymbol>> funcSymbolsOfTRS;
        private final Set<FunctionSymbol> highArityFuncSymbols;
        private final Set<FunctionSymbol> allFuncSymbols;
        private final Map<FunctionSymbol, ArrayList<FunctionSymbol>> freshNamesMap;
        private final Map<TRSFunctionApplication, TRSFunctionApplication> transformedTermMap =
            new HashMap<TRSFunctionApplication, TRSFunctionApplication>();
        private final Set<FunctionSymbol> possibleRootOnlySymbols;
        private final Set<FunctionSymbol> otherSymbols;

        private FuncArityTransformer() {
            this.possibleRootOnlySymbols = new LinkedHashSet<FunctionSymbol>();
            this.otherSymbols = new LinkedHashSet<FunctionSymbol>();
            this.highArityFuncSymbols = new LinkedHashSet<FunctionSymbol>();
            this.allFuncSymbols = new LinkedHashSet<FunctionSymbol>();
            this.freshNamesMap = new HashMap<FunctionSymbol, ArrayList<FunctionSymbol>>();
        }

        /**
         * Calculation of all relevant meta information<br>
         * and replacement of the high arity function symbols in oldRules.
         * @param oldRules the rules of the TRS
         * @return a Quadruple consisting of :<br>
         * w : the transformed qTerms
         * x : the transformed rules
         * y : the signature of the TRS
         * z : a mapping from FApps with high arity FSyms to transformed FApps
         */

        public
            Quadruple<Set<TRSFunctionApplication>, Set<Rule>, Pair<Pair<Set<FunctionSymbol>, Set<FunctionSymbol>>, Boolean>, Map<TRSFunctionApplication, TRSFunctionApplication>>
            transform(final QTRSProblem qtrs)
        {
            //Collect all Function Symbols declared in Rules to avoid duplicate names later on and
            //Collect all Function Symbols with arity bigger than 2 declared in Rules to transform them later on.
            //Store in the boolean if this is a big signature. This information can be used in the model finding process
            //e.g. to speed up the process it is possible to restrict the interpretations for some of the function symbols.
            boolean difficultSignature = false;
            int counter = 0;
            final ImmutableSet<Rule> oldRules = qtrs.getR();
            TRSTerm t;
            for (final Rule rule : oldRules) {
                this.possibleRootOnlySymbols.add(rule.getRootSymbol());
                this.allFuncSymbols.add(rule.getRootSymbol());
                this.otherSymbols.addAll(rule.getLeft().getNonRootFunctionSymbols());
                this.allFuncSymbols.addAll(rule.getLeft().getNonRootFunctionSymbols());
                t = rule.getRight();
                if (!t.isVariable()) {
                    this.possibleRootOnlySymbols.add(((TRSFunctionApplication) t).getRootSymbol());
                    this.allFuncSymbols.add(((TRSFunctionApplication) t).getRootSymbol());
                    this.otherSymbols.addAll(((TRSFunctionApplication) t).getNonRootFunctionSymbols());
                    this.allFuncSymbols.addAll(((TRSFunctionApplication) t).getNonRootFunctionSymbols());
                }
            }
            final ImmutableSet<TRSFunctionApplication> qTerms = qtrs.getQ().getTerms();
            for (final TRSFunctionApplication f : qTerms) {
                this.allFuncSymbols.addAll(f.getFunctionSymbols());
            }

            for (final FunctionSymbol funcSym : this.allFuncSymbols) {
                if (funcSym.getArity() > 2) {
                    this.highArityFuncSymbols.add(funcSym);
                } else {
                    if (funcSym.getArity() == 2) {
                        counter++;
                    }
                }
            }
            if (this.highArityFuncSymbols.size() > 2 || counter > 2) {
                difficultSignature = true;
            }

            this.possibleRootOnlySymbols.removeAll(this.otherSymbols);

            //Create Hashmap for Function Symbols with arity bigger than 2
            //the key is the old Function Symbol
            //the value is a list of new Function Symbols each with arity 2
            //the list has arity of the old Function Symbol minus 1 as length,
            //so e.g. the Function Application f(x, y, z) will be transformed
            //into f1(x, f2(y, z)) later on.
            //Also create Hashmap from the old terms to the transformed terms
            //for the labelling process and the reverse transformation.
            final FreshNameGenerator freshNameGen =
                new FreshNameGenerator(this.allFuncSymbols, FreshNameGenerator.TYPE_INFERENCE);
            for (final FunctionSymbol funcSymb : this.highArityFuncSymbols) {
                final String oldName = funcSymb.getName();
                final int funcSymbArity = funcSymb.getArity();
                final ArrayList<FunctionSymbol> funcSymbArrayList = new ArrayList<FunctionSymbol>((funcSymbArity - 1));
                for (int i = 1; i < funcSymbArity; i++) {
                    final String freshName = freshNameGen.getFreshName(oldName, false);
                    final FunctionSymbol freshNameFuncSymb = FunctionSymbol.create(freshName, 2);
                    funcSymbArrayList.add(freshNameFuncSymb);
                }
                this.freshNamesMap.put(funcSymb, funcSymbArrayList);
            }
            this.funcSymbolsOfTRS =
                new Pair<Set<FunctionSymbol>, Set<FunctionSymbol>>(this.possibleRootOnlySymbols, this.otherSymbols);
            final Pair<Pair<Set<FunctionSymbol>, Set<FunctionSymbol>>, Boolean> dummyPair =
                new Pair<Pair<Set<FunctionSymbol>, Set<FunctionSymbol>>, Boolean>(
                    this.funcSymbolsOfTRS,
                    difficultSignature);

            final Quadruple<Set<TRSFunctionApplication>, Set<Rule>, Pair<Pair<Set<FunctionSymbol>, Set<FunctionSymbol>>, Boolean>, Map<TRSFunctionApplication, TRSFunctionApplication>> resultQuadruple =
                new Quadruple<Set<TRSFunctionApplication>, Set<Rule>, Pair<Pair<Set<FunctionSymbol>, Set<FunctionSymbol>>, Boolean>, Map<TRSFunctionApplication, TRSFunctionApplication>>(
                    this.processQTerms(qTerms),
                    this.processRules(oldRules),
                    dummyPair,
                    this.transformedTermMap);

            return resultQuadruple;
        }

        private LinkedHashSet<Rule> processRules(final Collection<Rule> rules) {
            final LinkedHashSet<Rule> results = new LinkedHashSet<Rule>();
            TRSFunctionApplication newLhs;
            TRSTerm newRhs;
            for (final Rule r : rules) {
                newLhs = (TRSFunctionApplication) this.processTerm(r.getLeft());
                newRhs = this.processTerm(r.getRight());
                results.add(Rule.create(newLhs, newRhs));
            }
            return results;
        }

        private LinkedHashSet<TRSFunctionApplication> processQTerms(final Collection<TRSFunctionApplication> qTerms) {
            final LinkedHashSet<TRSFunctionApplication> labQTerms = new LinkedHashSet<TRSFunctionApplication>(qTerms.size());
            for (final TRSFunctionApplication t : qTerms) {
                labQTerms.add(((TRSFunctionApplication) this.processTerm(t)));
            }
            return labQTerms;
        }

        private TRSTerm processTerm(final TRSTerm oldterm) {
            TRSTerm result;
            // Variables don't need any transformation
            if (oldterm.isVariable()) {
                result = oldterm;
            } else {
                // Constants don't need any transformation
                if (oldterm.getSubTerms().size() == 1) {
                    result = oldterm;
                } else {
                    // oldterm has to be a Function Application with at least one
                    // argument!!
                    // recursiv call to transform all inner function symbols to
                    // arity 2.
                    final TRSFunctionApplication fApp = (TRSFunctionApplication) oldterm;
                    final FunctionSymbol actFSym = fApp.getRootSymbol();
                    final ImmutableList<? extends TRSTerm> args = fApp.getArguments();
                    final ArrayList<TRSTerm> processedArgs = new ArrayList<TRSTerm>();
                    for (final TRSTerm t : args) {
                        processedArgs.add(this.processTerm(t));
                    }
                    final ArrayList<FunctionSymbol> freshNames = this.freshNamesMap.get(actFSym);
                    if (freshNames == null) {
                        //the original fSym actFSym has arity 1 or 2.
                        //It has to be processed here.
                        if (Globals.useAssertions) {
                            final int arity = actFSym.getArity();
                            assert (arity < 3);
                            if (arity == 1) {
                                assert (processedArgs.size() == 1);
                            } else {
                                assert (processedArgs.size() == 2);
                            }
                        }
                        result =
                            TRSTerm.createFunctionApplication(
                                actFSym,
                                ImmutableCreator.create(processedArgs));
                        this.transformedTermMap.put(fApp, ((TRSFunctionApplication) result));

                    } else {
                        final Pair<TRSFunctionApplication, TRSFunctionApplication> resultPair =
                            this.replaceHighArityFSymsRoot(fApp, this.freshNamesMap.get(actFSym));
                        this.transformedTermMap.put(resultPair.x, resultPair.y);
                        result = resultPair.y;
                    }
                }
            }
            return result;
        }

        /**
         * This method is a wrapper for the actual transformation.<br>
         * It is also needed to remember the root position of the term
         * to be transformed.
         * @param fApp the FAppl with the high arity FSym at root position
         * @param freshNames list of "fresh" function symbols with arity 2
         * @return Pair of the old FApp fApp and the transformed fApp.
         */
        private Pair<TRSFunctionApplication, TRSFunctionApplication> replaceHighArityFSymsRoot(
            final TRSFunctionApplication fApp,
            final ArrayList<FunctionSymbol> freshNames)
        {
            TRSFunctionApplication transformedTerm;
            Pair<TRSFunctionApplication, TRSFunctionApplication> result;
            final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(fApp.getArguments());
            for (int i = 0; i < args.size(); i++) {
                final TRSTerm t = args.get(i);
                if (!t.isVariable()) {
                    final TRSFunctionApplication fApplic = (TRSFunctionApplication) t;
                    if (this.transformedTermMap.containsKey(fApplic)) {
                        args.set(i, this.transformedTermMap.get(fApplic));
                    }
                }
            }

            transformedTerm = (TRSFunctionApplication) this.replaceHighArityFSyms(args, freshNames, 0);
            result = new Pair<TRSFunctionApplication, TRSFunctionApplication>(fApp, transformedTerm);
            return result;
        }

        /**
         * This method does the actual transformation.<br>
         *  Replace in every rule the Function Symbols
         *  with arity bigger than 2 by a new construct<br>
         *  e.g. f(v, w, x, y, z) is transformed into
         *  f1( f2(f3(v, w), x), f4(y,z)<br>
         *  The result is a blanced tree!
         * @param args the arguments of the high arity function symbol
         * @param freshNames list of "fresh" function symbols with arity 2
         * @param position an integer, marking the position from where the
         *                 next "fresh" symbol is to be taken
         *
         * @return the transformed term
         */
        private TRSTerm replaceHighArityFSyms(
            final List<TRSTerm> args,
            final ArrayList<FunctionSymbol> freshNames,
            final int position)
        {

            final ArrayList<TRSTerm> arguments = new ArrayList<TRSTerm>(2);
            final int numberOfArgs = args.size();

            if (numberOfArgs == 2) {
                arguments.addAll(args);
                return TRSTerm.createFunctionApplication(
                    freshNames.get(position),
                    ImmutableCreator.create(arguments));
            } else {
                if (numberOfArgs > 2) {
                    int half;
                    if ((numberOfArgs % 2) == 0) {
                        half = (numberOfArgs / 2);
                    } else {
                        half = ((numberOfArgs / 2) + 1);
                    }
                    arguments.add(0, this.replaceHighArityFSyms(args.subList(0, half), freshNames, position + 1));

                    arguments.add(
                        1,
                        this.replaceHighArityFSyms(args.subList(half, numberOfArgs), freshNames, (position + half)));

                    return TRSTerm.createFunctionApplication(
                        freshNames.get(position),
                        ImmutableCreator.create(arguments));
                } else {
                    if (Globals.useAssertions) {
                        assert (args.size() == 1);
                    }
                    return args.get(0);
                }
            }
        }

    }

    private class FuncArityTransformerFiniteCarrier {

        private final Set<FunctionSymbol> funcSymbolsOfTRS;
        private final Set<FunctionSymbol> highArityFuncSymbols;
        private final Map<FunctionSymbol, ArrayList<FunctionSymbol>> freshNamesMap;
        private final Map<TRSFunctionApplication, TRSFunctionApplication> transformedTermMap =
            new HashMap<TRSFunctionApplication, TRSFunctionApplication>();

        private FuncArityTransformerFiniteCarrier() {
            this.funcSymbolsOfTRS = new LinkedHashSet<FunctionSymbol>();
            this.highArityFuncSymbols = new LinkedHashSet<FunctionSymbol>();
            this.freshNamesMap = new HashMap<FunctionSymbol, ArrayList<FunctionSymbol>>();
        }

        /**
         * Calculation of all relevant meta information<br>
         * and replacement of the high arity function symbols in oldRules.
         * @param oldRules the rules of the TRS
         * @return a Quadruple consisting of :<br>
         * w : the transformed qTerms
         * x : the transformed rules
         * y : the signature of the TRS
         * z : a mapping from FApps with high arity FSyms to transformed FApps
         */

        public
            Quadruple<Set<TRSFunctionApplication>, Set<Rule>, Pair<Set<FunctionSymbol>, Boolean>, Map<TRSFunctionApplication, TRSFunctionApplication>>
            transform(final QTRSProblem qtrs)
        {
            //Collect all Function Symbols declared in Rules to avoid duplicate names later on and
            //Collect all Function Symbols with arity bigger than 2 declared in Rules to transform them later on.
            //Store in the boolean if this is a big signature. This information can be used in the model finding process
            //e.g. to speed up the process it is possible to restrict the interpretations for some of the function symbols.
            boolean difficultSignature = false;
            int counter = 0;
            final ImmutableSet<Rule> oldRules = qtrs.getR();
            for (final Rule rule : oldRules) {
                this.funcSymbolsOfTRS.addAll(rule.getFunctionSymbols());
            }
            final ImmutableSet<TRSFunctionApplication> qTerms = qtrs.getQ().getTerms();
            for (final TRSFunctionApplication f : qTerms) {
                this.funcSymbolsOfTRS.addAll(f.getFunctionSymbols());
            }

            for (final FunctionSymbol funcSym : this.funcSymbolsOfTRS) {
                if (funcSym.getArity() > 2) {
                    this.highArityFuncSymbols.add(funcSym);
                } else {
                    if (funcSym.getArity() == 2) {
                        counter++;
                    }
                }
            }
            if (this.highArityFuncSymbols.size() > 2 || counter > 2) {
                difficultSignature = true;
            }

            //Create Hashmap for Function Symbols with arity bigger than 2
            //the key is the old Function Symbol
            //the value is a list of new Function Symbols each with arity 2
            //the list has arity of the old Function Symbol minus 1 as length,
            //so e.g. the Function Application f(x, y, z) will be transformed
            //into f1(x, f2(y, z)) later on.
            //Also create Hashmap from the old terms to the transformed terms
            //for the labelling process and the reverse transformation.
            final FreshNameGenerator freshNameGen =
                new FreshNameGenerator(this.funcSymbolsOfTRS, FreshNameGenerator.TYPE_INFERENCE);
            for (final FunctionSymbol funcSymb : this.highArityFuncSymbols) {
                final String oldName = funcSymb.getName();
                final int funcSymbArity = funcSymb.getArity();
                final ArrayList<FunctionSymbol> funcSymbArrayList = new ArrayList<FunctionSymbol>((funcSymbArity - 1));
                for (int i = 1; i < funcSymbArity; i++) {
                    final String freshName = freshNameGen.getFreshName(oldName, false);
                    final FunctionSymbol freshNameFuncSymb = FunctionSymbol.create(freshName, 2);
                    funcSymbArrayList.add(freshNameFuncSymb);
                }
                this.freshNamesMap.put(funcSymb, funcSymbArrayList);
            }
            final Pair<Set<FunctionSymbol>, Boolean> dummyPair =
                new Pair<Set<FunctionSymbol>, Boolean>(this.funcSymbolsOfTRS, difficultSignature);

            final Quadruple<Set<TRSFunctionApplication>, Set<Rule>, Pair<Set<FunctionSymbol>, Boolean>, Map<TRSFunctionApplication, TRSFunctionApplication>> resultQuadruple =
                new Quadruple<Set<TRSFunctionApplication>, Set<Rule>, Pair<Set<FunctionSymbol>, Boolean>, Map<TRSFunctionApplication, TRSFunctionApplication>>(
                    this.processQTerms(qTerms),
                    this.processRules(oldRules),
                    dummyPair,
                    this.transformedTermMap);

            return resultQuadruple;
        }

        private LinkedHashSet<Rule> processRules(final Collection<Rule> rules) {
            final LinkedHashSet<Rule> results = new LinkedHashSet<Rule>();
            TRSFunctionApplication newLhs;
            TRSTerm newRhs;
            for (final Rule r : rules) {
                newLhs = (TRSFunctionApplication) this.processTerm(r.getLeft());
                newRhs = this.processTerm(r.getRight());
                results.add(Rule.create(newLhs, newRhs));
            }
            return results;
        }

        private LinkedHashSet<TRSFunctionApplication> processQTerms(final Collection<TRSFunctionApplication> qTerms) {
            final LinkedHashSet<TRSFunctionApplication> labQTerms = new LinkedHashSet<TRSFunctionApplication>(qTerms.size());
            for (final TRSFunctionApplication t : qTerms) {
                labQTerms.add(((TRSFunctionApplication) this.processTerm(t)));
            }
            return labQTerms;
        }

        private TRSTerm processTerm(final TRSTerm oldterm) {
            TRSTerm result;
            // Variables don't need any transformation
            if (oldterm.isVariable()) {
                result = oldterm;
            } else {
                // Constants don't need any transformation
                if (oldterm.getSubTerms().size() == 1) {
                    result = oldterm;
                } else {
                    // oldterm has to be a Function Application with at least one
                    // argument!!
                    // recursiv call to transform all inner function symbols to
                    // arity 2.
                    final TRSFunctionApplication fApp = (TRSFunctionApplication) oldterm;
                    final FunctionSymbol actFSym = fApp.getRootSymbol();
                    final ImmutableList<? extends TRSTerm> args = fApp.getArguments();
                    final ArrayList<TRSTerm> processedArgs = new ArrayList<TRSTerm>();
                    for (final TRSTerm t : args) {
                        processedArgs.add(this.processTerm(t));
                    }
                    final ArrayList<FunctionSymbol> freshNames = this.freshNamesMap.get(actFSym);
                    if (freshNames == null) {
                        //the original fSym actFSym has arity 1 or 2.
                        //It has to be processed here.
                        if (Globals.useAssertions) {
                            final int arity = actFSym.getArity();
                            assert (arity < 3);
                            if (arity == 1) {
                                assert (processedArgs.size() == 1);
                            } else {
                                assert (processedArgs.size() == 2);
                            }
                        }
                        result =
                            TRSTerm.createFunctionApplication(
                                actFSym,
                                ImmutableCreator.create(processedArgs));
                        this.transformedTermMap.put(fApp, ((TRSFunctionApplication) result));

                    } else {
                        final Pair<TRSFunctionApplication, TRSFunctionApplication> resultPair =
                            this.replaceHighArityFSymsRoot(fApp, this.freshNamesMap.get(actFSym));
                        this.transformedTermMap.put(resultPair.x, resultPair.y);
                        result = resultPair.y;
                    }
                }
            }
            return result;
        }

        /**
         * This method is a wrapper for the actual transformation.<br>
         * It is also needed to remember the root position of the term
         * to be transformed.
         * @param fApp the FAppl with the high arity FSym at root position
         * @param freshNames list of "fresh" function symbols with arity 2
         * @return Pair of the old FApp fApp and the transformed fApp.
         */
        private Pair<TRSFunctionApplication, TRSFunctionApplication> replaceHighArityFSymsRoot(
            final TRSFunctionApplication fApp,
            final ArrayList<FunctionSymbol> freshNames)
        {
            TRSFunctionApplication transformedTerm;
            Pair<TRSFunctionApplication, TRSFunctionApplication> result;
            final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(fApp.getArguments());
            for (int i = 0; i < args.size(); i++) {
                final TRSTerm t = args.get(i);
                if (!t.isVariable()) {
                    final TRSFunctionApplication fApplic = (TRSFunctionApplication) t;
                    if (this.transformedTermMap.containsKey(fApplic)) {
                        args.set(i, this.transformedTermMap.get(fApplic));
                    }
                }
            }

            transformedTerm = (TRSFunctionApplication) this.replaceHighArityFSyms(args, freshNames, 0);
            result = new Pair<TRSFunctionApplication, TRSFunctionApplication>(fApp, transformedTerm);
            return result;
        }

        /**
         * This method does the actual transformation.<br>
         *  Replace in every rule the Function Symbols
         *  with arity bigger than 2 by a new construct<br>
         *  e.g. f(v, w, x, y, z) is transformed into
         *  f1( f2(f3(v, w), x), f4(y,z)<br>
         *  The result is a blanced tree!
         * @param args the arguments of the high arity function symbol
         * @param freshNames list of "fresh" function symbols with arity 2
         * @param position an integer, marking the position from where the
         *                 next "fresh" symbol is to be taken
         *
         * @return the transformed term
         */
        private TRSTerm replaceHighArityFSyms(
            final List<TRSTerm> args,
            final ArrayList<FunctionSymbol> freshNames,
            final int position)
        {

            final ArrayList<TRSTerm> arguments = new ArrayList<TRSTerm>(2);
            final int numberOfArgs = args.size();

            if (numberOfArgs == 2) {
                arguments.addAll(args);
                return TRSTerm.createFunctionApplication(
                    freshNames.get(position),
                    ImmutableCreator.create(arguments));
            } else {
                if (numberOfArgs > 2) {
                    int half;
                    if ((numberOfArgs % 2) == 0) {
                        half = (numberOfArgs / 2);
                    } else {
                        half = ((numberOfArgs / 2) + 1);
                    }
                    arguments.add(0, this.replaceHighArityFSyms(args.subList(0, half), freshNames, position + 1));

                    arguments.add(
                        1,
                        this.replaceHighArityFSyms(args.subList(half, numberOfArgs), freshNames, (position + half)));

                    return TRSTerm.createFunctionApplication(
                        freshNames.get(position),
                        ImmutableCreator.create(arguments));
                } else {
                    if (Globals.useAssertions) {
                        assert (args.size() == 1);
                    }
                    return args.get(0);
                }
            }
        }

    }

    public static class Arguments {
        public boolean allowQuasi = true;
        public int carrierSetSize = 2;
        public Engine engine;
        // We once had "strategy" and "allowedInterpretations" parameters,
        // but the implementation made no use of them.
    }

}
