package aprove.input.Programs.prolog.processors;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.input.Programs.prolog.*;
import aprove.input.Programs.prolog.processors.PrologToPPiTRSTransformer.AfsModeAnalyser.ModedRule.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class PrologToPPiTRSTransformer extends AbstractPrologToTRSTransformer {

    private final boolean force;
    private final Heuristic heuristic;
    private final boolean modeAnalysis;

    public enum Heuristic {
        IO, IM, OM, IO2, OM2, IM2
    };

    // Just for PrologTest
    public PrologToPPiTRSTransformer() {
        this(new Arguments());
    }

    @ParamsViaArgumentObject
    public PrologToPPiTRSTransformer(final Arguments arguments) {
        this.force = arguments.force;
        this.heuristic = arguments.heuristic;
        this.modeAnalysis = arguments.modeAnalysis;
    }

    public static class Arguments {
        public boolean force;
        public PrologToPPiTRSTransformer.Heuristic heuristic = PrologToPPiTRSTransformer.Heuristic.IM2;
        public boolean modeAnalysis = true;
    }

    public Pair<PPiTRSProblem, Proof> calculatePPiTRSProblem(
        final PrologProblem pp,
        final Afs pi,
        final PrologFNG fridge)
    {
        final Pair<BasicObligation, Proof> p = this.calculateTRSProblem(pp, pi, fridge);
        return new Pair<PPiTRSProblem, Proof>((PPiTRSProblem) p.x, p.y);
    }

    @Override
    public
        Pair<BasicObligation, Proof>
        calculateTRSProblem(final PrologProblem pp, final Afs pi, final PrologFNG fridge)
    {
        if (Globals.useAssertions) {
            assert pp != null;
            assert pi != null && pi.getFunctionSymbols().size() == 1;
        }

        final PrologProgram prologProg = pp.getProgram().copy();

        AbstractPrologToTRSTransformer.logger.log(Level.FINEST, "Dumping prolog program:\n"); //#
        AbstractPrologToTRSTransformer.logger.log(Level.FINEST, prologProg.toString() + "\n"); //#

        prologProg.flattenOutConjunctions();

        prologProg.transformUnderscores();
        final Set<ConditionalRule> conditionals = new LinkedHashSet<ConditionalRule>();

        for (final PrologClause clause : prologProg.getClauses()) {
            conditionals.add(AbstractPrologToTRSTransformer.toConditionalRule(clause, fridge));
        }

        Afs Pi = new Afs(pi);
        Set<GeneralizedRule> R =
            AbstractPrologToTRSTransformer.translate(
                ImmutableCreator.create(conditionals),
                fridge,
                this.identify,
                this.eliminate).x;
        FunctionSymbol startSymbol = Pi.getFunctionSymbols().iterator().next();
        Map<FunctionSymbol, Set<List<Boolean>>> modings = null;

        /* optimazation: do mode analysis */
        if (this.modeAnalysis) {
            final List<Boolean> initialModing = Pi.getRegardedArgsAsList(startSymbol);
            startSymbol = AfsModeAnalyser.fromPair(startSymbol, initialModing);

            AfsSelectionHeuristic heuristic = null;
            switch (this.heuristic) {
            case IO:
                heuristic = new InputOutputHeuristic();
                break;
            case IM:
                heuristic = new InnermostHeuristic();
                break;
            case OM:
                heuristic = new OutermostHeuristic();
                break;
            case IO2:
                heuristic = new InputOutput2Heuristic(new TypeGraph(R));
                break;
            case OM2:
                heuristic = new Outermost2Heuristic(new TypeGraph(R));
                break;
            case IM2:
                heuristic = new Innermost2Heuristic(new TypeGraph(R));
                break;
            }
            final Triple<Set<GeneralizedRule>, Afs, Map<FunctionSymbol, Set<List<Boolean>>>> pair =
                new AfsModeAnalyser(R, Pi, heuristic, this.force).getSplitRules();
            R = pair.x;
            final Set<FunctionSymbol> sig = new LinkedHashSet<FunctionSymbol>();
            sig.add(startSymbol);
            //            for(Map.Entry<FunctionSymbol, Set<List<Boolean>>> symbols : pair.z.entrySet())
            //            {
            //                for(List<Boolean> moding : symbols.getValue()) {
            //                    sig.add(AfsModeAnalyser.fromPair(symbols.getKey(), moding));
            //                }
            //            }
            Pi = pair.y.reduceToSignature(sig);
            modings = pair.z;
        } else {
            //            modings = new LinkedHashMap<FunctionSymbol, Set<List<Boolean>>>();
            //            Set<List<Boolean>> modes = new LinkedHashSet<List<Boolean>>(1);
            //            modes.add(Pi.getRegardedArgsAsList(startSymbol));
            //            modings.put(startSymbol, modes);
        }

        final PPiTRSProblem ppitrs =
            PPiTRSProblem.create(ImmutableCreator.create(R), new ImmutableAfs(Pi), startSymbol);
        return
            new Pair<BasicObligation, Proof>(
                ppitrs,
                new PrologToPPiTRSProof(
                    new PrologProblem(prologProg, pp.getQuery(), pp.getSMTFactory(), pp.getSMTLogic()),
                    ppitrs,
                    R,
                    modings
                )
            );
    }

    public class PrologToPPiTRSProof extends Proof.DefaultProof {
        PrologProblem pp;
        PPiTRSProblem ppitrs;
        Set<GeneralizedRule> R;
        Map<FunctionSymbol, Set<List<Boolean>>> modings;

        public PrologToPPiTRSProof(
            final PrologProblem pp,
            final PPiTRSProblem ppitrs,
            final Set<GeneralizedRule> R,
            final Map<FunctionSymbol, Set<List<Boolean>>> modings)
        {
            this.pp = pp;
            this.ppitrs = ppitrs;
            this.R = R;
            this.modings = modings;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            this.startUp();
            this.result.append("We use the technique of " + "[TODO]."); //TODO o.cite(Citation.TOCL09)
            if (this.modings != null) {
                this.result.append(" With regard to the inferred argument filtering the"
                    + " predicates were used in the following modes:\n"
                    + o.linebreak());
                for (final Map.Entry<FunctionSymbol, Set<List<Boolean>>> entry : this.modings.entrySet()) {
                    FunctionSymbol f = entry.getKey();
                    if (f.getArity() == 0) {
                        continue;
                    }
                    final String newName = f.getName();
                    f = FunctionSymbol.create(newName, f.getArity());
                    final Set<List<Boolean>> modes = entry.getValue();
                    this.result.append(o.export(f) + ":");
                    for (final List<Boolean> mode : modes) {
                        this.result.append(" (");
                        boolean first = true;
                        for (final Boolean arg : mode) {
                            if (first) {
                                first = false;
                            } else {
                                this.result.append(",");
                            }
                            this.result.append(arg ? "b" : "f");
                        }
                        this.result.append(")");
                    }
                    this.result.append("\n" + o.linebreak());
                }
            }

            this.result.append("Transforming "
                + ProofUtility.R(o, this.pp.getName(NameLength.SHORT))
                + " into the following "
                + ProofUtility.TRS(o)
                + ":\n"
                + o.linebreak());

            this.result.append(o.export(this.ppitrs));
            this.result.append("\n" + o.paragraph());

            this.result.append(o.bold("Infinitary Constructor Rewriting Termination")
                + " of "
                + this.ppitrs.getName(aprove.verification.dpframework.NameLength.SHORT)
                + " implies "
                + o.bold("Termination")
                + " of "
                + this.pp.getName(NameLength.SHORT)
                + o.paragraph()
                + "\n");

            return this.result.toString();
        }
    }

    /*- MODE ANANLYSIS -------------------------------------------------------*/

    public static class AfsModeAnalyser {

        private Graph<ModedRule, Object> ruleGraph;
        private Set<ModedRule> have;
        private Map<FunctionSymbol, Set<GeneralizedRule>> sym2Rules;
        private Map<Pair<FunctionSymbol, List<Boolean>>, List<Boolean>> oldAfs;
        private Map<Pair<FunctionSymbol, List<Boolean>>, List<Boolean>> afs;
        private final AfsSelectionHeuristic heuristic;
        private final boolean force;

        public AfsModeAnalyser(
            final Set<GeneralizedRule> rules,
            final Afs initialAfs,
            final AfsSelectionHeuristic heuristic,
            final boolean force)
        {
            this.force = force;
            this.heuristic = heuristic;
            this.buildSym2Rules(rules);
            this.buildRuleGraph(initialAfs);
        }

        private void buildSym2Rules(final Set<GeneralizedRule> rules) {
            this.sym2Rules = new LinkedHashMap<FunctionSymbol, Set<GeneralizedRule>>();
            for (final GeneralizedRule rule : rules) {
                final FunctionSymbol f = rule.getRootSymbol();
                Set<GeneralizedRule> fRules = this.sym2Rules.get(f);
                if (fRules == null) {
                    fRules = new LinkedHashSet<GeneralizedRule>();
                    this.sym2Rules.put(f, fRules);
                }
                if (!fRules.add(rule)) {
                    throw new RuntimeException("duplicate rule");
                }
            }
        }

        private void buildRuleGraph(final Afs initialAfs) {
            this.oldAfs = null;
            this.afs = new LinkedHashMap<Pair<FunctionSymbol, List<Boolean>>, List<Boolean>>();
            for (final FunctionSymbol f : initialAfs.getFunctionSymbols()) {
                final List<Boolean> regArgs = initialAfs.getRegardedArgsAsList(f);
                List<Boolean> rootArgs = null;
                if (this.sym2Rules.get(f) != null) {
                    rootArgs = regArgs;
                }
                this.afs.put(new Pair<FunctionSymbol, List<Boolean>>(f, rootArgs), regArgs);
            }
            final boolean force = this.force;
            while (true) {
                try {
                    this.ruleGraph = new Graph<ModedRule, Object>();
                    this.have = new LinkedHashSet<ModedRule>();
                    // iterate over symbols that have a filtering
                    for (final FunctionSymbol f : initialAfs.getFunctionSymbols()) {
                        // iterate over rules for this function symbol
                        final Set<GeneralizedRule> rules = this.sym2Rules.get(f);
                        if (rules != null) {
                            for (final GeneralizedRule rule : rules) {
                                final List<Boolean> regArgs = initialAfs.getRegardedArgsAsList(f);
                                final ModedRule mRule = new ModedRule(rule, regArgs);
                                this.buildRuleGraph(mRule, null, regArgs, null);
                            }
                        }
                    }
                } catch (final AfsException e) {
                    continue;
                }
                if (!force) {
                    break;
                }
                if (this.oldAfs != null) {
                    if (this.oldAfs.keySet().containsAll(this.afs.keySet())) {
                        break;
                    }
                    //                    force = false;
                    //                    this.afs = this.oldAfs;
                }
                boolean changed = false;
                for (final Map.Entry<Pair<FunctionSymbol, List<Boolean>>, List<Boolean>> entry : this.afs.entrySet()) {
                    final FunctionSymbol oldSym = entry.getKey().x;
                    final List<Boolean> filtering = entry.getValue();
                    final String oldName = oldSym.getName();
                    if (oldName.endsWith(PrologFNG.OUT)) {
                        final FunctionSymbol inSymbol =
                            FunctionSymbol.create(
                                oldName.substring(0, oldName.length() - 4) + PrologFNG.IN,
                                oldSym.getArity());
                        final List<Boolean> inFiltering =
                            this.afs.get(new Pair<FunctionSymbol, List<Boolean>>(inSymbol, entry.getKey().y));
                        for (int i = 0; i < filtering.size(); i++) {
                            if (filtering.get(i)) {
                                if (inFiltering.get(i)) {
                                    filtering.set(i, false);
                                    changed = true;
                                }
                            }
                        }
                    }
                }
                if (changed) {
                    this.oldAfs = new LinkedHashMap<Pair<FunctionSymbol, List<Boolean>>, List<Boolean>>(this.afs);
                    continue;
                }
                break;
            }
        }

        private void buildRuleGraph(
            final ModedRule mRule,
            final Node<ModedRule> prev,
            final List<Boolean> root,
            final List<Boolean> out) throws AfsException
        {
            if (this.have.contains(mRule)) {
                if (prev != null) {
                    final Node<ModedRule> mNode = this.ruleGraph.getNodeFromObject(mRule);
                    this.ruleGraph.addEdge(prev, mNode);
                }
                return; // been there, done that
            }
            this.have.add(mRule);

            mRule.setOutArgs(out);
            // create new node in graph
            final Node<ModedRule> mNode = new Node<ModedRule>(mRule);
            this.ruleGraph.addNode(mNode);
            if (prev != null) {
                this.ruleGraph.addEdge(prev, mNode);
            }

            final Set<TRSVariable> leftVars = new LinkedHashSet<TRSVariable>();
            final TRSFunctionApplication leftApp = mRule.getLeft();
            final FunctionSymbol leftSym = leftApp.getRootSymbol();
            final List<Boolean> leftArgs = this.afs.get(new Pair<FunctionSymbol, List<Boolean>>(leftSym, root));
            final ModedRule.RuleType type = mRule.getType();
            for (int i = 0; i < leftSym.getArity(); i++) {
                if (leftArgs.get(i)) {
                    if (i + 1 == leftSym.getArity()) {
                        switch (type) {
                        case MIDDLE:
                        case LAST:
                            final TRSFunctionApplication outApp = (TRSFunctionApplication) leftApp.getArgument(i);
                            final FunctionSymbol outSym = outApp.getRootSymbol();
                            final Pair<FunctionSymbol, List<Boolean>> key =
                                new Pair<FunctionSymbol, List<Boolean>>(outSym, out);
                            List<Boolean> outArgs = this.afs.get(key);
                            if (outArgs == null) {
                                outArgs = new ArrayList<Boolean>();
                                for (int j = 0; j < outSym.getArity(); j++) {
                                    outArgs.add(true);
                                }
                                this.afs.put(key, outArgs);
                            }
                            for (int j = 0; j < outSym.getArity(); j++) {
                                if (outArgs.get(j)) {
                                    this.getVariables(outApp.getArgument(j), leftVars);
                                }
                            }
                            break;
                        case FACT:
                        case FIRST:
                            this.getVariables(leftApp.getArgument(i), leftVars);
                            break;
                        }
                    } else {
                        this.getVariables(leftApp.getArgument(i), leftVars);
                    }
                }
            }

            final Set<Position> rightPos = new LinkedHashSet<Position>();
            final TRSFunctionApplication rightApp = mRule.getRight();
            this.getPositions(rightApp, rightPos, leftVars, Position.create(), root);

            final FunctionSymbol rightSym = rightApp.getRootSymbol();
            FunctionSymbol inSym = null;
            FunctionSymbol correspondingInSym = null;
            switch (type) {
            case FIRST:
            case MIDDLE:
                final TRSTerm argument = rightApp.getArgument(rightSym.getArity() - 1);
                inSym = ((TRSFunctionApplication) argument).getRootSymbol();
                //inSym = (rightApp.getArgument(rightSym.getArity()-1)) instanceof FunctionApplication ? ((FunctionApplication)rightApp.getArgument(rightSym.getArity()-1)).getRootSymbol() : null;
                break;
            case LAST:
            case FACT:
                correspondingInSym =
                    FunctionSymbol.create(rightSym.getName().substring(0, rightSym.getName().length() - 3)
                        + PrologFNG.IN, rightSym.getArity());
                break;
            }
            final Afs newAfs =
                this.heuristic.getAfs(
                    rightApp,
                    rightPos,
                    rightSym,
                    inSym,
                    type,
                    this.afs.get(new Pair<FunctionSymbol, List<Boolean>>(correspondingInSym, root)));
            final Set<FunctionSymbol> fsyms = new LinkedHashSet<FunctionSymbol>(newAfs.getFunctionSymbols());
            List<Boolean> rootArgs = newAfs.getRegardedArgsAsList(rightSym);
            boolean restart = false;
            {
                final Pair<FunctionSymbol, List<Boolean>> key = new Pair<FunctionSymbol, List<Boolean>>(rightSym, root);
                final List<Boolean> oldRootArgs = this.afs.get(key);
                if (oldRootArgs != null) {
                    final List<Boolean> newerArgs = new ArrayList<Boolean>();
                    for (int i = 0; i < rightSym.getArity(); i++) {
                        if (oldRootArgs.get(i)) {
                            if (rootArgs.get(i)) {
                                newerArgs.add(true);
                            } else {
                                newerArgs.add(false);
                                restart = true;
                            }
                        } else {
                            newerArgs.add(false);
                        }
                    }
                    rootArgs = newerArgs;
                }
            }
            this.afs.put(new Pair<FunctionSymbol, List<Boolean>>(rightSym, root), rootArgs);
            if (restart) {
                throw new AfsException(rightSym);
            }
            fsyms.remove(rightSym);
            List<Boolean> inArgs = null;
            if (inSym != null) {
                inArgs = newAfs.getRegardedArgsAsList(inSym);
                this.afs.put(new Pair<FunctionSymbol, List<Boolean>>(inSym, inArgs), inArgs);
                fsyms.remove(inSym);
                mRule.setInArgs(inArgs);
            }
            for (final FunctionSymbol f : fsyms) {
                restart = false;
                final Pair<FunctionSymbol, List<Boolean>> key = new Pair<FunctionSymbol, List<Boolean>>(f, null);
                final List<Boolean> oldArgs = this.afs.get(key);
                List<Boolean> newArgs = newAfs.getRegardedArgsAsList(f);
                if (oldArgs != null) {
                    final List<Boolean> newerArgs = new ArrayList<Boolean>();
                    for (int i = 0; i < f.getArity(); i++) {
                        if (oldArgs.get(i)) {
                            if (newArgs.get(i)) {
                                newerArgs.add(true);
                            } else {
                                newerArgs.add(false);
                                restart = true;
                            }
                        } else {
                            newerArgs.add(false);
                        }
                    }
                    newArgs = newerArgs;
                }
                this.afs.put(key, newArgs);
                if (restart) {
                    throw new AfsException(f);
                }
            }

            switch (type) {
            case FIRST:
            case MIDDLE:
                // recurse on in level
                for (final GeneralizedRule rule : this.sym2Rules.get(inSym)) {
                    final ModedRule newMRule = new ModedRule(rule, inArgs);
                    this.buildRuleGraph(newMRule, mNode, inArgs, null);
                }
                // recurse on root level
                for (final GeneralizedRule rule : this.sym2Rules.get(rightSym)) {
                    final ModedRule newMRule = new ModedRule(rule, root);
                    this.buildRuleGraph(newMRule, mNode, root, inArgs);
                }
                break;
            case LAST:
            case FACT:
                break;
            }
        }

        private void getPositions(
            final TRSTerm argument,
            final Set<Position> poss,
            final Set<TRSVariable> leftVars,
            final Position pos,
            final List<Boolean> goal)
        {
            if (argument.isVariable()) {
                if (!leftVars.contains(argument)) {
                    poss.add(pos);
                }
            } else {
                final TRSFunctionApplication fapp = (TRSFunctionApplication) argument;
                final FunctionSymbol f = fapp.getRootSymbol();
                final Pair<FunctionSymbol, List<Boolean>> key = new Pair<FunctionSymbol, List<Boolean>>(f, goal);
                List<Boolean> regArgs = this.afs.get(key);
                if (regArgs == null) {
                    regArgs = new ArrayList<Boolean>();
                    for (int i = 0; i < f.getArity(); i++) {
                        regArgs.add(true);
                    }
                }
                for (int i = 0; i < f.getArity(); i++) {
                    if (regArgs.get(i)) {
                        this.getPositions(fapp.getArgument(i), poss, leftVars, pos.append(i), null);
                    }
                }
            }
        }

        private void getVariables(final TRSTerm argument, final Set<TRSVariable> vars) {
            if (argument.isVariable()) {
                vars.add((TRSVariable) argument);
            } else {
                final TRSFunctionApplication fapp = (TRSFunctionApplication) argument;
                final FunctionSymbol f = fapp.getRootSymbol();
                final Pair<FunctionSymbol, List<Boolean>> key = new Pair<FunctionSymbol, List<Boolean>>(f, null);
                if (!this.afs.containsKey(key)) {
                    final List<Boolean> args = new ArrayList<Boolean>();
                    for (int i = 0; i < f.getArity(); i++) {
                        args.add(true);
                    }
                    this.afs.put(key, args);
                }
                final List<Boolean> regArgs = this.afs.get(key);
                for (int i = 0; i < f.getArity(); i++) {
                    if (regArgs.get(i)) {
                        this.getVariables(fapp.getArgument(i), vars);
                    }
                }
            }
        }

        public Triple<Set<GeneralizedRule>, Afs, Map<FunctionSymbol, Set<List<Boolean>>>> getSplitRules() {
            //            if (false) {try {
            //                java.io.PrintWriter pw = new java.io.PrintWriter(new java.io.FileWriter("/tmp/killme"));
            //                pw.println(this.ruleGraph.toDOT());
            //                for (Map.Entry<Pair<FunctionSymbol, List<Boolean>>, List<Boolean>> entry : this.afs.entrySet()) {
            //                    pw.println();
            //                    pw.println(entry.getKey());
            //                    pw.println(entry.getValue());
            //                }
            //                pw.close();
            //            } catch (java.io.IOException e) {
            //                // TODO Auto-generated catch block
            //                e.printStackTrace();
            //            }}
            // keep track what U symbols we have already put all trues to nulls
            final Set<Pair<FunctionSymbol, List<Boolean>>> nulled =
                new LinkedHashSet<Pair<FunctionSymbol, List<Boolean>>>();
            for (final Node<ModedRule> mNode : this.ruleGraph.getNodes()) {
                final ModedRule mRule = mNode.getObject();
                switch (mRule.getType()) {
                case LAST:
                    this.eliminateRedundantVars(mNode, new LinkedHashSet<TRSVariable>(), nulled);
                    break;
                case FACT:
                case FIRST:
                case MIDDLE:
                    break;
                }
            }
            // those arguments where we could decide and were not forced to set true, set them to false!
            for (final Pair<FunctionSymbol, List<Boolean>> key : nulled) {
                final List<Boolean> args = this.afs.get(key);
                for (int i = 0; i + 1 < key.x.getArity(); i++) {
                    if (args.get(i) == null) {
                        args.set(i, false);
                    }
                }
            }
            final Afs newAfs = new Afs();
            for (final Map.Entry<Pair<FunctionSymbol, List<Boolean>>, List<Boolean>> entry : this.afs.entrySet()) {
                final FunctionSymbol f = AfsModeAnalyser.fromPair(entry.getKey());
                final YNM[] filtering = this.fromBoolList(entry.getValue());
                newAfs.setFiltering(f, filtering);
            }
            final Map<FunctionSymbol, Set<List<Boolean>>> modings =
                new LinkedHashMap<FunctionSymbol, Set<List<Boolean>>>();
            final Set<GeneralizedRule> newRules = new LinkedHashSet<GeneralizedRule>();
            for (final Node<ModedRule> mNode : this.ruleGraph.getNodes()) {
                final ModedRule mRule = mNode.getObject();
                final ModedRule.RuleType type = mRule.getType();
                final List<? extends TRSTerm> oldLeft = mRule.getLeft().getArguments();
                final FunctionSymbol oldLeftSym = mRule.getLeft().getRootSymbol();
                if (type == ModedRule.RuleType.FIRST) {
                    Set<List<Boolean>> modes = modings.get(oldLeftSym);
                    if (modes == null) {
                        modes = new LinkedHashSet<List<Boolean>>();
                        modings.put(oldLeftSym, modes);
                    }
                    modes.add(mRule.getModing());
                }
                final FunctionSymbol newLeftSym = AfsModeAnalyser.fromPair(oldLeftSym, mRule.getModing());
                final ArrayList<TRSTerm> newLeft = new ArrayList<TRSTerm>();
                for (int i = 0; i < oldLeftSym.getArity(); i++) {
                    if (i + 1 == oldLeftSym.getArity()) {
                        switch (type) {
                        case MIDDLE:
                        case LAST:
                            final TRSFunctionApplication oldOutApp = (TRSFunctionApplication) oldLeft.get(i);
                            final ImmutableList<? extends TRSTerm> oldOut = oldOutApp.getArguments();
                            final FunctionSymbol newOutSym =
                                AfsModeAnalyser.fromPair(oldOutApp.getRootSymbol(), mRule.getOutArgs());
                            newLeft.add(TRSTerm.createFunctionApplication(newOutSym, oldOut));
                            break;
                        case FIRST:
                        case FACT:
                            newLeft.add(oldLeft.get(i));
                            break;
                        }
                    } else {
                        newLeft.add(oldLeft.get(i));
                    }
                }
                final TRSFunctionApplication newLeftApp =
                    TRSTerm.createFunctionApplication(newLeftSym, ImmutableCreator.create(newLeft));
                final List<? extends TRSTerm> oldRight = mRule.getRight().getArguments();
                final FunctionSymbol oldRightSym = mRule.getRight().getRootSymbol();
                final FunctionSymbol newRightSym = AfsModeAnalyser.fromPair(oldRightSym, mRule.getModing());
                final ArrayList<TRSTerm> newRight = new ArrayList<TRSTerm>();
                for (int i = 0; i < oldRightSym.getArity(); i++) {
                    if (i + 1 == oldRightSym.getArity()) {
                        switch (type) {
                        case FIRST:
                        case MIDDLE:
                            final TRSFunctionApplication oldInApp = (TRSFunctionApplication) oldRight.get(i);
                            final ImmutableList<? extends TRSTerm> oldIn = oldInApp.getArguments();
                            final FunctionSymbol newInSym =
                                AfsModeAnalyser.fromPair(oldInApp.getRootSymbol(), mRule.getInArgs());
                            newRight.add(TRSTerm.createFunctionApplication(newInSym, oldIn));
                            break;
                        case LAST:
                        case FACT:
                            newRight.add(oldRight.get(i));
                            break;
                        }
                    } else {
                        newRight.add(oldRight.get(i));
                    }
                }
                final TRSFunctionApplication newRightApp =
                    TRSTerm.createFunctionApplication(newRightSym, ImmutableCreator.create(newRight));
                newRules.add(GeneralizedRule.create(newLeftApp, newRightApp));

            }
            return new Triple<Set<GeneralizedRule>, Afs, Map<FunctionSymbol, Set<List<Boolean>>>>(
                newRules,
                newAfs,
                modings);
        }

        private void eliminateRedundantVars(
            final Node<ModedRule> mNode,
            final Set<TRSVariable> vars,
            final Set<Pair<FunctionSymbol, List<Boolean>>> nulled)
        {
            final ModedRule mRule = mNode.getObject();
            final ModedRule.RuleType type = mRule.getType();
            switch (type) {
            case FIRST:
            case FACT:
                return;
            }
            final TRSFunctionApplication rightApp = mRule.getRight();
            final FunctionSymbol rightSym = rightApp.getRootSymbol();
            switch (type) {
            case LAST:
                final List<Boolean> outArgs =
                    this.afs.get(new Pair<FunctionSymbol, List<Boolean>>(rightSym, mRule.getModing()));
                for (int i = 0; i < rightSym.getArity(); i++) {
                    if (outArgs.get(i)) {
                        this.getVariables(rightApp.getArgument(i), vars);
                    }
                }
                break;
            case MIDDLE:
                ModedRule inRule = null;
                for (final Node<ModedRule> child : this.ruleGraph.getOut(mNode)) {
                    final ModedRule childRule = child.getObject();
                    switch (childRule.getType()) {
                    case FIRST:
                    case FACT:
                        inRule = childRule;
                        break;
                    case MIDDLE:
                    case LAST:
                        break;
                    }
                }
                final TRSFunctionApplication inApp = (TRSFunctionApplication) rightApp.getArgument(rightSym.getArity() - 1);
                final FunctionSymbol inSym = inApp.getRootSymbol();
                final List<Boolean> inArgs =
                    this.afs.get(new Pair<FunctionSymbol, List<Boolean>>(inSym, inRule.getModing()));
                for (int i = 0; i < inSym.getArity(); i++) {
                    if (inArgs.get(i)) {
                        this.getVariables(inApp.getArgument(i), vars);
                    }
                }
                break;
            }
            final TRSFunctionApplication leftApp = mRule.getLeft();
            final FunctionSymbol leftSym = leftApp.getRootSymbol();
            switch (type) {
            case LAST:
            case MIDDLE:
                final Pair<FunctionSymbol, List<Boolean>> key =
                    new Pair<FunctionSymbol, List<Boolean>>(leftSym, mRule.getModing());
                final List<Boolean> leftArgs = this.afs.get(key);
                if (!nulled.contains(key)) {
                    nulled.add(key);
                    for (int i = 0; i + 1 < leftSym.getArity(); i++) {
                        if (leftArgs.get(i)) {
                            leftArgs.set(i, null);
                        }
                    }
                }
                for (int i = 0; i + 1 < leftSym.getArity(); i++) {
                    if (leftArgs.get(i) == null) {
                        final TRSTerm arg = leftApp.getArgument(i);
                        if (vars.contains(arg)) {
                            leftArgs.set(i, true);
                        }
                    }
                }
                break;
            }
            switch (type) {
            case LAST:
            case MIDDLE:
                final Node<ModedRule> nextNode = this.ruleGraph.getIn(mNode).iterator().next();
                this.eliminateRedundantVars(nextNode, vars, nulled);
                break;
            }
        }

        private YNM[] fromBoolList(final List<Boolean> value) {
            final YNM[] filtering = new YNM[value.size()];
            for (int i = 0; i < filtering.length; i++) {
                filtering[i] = YNM.fromBool(value.get(i));
            }
            return filtering;
        }

        public static FunctionSymbol fromPair(final Pair<FunctionSymbol, List<Boolean>> key) {
            return AfsModeAnalyser.fromPair(key.x, key.y);
        }

        public static FunctionSymbol fromPair(final FunctionSymbol f, final List<Boolean> moding) {
            if (moding == null) {
                return f;
            }
            final StringBuffer modingId = new StringBuffer();
            for (final boolean mode : moding) {
                modingId.append(mode ? "g" : "a");
            }
            return FunctionSymbol.create(f.getName() + "_" + modingId.toString(), f.getArity());
        }

        public static class ModedRule {
            public enum RuleType {
                FACT, FIRST, MIDDLE, LAST
            };

            private final GeneralizedRule rule;
            private final List<Boolean> moding;
            private List<Boolean> inArgs;
            private List<Boolean> outArgs;

            public ModedRule(final GeneralizedRule rule, final List<Boolean> regArgs) {
                this.rule = rule;
                this.moding = regArgs;
            }

            public List<Boolean> getModing() {
                return this.moding;
            }

            public void setInArgs(final List<Boolean> inArgs) {
                this.inArgs = inArgs;
            }

            public List<Boolean> getInArgs() {
                return this.inArgs;
            }

            public void setOutArgs(final List<Boolean> outArgs) {
                this.outArgs = outArgs;
            }

            public List<Boolean> getOutArgs() {
                return this.outArgs;
            }

            public TRSFunctionApplication getRight() {
                return (TRSFunctionApplication) this.rule.getRight();
            }

            public TRSFunctionApplication getLeft() {
                return this.rule.getLeft();
            }

            public RuleType getType() {
                final FunctionSymbol leftSym = this.rule.getLeft().getRootSymbol();
                final FunctionSymbol rightSym = ((TRSFunctionApplication) this.rule.getRight()).getRootSymbol();
                if (leftSym.getName().endsWith(PrologFNG.IN)) {
                    if (rightSym.getName().endsWith(PrologFNG.OUT)) {
                        return RuleType.FACT;
                    }
                    return RuleType.FIRST;
                }
                if (rightSym.getName().endsWith(PrologFNG.OUT)) {
                    return RuleType.LAST;
                }
                return RuleType.MIDDLE;
            }

            @Override
            public int hashCode() {
                return this.rule.hashCode() + 101 * this.moding.hashCode();
            }

            @Override
            public boolean equals(final Object o) {
                final ModedRule other = (ModedRule) o;
                return this.rule.equals(other.rule) && this.moding.equals(other.moding);
            }

            @Override
            public String toString() {
                return this.rule.toString() + ": " + this.moding.toString();
            }
        }

        public class AfsException extends Exception {
            private static final long serialVersionUID = 1L;

            public AfsException(final FunctionSymbol f) {
                super(f.getName());
            }
        }

    }

    public interface AfsSelectionHeuristic {
        public Afs getAfs(
            TRSTerm t,
            Set<Position> poss,
            FunctionSymbol rootSym,
            FunctionSymbol inSym,
            RuleType type,
            List<Boolean> name);
    }

    public static class InnermostHeuristic implements AfsSelectionHeuristic {
        @Override
        public Afs getAfs(
            final TRSTerm t,
            final Set<Position> poss,
            final FunctionSymbol rootSym,
            final FunctionSymbol inSym,
            final RuleType type,
            final List<Boolean> inArgs)
        {
            final Afs afs = new Afs();
            for (final Position pos : poss) {
                final Position parent = pos.shorten(1);
                final FunctionSymbol f = ((TRSFunctionApplication) t.getSubterm(parent)).getRootSymbol();
                afs.setFiltering(f, pos.lastIndex(), YNM.NO);
            }
            return afs;
        }
    }

    public static class OutermostHeuristic implements AfsSelectionHeuristic {
        @Override
        public Afs getAfs(
            final TRSTerm t,
            final Set<Position> poss,
            final FunctionSymbol rootSym,
            final FunctionSymbol inSym,
            final RuleType type,
            final List<Boolean> inArgs)
        {
            final Afs afs = new Afs();
            switch (type) {
            case FACT:
            case LAST:
                for (final Position pos : poss) {
                    afs.setFiltering(rootSym, pos.firstIndex(), YNM.NO);
                }
                break;
            case FIRST:
            case MIDDLE:
                for (final Position pos : poss) {
                    if (pos.firstIndex() + 1 == rootSym.getArity()) {
                        afs.setFiltering(inSym, pos.toIntArray()[1], YNM.NO);
                    } else {
                        afs.setFiltering(rootSym, pos.firstIndex(), YNM.NO);
                    }
                }
                break;
            }
            return afs;
        }
    }

    public static class InputOutputHeuristic implements AfsSelectionHeuristic {
        @Override
        public Afs getAfs(
            final TRSTerm t,
            final Set<Position> poss,
            final FunctionSymbol rootSym,
            final FunctionSymbol inSym,
            final RuleType type,
            final List<Boolean> inArgs)
        {
            final Afs afs = new Afs();
            switch (type) {
            case FACT:
            case LAST:
                for (final Position pos : poss) {
                    final int arg = pos.firstIndex();
                    if (inArgs.get(arg)) {
                        afs.setFiltering(rootSym, arg, YNM.NO);
                    } else {
                        final Position parent = pos.shorten(1);
                        final FunctionSymbol f = ((TRSFunctionApplication) t.getSubterm(parent)).getRootSymbol();
                        afs.setFiltering(f, pos.lastIndex(), YNM.NO);
                    }
                }
                break;
            case FIRST:
            case MIDDLE:
                for (final Position pos : poss) {
                    if (pos.firstIndex() + 1 == rootSym.getArity()) {
                        afs.setFiltering(inSym, pos.toIntArray()[1], YNM.NO);
                    } else {
                        afs.setFiltering(rootSym, pos.firstIndex(), YNM.NO);
                    }
                }
                break;
            }
            return afs;
        }
    }

    public static class ModedAfs extends LinkedHashMap<Pair<FunctionSymbol, List<Boolean>>, List<Boolean>> {
        private static final long serialVersionUID = 5587799741196116226L;

        public ModedAfs() {
        }

        public ModedAfs(final Map<Pair<FunctionSymbol, List<Boolean>>, List<Boolean>> map) {
            super(map);
        }

        @Override
        public List<Boolean> put(final Pair<FunctionSymbol, List<Boolean>> key, final List<Boolean> value) {
            if (key.x.getName().endsWith(PrologFNG.OUT)) {
                try {
                    final java.io.PrintWriter pw =
                        new java.io.PrintWriter(new java.io.FileWriter("/tmp/killme2", true));
                    pw.println();
                    pw.println(key);
                    pw.println(value);
                    pw.close();
                } catch (final java.io.IOException e) {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }
            }
            return super.put(key, value);
        }
    }

    public static class InputOutput2Heuristic implements AfsSelectionHeuristic {
        private final TypeGraph graph;

        public InputOutput2Heuristic(final TypeGraph graph) {
            this.graph = graph;
        }

        @Override
        public Afs getAfs(
            final TRSTerm t,
            final Set<Position> poss,
            final FunctionSymbol rootSym,
            final FunctionSymbol inSym,
            final RuleType type,
            final List<Boolean> inArgs)
        {
            final Afs afs = new Afs();
            switch (type) {
            case FACT:
            case LAST:
                for (Position pos : poss) {
                    final int arg = pos.firstIndex();
                    if (inArgs.get(arg)) {
                        afs.setFiltering(rootSym, arg, YNM.NO);
                    } else {
                        Position parent = pos.shorten(1);
                        FunctionSymbol f = ((TRSFunctionApplication) t.getSubterm(parent)).getRootSymbol();
                        while (parent.getDepth() > 0 && this.graph.isRecursive(f, pos.lastIndex())) {
                            pos = parent;
                            parent = parent.shorten(1);
                            f = ((TRSFunctionApplication) t.getSubterm(parent)).getRootSymbol();
                        }
                        afs.setFiltering(f, pos.lastIndex(), YNM.NO);
                    }
                }
                break;
            case FIRST:
            case MIDDLE:
                for (final Position pos : poss) {
                    if (pos.firstIndex() + 1 == rootSym.getArity()) {
                        afs.setFiltering(inSym, pos.toIntArray()[1], YNM.NO);
                    } else {
                        afs.setFiltering(rootSym, pos.firstIndex(), YNM.NO);
                    }
                }
                break;
            }
            return afs;
        }
    }

    public static class Outermost2Heuristic implements AfsSelectionHeuristic {
        private final TypeGraph graph;

        public Outermost2Heuristic(final TypeGraph graph) {
            this.graph = graph;
        }

        @Override
        public Afs getAfs(
            final TRSTerm t,
            final Set<Position> poss,
            final FunctionSymbol rootSym,
            final FunctionSymbol inSym,
            final RuleType type,
            final List<Boolean> inArgs)
        {
            final Afs afs = new Afs();
            switch (type) {
            case FACT:
            case LAST:
                for (Position pos : poss) {
                    Position parent = pos.shorten(1);
                    FunctionSymbol f = ((TRSFunctionApplication) t.getSubterm(parent)).getRootSymbol();
                    while (parent.getDepth() > 0 && this.graph.isRecursive(f, pos.lastIndex())) {
                        pos = parent;
                        parent = parent.shorten(1);
                        f = ((TRSFunctionApplication) t.getSubterm(parent)).getRootSymbol();
                    }
                    afs.setFiltering(f, pos.lastIndex(), YNM.NO);
                }
                break;
            case FIRST:
            case MIDDLE:
                for (final Position pos : poss) {
                    if (pos.firstIndex() + 1 == rootSym.getArity()) {
                        afs.setFiltering(inSym, pos.toIntArray()[1], YNM.NO);
                    } else {
                        afs.setFiltering(rootSym, pos.firstIndex(), YNM.NO);
                    }
                }
                break;
            }
            return afs;
        }
    }

    public static class Innermost2Heuristic implements AfsSelectionHeuristic {
        private final TypeGraph graph;

        public Innermost2Heuristic(final TypeGraph graph) {
            this.graph = graph;
        }

        @Override
        public Afs getAfs(
            final TRSTerm t,
            final Set<Position> poss,
            final FunctionSymbol rootSym,
            final FunctionSymbol inSym,
            final RuleType type,
            final List<Boolean> inArgs)
        {
            final Afs afs = new Afs();
            switch (type) {
            case FACT:
            case LAST:
                for (Position pos : poss) {
                    Position parent = pos.shorten(1);
                    FunctionSymbol f = ((TRSFunctionApplication) t.getSubterm(parent)).getRootSymbol();
                    while (parent.getDepth() > 0 && this.graph.isRecursive(f, pos.lastIndex())) {
                        pos = parent;
                        parent = parent.shorten(1);
                        f = ((TRSFunctionApplication) t.getSubterm(parent)).getRootSymbol();
                    }
                    afs.setFiltering(f, pos.lastIndex(), YNM.NO);
                }
                break;
            case FIRST:
            case MIDDLE:
                for (Position pos : poss) {
                    if (pos.firstIndex() + 1 == rootSym.getArity()) {
                        Position parent = pos.shorten(1);
                        FunctionSymbol f = ((TRSFunctionApplication) t.getSubterm(parent)).getRootSymbol();
                        while (parent.getDepth() > 1 && this.graph.isRecursive(f, pos.lastIndex())) {
                            pos = parent;
                            parent = parent.shorten(1);
                            f = ((TRSFunctionApplication) t.getSubterm(parent)).getRootSymbol();
                        }
                        afs.setFiltering(f, pos.lastIndex(), YNM.NO);
                    } else {
                        afs.setFiltering(rootSym, pos.firstIndex(), YNM.NO);
                    }
                }
                break;
            }
            return afs;
        }
    }

    public static class TypeGraph {
        private final Graph<TypeEntity, Object> graph;
        private Set<FuncPosEntity> recursive;

        public TypeGraph(final Set<GeneralizedRule> R) {
            this.graph = new Graph<TypeEntity, Object>();
            this.buildGraph(R);
        }

        private void buildGraph(final Set<GeneralizedRule> R) {
            for (final GeneralizedRule rule : R) {
                this.buildGraph(rule.getLeft(), rule);
                this.buildGraph(rule.getRight(), rule);
            }
        }

        private void buildGraph(final TRSTerm term, final GeneralizedRule rule) {
            if (!term.isVariable()) {
                final TRSFunctionApplication fApp = (TRSFunctionApplication) term;
                final FunctionSymbol fSym = fApp.getRootSymbol();
                final ImmutableList<? extends TRSTerm> args = fApp.getArguments();
                for (int i = 0; i < fSym.getArity(); i++) {
                    final TRSTerm arg = args.get(i);
                    final TypeEntity e1 = new FuncPosEntity(fSym, i);
                    final TypeEntity e2 = this.getEntity(arg, rule);
                    Node<TypeEntity> n1 = this.graph.getNodeFromObject(e1);
                    Node<TypeEntity> n2 = this.graph.getNodeFromObject(e2);
                    if (n1 == null) {
                        n1 = new Node<TypeEntity>(e1);
                    }
                    if (n2 == null) {
                        n2 = new Node<TypeEntity>(e2);
                    }
                    this.graph.addEdge(n1, n2);
                    this.graph.addEdge(n2, n1);
                    this.buildGraph(arg, rule);
                }
            }
        }

        private TypeEntity getEntity(final TRSTerm term, final GeneralizedRule rule) {
            if (term.isVariable()) {
                return new VarRuleEntity((TRSVariable) term, rule);
            }
            return new FuncEntity(((TRSFunctionApplication) term).getRootSymbol());
        }

        public Set<FuncPosEntity> getRecursiveFuncPos() {
            if (this.recursive != null) {
                return this.recursive;
            }
            final Set<FuncPosEntity> recursive = new LinkedHashSet<FuncPosEntity>();
            final Set<FunctionSymbol> recursiveFuncs = new LinkedHashSet<FunctionSymbol>();
            final Map<TypeEntity, Set<TypeEntity>> classes = this.getEquivalenceClasses();
            boolean changed = true;
            while (changed) {
                changed = false;
                for (final Map.Entry<TypeEntity, Set<TypeEntity>> entry : classes.entrySet()) {
                    final TypeEntity key = entry.getKey();
                    if (key instanceof FuncPosEntity) {
                        final FuncPosEntity fpKey = (FuncPosEntity) key;
                        if (!recursive.contains(fpKey)) {
                            for (final TypeEntity entity : entry.getValue()) {
                                if (entity instanceof FuncEntity) {
                                    final FuncEntity fValue = (FuncEntity) entity;
                                    if (fpKey.f.equals(fValue.f) || recursiveFuncs.contains(fValue.f)) {
                                        recursive.add(fpKey);
                                        recursiveFuncs.add(fpKey.f);
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            this.recursive = recursive;
            return recursive;
        }

        public Map<TypeEntity, Set<TypeEntity>> getEquivalenceClasses() {
            final Map<TypeEntity, Set<TypeEntity>> result = new LinkedHashMap<TypeEntity, Set<TypeEntity>>();
            for (final Cycle<TypeEntity> cycle : this.graph.getSCCs(false)) {
                final Set<TypeEntity> eClass = new LinkedHashSet<TypeEntity>();
                for (final Node<TypeEntity> node : cycle) {
                    final TypeEntity entity = node.getObject();
                    if (entity instanceof FuncEntity || entity instanceof FuncPosEntity) {
                        eClass.add(entity);
                    }
                }
                for (final TypeEntity entity : eClass) {
                    result.put(entity, eClass);
                }
            }
            return result;
        }

        public boolean isRecursive(final FunctionSymbol f, final int pos) {
            return this.getRecursiveFuncPos().contains(new FuncPosEntity(f, pos));
        }

        @Override
        public String toString() {
            return this.graph.toDOT();
        }
    }

    public interface TypeEntity {
    }

    public static class FuncPosEntity implements TypeEntity {
        private final FunctionSymbol f;
        private final int pos;

        public FuncPosEntity(final FunctionSymbol f, final int pos) {
            this.f = f;
            this.pos = pos;
        }

        @Override
        public String toString() {
            return this.f.getName() + "/" + this.pos;
        }

        @Override
        public boolean equals(final Object o) {
            final FuncPosEntity other = (FuncPosEntity) o;
            return this.pos == other.pos && this.f.equals(other.f);
        }

        @Override
        public int hashCode() {
            return this.pos + 101 * this.f.hashCode();
        }
    }

    public static class FuncEntity implements TypeEntity {
        private final FunctionSymbol f;

        public FuncEntity(final FunctionSymbol f) {
            this.f = f;
        }

        @Override
        public String toString() {
            return this.f.getName();
        }

        @Override
        public boolean equals(final Object o) {
            final FuncEntity other = (FuncEntity) o;
            return this.f.equals(other.f);
        }

        @Override
        public int hashCode() {
            return this.f.hashCode();
        }
    }

    public static class VarRuleEntity implements TypeEntity {
        private final TRSVariable v;
        private final GeneralizedRule rule;

        public VarRuleEntity(final TRSVariable v, final GeneralizedRule rule) {
            this.v = v;
            this.rule = rule;
        }

        @Override
        public String toString() {
            return this.v.getName() + "/" + this.rule;
        }

        @Override
        public boolean equals(final Object o) {
            if (o instanceof VarRuleEntity) {
                final VarRuleEntity other = (VarRuleEntity) o;
                return this.v.equals(other.v) && this.rule.equals(other.rule);
            } else {
                return false;
            }
        }

        @Override
        public int hashCode() {
            return this.v.hashCode() + 101 * this.rule.hashCode();
        }
    }

}
