package aprove.input.Programs.triples.processors;

import java.util.*;
import java.util.logging.*;

import aprove.input.Programs.prolog.processors.*;
import aprove.input.Programs.prolog.structure.*;
import aprove.input.Programs.triples.*;
import aprove.input.Programs.triples.processors.TriplesToPiDPTransformer.AfsModeAnalyser.ModedRule.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Condition.*;
import aprove.verification.dpframework.PiDPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.dpframework.TRSProblem.Processors.CTRSToQTRSProcessor.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

/**
 * @author nowonder
 * @version $Id$
 */
public class TriplesToPiDPTransformer extends TriplesProblemProcessor {

    public static class AfsModeAnalyser {

        public class AfsException extends Exception {
            private static final long serialVersionUID = 1L;

            public AfsException(final FunctionSymbol f) {
                super(f.getName());
            }
        }

        public static class ModedRule {
            public enum RuleType {
                FACT, FIRST, LAST, MIDDLE
            };

            private List<Boolean> inArgs;
            private final List<Boolean> moding;
            private List<Boolean> outArgs;
            private final GeneralizedRule rule;

            public ModedRule(final GeneralizedRule rule, final List<Boolean> regArgs) {
                this.rule = rule;
                this.moding = regArgs;
            }

            @Override
            public boolean equals(final Object o) {
                final ModedRule other = (ModedRule) o;
                return this.rule.equals(other.rule) && this.moding.equals(other.moding);
            }

            public List<Boolean> getInArgs() {
                return this.inArgs;
            }

            public TRSFunctionApplication getLeft() {
                return this.rule.getLeft();
            }

            public List<Boolean> getModing() {
                return this.moding;
            }

            public List<Boolean> getOutArgs() {
                return this.outArgs;
            }

            public TRSFunctionApplication getRight() {
                return (TRSFunctionApplication) this.rule.getRight();
            }

            public GeneralizedRule getRule() {
                return this.rule;
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

            public void setInArgs(final List<Boolean> inArgs) {
                this.inArgs = inArgs;
            }

            public void setOutArgs(final List<Boolean> outArgs) {
                this.outArgs = outArgs;
            }

            @Override
            public String toString() {
                return this.rule.toString() + ": " + this.moding.toString();
            }
        }

        private Map<Pair<FunctionSymbol, List<Boolean>>, List<Boolean>> afs;
        private final boolean force;
        private Set<ModedRule> have;
        private final AfsSelectionHeuristic heuristic;
        private Map<Pair<FunctionSymbol, List<Boolean>>, List<Boolean>> oldAfs;
        private final Set<GeneralizedRule> P;
        private final Set<GeneralizedRule> R;

        private Graph<ModedRule, Object> ruleGraph;

        private final Map<FunctionSymbol, Set<GeneralizedRule>> sym2Rules;

        public AfsModeAnalyser(
            final Set<GeneralizedRule> pairs,
            final Set<GeneralizedRule> rules,
            final Afs initialAfs,
            final AfsSelectionHeuristic heuristic,
            final boolean force)
        {
            this.force = force;
            this.heuristic = heuristic;
            this.P = pairs;
            this.R = rules;
            this.sym2Rules = new LinkedHashMap<FunctionSymbol, Set<GeneralizedRule>>();
            this.buildSym2Rules(pairs);
            this.buildSym2Rules(rules);
            this.buildRuleGraph(initialAfs);
        }

        public
            Triple<Pair<Set<GeneralizedRule>, Set<GeneralizedRule>>, Afs, Map<FunctionSymbol, Set<List<Boolean>>>>
            getSplitRules()
        {
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
            for (final Node<ModedRule> mNode : this.ruleGraph.getNodes()) {
                final ModedRule mRule = mNode.getObject();
                switch (mRule.getType()) {
                case LAST:
                    this.eliminateRedundantVars(mNode, new LinkedHashSet<TRSVariable>());
                    break;
                case FACT:
                case FIRST:
                case MIDDLE:
                    break;
                }
            }
            final Afs newAfs = new Afs();
            for (final Map.Entry<Pair<FunctionSymbol, List<Boolean>>, List<Boolean>> entry : this.afs.entrySet()) {
                final FunctionSymbol f = this.fromPair(entry.getKey());
                final YNM[] filtering = this.fromBoolList(entry.getValue());
                newAfs.setFiltering(f, filtering);
            }
            final Map<FunctionSymbol, Set<List<Boolean>>> modings =
                new LinkedHashMap<FunctionSymbol, Set<List<Boolean>>>();
            final Set<GeneralizedRule> newP = new LinkedHashSet<GeneralizedRule>();
            final Set<GeneralizedRule> newR = new LinkedHashSet<GeneralizedRule>();
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
                final FunctionSymbol newLeftSym = this.fromPair(oldLeftSym, mRule.getModing());
                final ArrayList<TRSTerm> newLeft = new ArrayList<TRSTerm>();
                for (int i = 0; i < oldLeftSym.getArity(); i++) {
                    if (i + 1 == oldLeftSym.getArity()) {
                        switch (type) {
                        case MIDDLE:
                        case LAST:
                            final TRSFunctionApplication oldOutApp = (TRSFunctionApplication) oldLeft.get(i);
                            final ImmutableList<? extends TRSTerm> oldOut = oldOutApp.getArguments();
                            final FunctionSymbol newOutSym =
                                this.fromPair(oldOutApp.getRootSymbol(), mRule.getOutArgs());
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
                final FunctionSymbol newRightSym = this.fromPair(oldRightSym, mRule.getModing());
                final ArrayList<TRSTerm> newRight = new ArrayList<TRSTerm>();
                for (int i = 0; i < oldRightSym.getArity(); i++) {
                    if (i + 1 == oldRightSym.getArity()) {
                        switch (type) {
                        case FIRST:
                        case MIDDLE:
                            final TRSFunctionApplication oldInApp = (TRSFunctionApplication) oldRight.get(i);
                            final ImmutableList<? extends TRSTerm> oldIn = oldInApp.getArguments();
                            final FunctionSymbol newInSym = this.fromPair(oldInApp.getRootSymbol(), mRule.getInArgs());
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
                final GeneralizedRule rule = mRule.getRule();
                if (this.P.contains(rule)) {
                    newP.add(GeneralizedRule.create(newLeftApp, newRightApp));
                } else if (this.R.contains(rule)) {
                    newR.add(GeneralizedRule.create(newLeftApp, newRightApp));
                } else {
                    throw new IllegalStateException("Found rule which is not contained in P or R: " + rule);
                }
            }
            return new Triple<Pair<Set<GeneralizedRule>, Set<GeneralizedRule>>, Afs, Map<FunctionSymbol, Set<List<Boolean>>>>(
                new Pair<Set<GeneralizedRule>, Set<GeneralizedRule>>(newP, newR),
                newAfs,
                modings);
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
                                if (this.P.contains(rule)) {
                                    final List<Boolean> regArgs = initialAfs.getRegardedArgsAsList(f);
                                    final ModedRule mRule = new ModedRule(rule, regArgs);
                                    this.buildRuleGraph(mRule, null, regArgs, null);
                                }
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
                inSym = ((TRSFunctionApplication) rightApp.getArgument(rightSym.getArity() - 1)).getRootSymbol();
                //                inSym = (rightApp.getArgument(rightSym.getArity()-1)) instanceof FunctionApplication ? ((FunctionApplication)rightApp.getArgument(rightSym.getArity()-1)).getRootSymbol() : null;
                break;
            case LAST:
            case FACT:
                correspondingInSym =
                    FunctionSymbol.create(
                        rightSym.getName().substring(0, rightSym.getName().length() - 3) + "in",
                        rightSym.getArity());
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

        private void buildSym2Rules(final Set<GeneralizedRule> rules) {
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

        private void eliminateRedundantVars(final Node<ModedRule> mNode, final Set<TRSVariable> vars) {
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
                final List<Boolean> leftArgs =
                    this.afs.get(new Pair<FunctionSymbol, List<Boolean>>(leftSym, mRule.getModing()));
                for (int i = 0; i + 1 < leftSym.getArity(); i++) {
                    if (leftArgs.get(i)) {
                        final TRSTerm arg = leftApp.getArgument(i);
                        if (!vars.contains(arg)) {
                            leftArgs.set(i, false);
                        }
                    }
                }
                break;
            }
            switch (type) {
            case LAST:
            case MIDDLE:
                final Node<ModedRule> nextNode = this.ruleGraph.getIn(mNode).iterator().next();
                this.eliminateRedundantVars(nextNode, vars);
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

        private FunctionSymbol fromPair(final FunctionSymbol f, final List<Boolean> moding) {
            if (moding == null) {
                return f;
            }
            final StringBuffer modingId = new StringBuffer();
            for (final boolean mode : moding) {
                modingId.append(mode ? "g" : "a");
            }
            return FunctionSymbol.create(f.getName() + "_" + modingId.toString(), f.getArity());
        }

        private FunctionSymbol fromPair(final Pair<FunctionSymbol, List<Boolean>> key) {
            return this.fromPair(key.x, key.y);
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

    public static class Arguments {
        public boolean force;
        public TriplesToPiDPTransformer.Heuristic heuristic = TriplesToPiDPTransformer.Heuristic.IM2;
    }

    public static class FuncEntity implements TypeEntity {
        private final FunctionSymbol f;

        public FuncEntity(final FunctionSymbol f) {
            this.f = f;
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

        @Override
        public String toString() {
            return this.f.getName();
        }
    }

    public static class FuncPosEntity implements TypeEntity {
        private final FunctionSymbol f;
        private final int pos;

        public FuncPosEntity(final FunctionSymbol f, final int pos) {
            this.f = f;
            this.pos = pos;
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

        @Override
        public String toString() {
            return this.f.getName() + "/" + this.pos;
        }
    }

    public enum Heuristic {
        IM, IM2, IO, IO2, OM, OM2
    };

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

    public class TriplesToPiDPProof extends Proof.DefaultProof {

        Map<FunctionSymbol, Set<List<Boolean>>> modings;
        Set<GeneralizedRule> P;
        PiDPProblem pidp;
        Set<GeneralizedRule> R;
        TriplesProblem tp;

        public TriplesToPiDPProof(
            final TriplesProblem tp,
            final PiDPProblem pidp,
            final Set<GeneralizedRule> P,
            final Set<GeneralizedRule> R,
            final Map<FunctionSymbol, Set<List<Boolean>>> modings)
        {
            this.tp = tp;
            this.pidp = pidp;
            this.P = P;
            this.R = R;
            this.modings = modings;
        }

        /**
         * Formats the output string of the proof and returns it.
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            this.startUp();
            this.result.append("We use the technique of "
                + o.cite(Citation.DT09)
                + ". With regard to the inferred argument filtering the predicates were used in the following modes:\n"
                + o.linebreak());
            for (final Map.Entry<FunctionSymbol, Set<List<Boolean>>> entry : this.modings.entrySet()) {
                FunctionSymbol f = entry.getKey();
                if (f.getArity() == 0) {
                    continue;
                }
                //String[] parts = f.getName().split("_");
                final String newName = f.getName();//.substring(0,f.getName().length()-parts[parts.length-2].length()-parts[parts.length-1].length()-2);
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
            this.result.append("Transforming "
                + ProofUtility.R(o, this.tp.getName(NameLength.SHORT))
                + " into the following "
                + ProofUtility.TRS(o)
                + ":\n"
                + o.linebreak());

            this.result.append(o.export(this.pidp));
            this.result.append("\n" + o.paragraph());

            this.result.append(o.bold("Infinitary Constructor Rewriting Termination")
                + " of "
                + this.pidp.getName(aprove.verification.dpframework.NameLength.SHORT)
                + " implies "
                + o.bold("Termination")
                + " of "
                + this.tp.getName(NameLength.SHORT)
                + o.paragraph()
                + "\n");

            return this.result.toString();
        };
    }

    public class TriplesToPiDPProofs extends Proof.DefaultProof {

        Collection<Proof> proofs;

        public TriplesToPiDPProofs(final Collection<Proof> proofs) {
            this.proofs = proofs;
        }

        /* (non-Javadoc)
         * @see aprove.verification.oldframework.Utility.VerbosityExportable#export(aprove.verification.oldframework.Utility.Export_Util, aprove.verification.oldframework.Utility.VerbosityLevel)
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            for (final Proof p : this.proofs) {
                res.append(p.export(o, level));
                res.append(o.newline());
            }
            return res.toString();
        }

    }

    public interface TypeEntity {
    }

    public static class TypeGraph {
        private final Graph<TypeEntity, Object> graph;
        private Set<FuncPosEntity> recursive;

        public TypeGraph(final Set<GeneralizedRule> R) {
            this.graph = new Graph<TypeEntity, Object>();
            this.buildGraph(R);
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

        public boolean isRecursive(final FunctionSymbol f, final int pos) {
            return this.getRecursiveFuncPos().contains(new FuncPosEntity(f, pos));
        }

        @Override
        public String toString() {
            return this.graph.toDOT();
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
    }

    public static class VarRuleEntity implements TypeEntity {
        private final GeneralizedRule rule;
        private final TRSVariable v;

        public VarRuleEntity(final TRSVariable v, final GeneralizedRule rule) {
            this.v = v;
            this.rule = rule;
        }

        @Override
        public boolean equals(final Object o) {
            final VarRuleEntity other = (VarRuleEntity) o;
            return this.v.equals(other.v) && this.rule.equals(other.rule);
        }

        @Override
        public int hashCode() {
            return this.v.hashCode() + 101 * this.rule.hashCode();
        }

        @Override
        public String toString() {
            return this.v.getName() + "/" + this.rule;
        }
    }

    protected final static Logger logger = Logger
        .getLogger("aprove.input.Programs.triples.processors.TriplesToPiDPTransformer");

    private final boolean eliminate = true;

    private final boolean force;

    private final Heuristic heuristic;

    private final boolean identify = true;

    // Just for PrologTest
    public TriplesToPiDPTransformer() {
        this(new Arguments());
    }

    @ParamsViaArgumentObject
    public TriplesToPiDPTransformer(final Arguments arguments) {
        this.force = arguments.force;
        this.heuristic = arguments.heuristic;
    }

    public static void extendPi(final Afs Pi, final Set<GeneralizedRule> R) {
        boolean tryToExtend = true;
        while (tryToExtend) {
            tryToExtend = false;
            for (final GeneralizedRule rule : R) {
                tryToExtend = TriplesToPiDPTransformer.extendPi(Pi, rule) || tryToExtend;
            }
        }
    }

    /**
     * Transforms a given set of ConditionalRules to a set of
     * GeneralizedRules.
     * @param condRules The set of ConditionalRules to transform.
     * @param fg A PrologFNG for avoiding name conflicts.
     * @return A set of GeneralizedRules computed from the given
     *         ConditionalRules.
     */
    protected static Pair<Set<GeneralizedRule>, Set<FunctionSymbol>> translate(
        final ImmutableSet<ConditionalRule> condRules,
        final PrologFNG fg,
        final boolean identify,
        final boolean eliminate)
    {
        // init graph
        final Graph<CondNode, TRSTerm> condGraph = new Graph<CondNode, TRSTerm>();
        // build special start node (so we have a way to reach all trees in the forest)
        final Node<CondNode> start = new Node<CondNode>(new CondNode(null));
        condGraph.addNode(start);
        // build graph
        TriplesToPiDPTransformer.buildGraph(condGraph, start, condRules, identify);
        // calculate vars
        TriplesToPiDPTransformer.calcVars(condGraph, start, new LinkedHashSet<TRSVariable>());
        if (eliminate) {
            // remove unneeded vars from the paths
            TriplesToPiDPTransformer.elimVars(condGraph);
        }
        // label all nodes with new function symbols U, U1, U2, ...
        final Set<FunctionSymbol> newFuncs = new LinkedHashSet<FunctionSymbol>();
        TriplesToPiDPTransformer.calcFuns(condGraph, start, fg, newFuncs);
        // build rules
        final Set<GeneralizedRule> newRules = new LinkedHashSet<GeneralizedRule>();
        TriplesToPiDPTransformer.buildRules(condGraph, start, newRules);
        return new Pair<Set<GeneralizedRule>, Set<FunctionSymbol>>(newRules, newFuncs);
    }

    /**
     * Transforms the given set of ConditionalRules into a graph. The
     * start node of the graph is specified by the start argument. For
     * every ConditionalRule of the given set nodes and edges are added
     * in the following way:
     * The left side of the ConditionalRule is the label for the
     * outgoing edge from the start node. The node reached with this
     * edge is labeled with the left side of the first condition (or the
     * right side of the ConditionalRule if no conditions exist for this
     * rule). Then the conditions are transformed in the way that every
     * right side of a condition is the label for an outgoing edge from
     * the node labeled with this condition's left side to a node
     * labeled with the left side of the next condition. The last
     * condition's edge (labeled with its right side) leads to a node
     * labeled with the right side of the ConditionalRule.
     * So all edges but the first from the start node are labeled with
     * the right sides of the conditions while the first edge is labeled
     * with the left side of the ConditionalRule. All nodes but the last
     * are labeled with the left sides of the conditions while the last
     * node is labeled with the right side of the ConditionalRule.
     * If the identify flag is set then edges will be reused if the
     * labels of the edge and the end node of this edge are equal to the
     * labels of a new edge and its end node.
     * @param condGraph The graph to be built (should only contain the
     *                  start node).
     * @param start The start node for the graph.
     * @param condRules The set of ConditionalRules to be transformed
     *                  into the graph.
     * @param identify Flag to indicate if edges should be reused.
     */
    private static void buildGraph(
        final Graph<CondNode, TRSTerm> condGraph,
        final Node<CondNode> start,
        final Set<ConditionalRule> condRules,
        final boolean identify)
    {
        for (final ConditionalRule condRule : condRules) {
            Node<CondNode> current = start;
            TRSTerm edgeLabel = condRule.getLeft();
            for (final Condition cond : condRule.getConditions()) {
                final TRSTerm nodeLabel = cond.getLeft();
                Node<CondNode> nextNode = null;
                if (identify) {
                    // if we already have an edge with the same label to a node with the same term, reuse it
                    for (final Edge<TRSTerm, CondNode> edge : condGraph.getOutEdges(current)) {
                        if (edge.getObject().equals(edgeLabel)
                            && edge.getEndNode().getObject().getTerm().equals(nodeLabel))
                        {
                            nextNode = edge.getEndNode();
                            break;
                        }
                    }
                }
                if (nextNode == null) {
                    // if we do not reuse an existing node, build a new one and add a corresponding edge
                    nextNode = new Node<CondNode>(new CondNode(nodeLabel));
                    condGraph.addEdge(current, nextNode, edgeLabel);
                }
                current = nextNode;
                edgeLabel = cond.getRight();
            }
            final Node<CondNode> leafNode = new Node<CondNode>(new CondNode(condRule.getRight()));
            condGraph.addEdge(current, leafNode, edgeLabel);
        }
    }

    /**
     * Transforms the given graph in a set of GeneralizedRules.<br><br>
     * The graph must be prepared in the way that new FunctionSymbols
     * have been created by invoking the calcFuns() method.<br><br>
     * This method traverses the graph and builds new GeneralizedRules
     * in the following way:<br>
     * The left side of the rule is the label of the first edge in case
     * of the start node and a new FunctionApplication built from the
     * new FunctionSymbol of the next edge and the variables in use at
     * the current node followed by the next edge's label as arguments
     * otherwise. The right side of the rule is the label of the edge's
     * end node in case of the last node and a new FunctionApplication
     * built from the new FunctionSymbol of the end node and its
     * variables in use and its label as arguments otherwise. Speaking
     * in terms of ConditionalRules the GeneralizedRules are constructed
     * by using the left side of the ConditionalRule as left side of the
     * first GeneralizedRule and the helping FunctionApplications as
     * left sides of all other GeneralizedRules for this
     * ConditionalRule. The right side of the last GeneralizedRule is
     * the right side of the ConditionalRule and the right side of all
     * other GeneralizedRules are the helping FunctionApplications. The
     * helping FunctionApplications have the next condition's left side
     * as argument if they are on a right side in the GeneralizedRule
     * and the next condition's right side as argument if they are on
     * the left side of the GeneralizedRule - always after the variables
     * in use as arguments.<br><br>
     * This method should be called on the start node as current node
     * and an empty set of GeneralizedRules.
     * @param condGraph The graph to transform.
     * @param current The current node to process.
     * @param newRules The set of GeneralizedRules to which the new
     *                 rules are added.
     */
    private static void buildRules(
        final Graph<CondNode, TRSTerm> condGraph,
        final Node<CondNode> current,
        final Set<GeneralizedRule> newRules)
    {
        final CondNode condNode = current.getObject();
        final boolean isStart = condNode.getTerm() == null;
        for (final Edge<TRSTerm, CondNode> edge : condGraph.getOutEdges(current)) {
            TRSTerm lhs = edge.getObject();
            if (!isStart) {
                final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
                args.addAll(condNode.getVars());
                args.add(lhs);
                lhs =
                    TRSTerm.createFunctionApplication(
                        edge.getStartNode().getObject().getF(),
                        ImmutableCreator.create(args));
            }
            final CondNode toNode = edge.getEndNode().getObject();
            TRSTerm rhs = toNode.getTerm();
            if (toNode.getF() != null) {
                final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
                args.addAll(toNode.getVars());
                args.add(rhs);
                rhs = TRSTerm.createFunctionApplication(toNode.getF(), ImmutableCreator.create(args));
            }
            newRules.add(GeneralizedRule.create((TRSFunctionApplication) lhs, rhs));
            TriplesToPiDPTransformer.buildRules(condGraph, edge.getEndNode(), newRules);
        }
    }

    /**
     * Prepares the given graph for the transformation in
     * GeneralizedRules through calculating new FunctionSymbols for
     * helping FunctionApplications. The names for the new
     * FunctionSymbols are generated with the given PrologFNG
     * deriving from "U". This method should be first called with the
     * start node as current node.
     * @param condGraph The graph to prepare.
     * @param current The current node to process.
     * @param fg The PrologFNG for new names.
     */
    private static void calcFuns(
        final Graph<CondNode, TRSTerm> condGraph,
        final Node<CondNode> current,
        final PrologFNG fg,
        final Set<FunctionSymbol> newFuncs)
    {
        final CondNode condNode = current.getObject();
        final Set<Edge<TRSTerm, CondNode>> outEdges = condGraph.getOutEdges(current);
        if (!outEdges.isEmpty()) {
            final FunctionSymbol newFunc =
                FunctionSymbol.create(fg.getFreshName("U", false), 1 + condNode.getVars().size());
            condNode.setF(newFunc);
            newFuncs.add(newFunc);
        }
        for (final Edge<TRSTerm, CondNode> edge : outEdges) {
            TriplesToPiDPTransformer.calcFuns(condGraph, edge.getEndNode(), fg, newFuncs);
        }
    }

    /**
     * Computes the set of variables used along a path through the
     * graph. The current node's variables are set to the given set of
     * variables. Then for all outgoing edges from the current node a
     * new set of variables is created with the variables of the next
     * edge's term in addition to all old variables. The method is then
     * recursively called with this new set of variables and the end
     * node of the edge.
     * This method should be first called with the start node and an
     * empty set of variables.
     * @param condGraph The graph in which the variables are computed.
     * @param current The current node.
     * @param vars The set of already computed variables.
     */
    private static void calcVars(
        final Graph<CondNode, TRSTerm> condGraph,
        final Node<CondNode> current,
        final Set<TRSVariable> vars)
    {
        final CondNode condNode = current.getObject();
        condNode.setVars(vars);
        for (final Edge<TRSTerm, CondNode> edge : condGraph.getOutEdges(current)) {
            final Set<TRSVariable> newVars = new LinkedHashSet<TRSVariable>(vars);
            newVars.addAll(edge.getObject().getVariables());
            TriplesToPiDPTransformer.calcVars(condGraph, edge.getEndNode(), newVars);
        }
    }

    /**
     * Creates an ArrayList of Terms out of the specified ArrayList of
     * PrologTerms using the toConstructorTerm() method for every
     * PrologTerm in the list.
     * @param arguments The list of PrologTerms to transform.
     * @param fridge
     * @return An ArrayList of Terms built from the given PrologTerms.
     */
    private static ArrayList<TRSTerm> createConstructorTermsForGeneralizedRule(
        final List<PrologTerm> arguments,
        final PrologFNG fridge)
    {
        final ArrayList<TRSTerm> res = new ArrayList<TRSTerm>();
        for (final PrologTerm arg : arguments) {
            res.add(TriplesToPiDPTransformer.toConstructorTerm(arg, fridge));
        }
        return res;
    }

    /**
     * Creates an ImmutableArrayList of Terms out of the specified
     * term's arguments for use as arguments in GeneralizedRules.
     * @param term The PrologTerm from which to build terms.
     * @param fridge
     * @return An ImmutableArrayList of Terms built from this term's
     *         arguments.
     */
    private static ImmutableArrayList<? extends TRSTerm> createTermsForGeneralizedRule(
        final PrologTerm term,
        final PrologFNG fridge)
    {
        final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
        for (final PrologTerm t : term.getArguments()) {
            if (t.isVariable()) {
                args.add(TRSTerm.createVariable(t.getName()));
            } else {
                final ArrayList<TRSTerm> termArgs =
                    TriplesToPiDPTransformer.createConstructorTermsForGeneralizedRule(t.getArguments(), fridge);
                args.add(TRSTerm.createFunctionApplication(
                    FunctionSymbol.create(fridge.getFreshName(t.getName(), true), t.getArity()),
                    ImmutableCreator.create(termArgs)));
            }
        }
        return ImmutableCreator.create(args);
    }

    /**
     * Eliminates all variables along the graph that are not used
     * anymore from the current position on. Therefore the nodes are
     * processed in the order of their ranks beginning with rank 0.
     * For every such node a new empty set of variables is created and
     * then for all outgoing edges the variables of the edges' end nodes
     * are added. Afterwards the retainAll() method is called for the
     * current node's set of variables with the created set as argument.
     * @param condGraph The graph in which the variables should be
     *                  eliminated.
     */
    private static void elimVars(final Graph<CondNode, TRSTerm> condGraph) {
        for (final Set<Node<CondNode>> rank : condGraph.getRanks()) {
            for (final Node<CondNode> node : rank) {
                final CondNode condNode = node.getObject();
                final TRSTerm term = condNode.getTerm();
                if (term == null) {
                    // we have reached the root node
                    break;
                }
                final Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>();
                for (final Edge<TRSTerm, CondNode> edge : condGraph.getOutEdges(node)) {
                    final CondNode toNode = edge.getEndNode().getObject();
                    vars.addAll(toNode.getTerm().getVariables());
                    vars.addAll(toNode.getVars());
                }
                condNode.getVars().retainAll(vars);
            }
        }
    }

    private static boolean extendPi(final Afs Pi, final TRSFunctionApplication fapp, final Set<TRSVariable> evilVars) {
        final FunctionSymbol f = fapp.getRootSymbol();
        final ImmutableList<? extends TRSTerm> args = fapp.getArguments();
        final boolean[] regarded = Pi.getRegardedArgs(f);
        final YNM[] newArgs = new YNM[regarded.length];
        boolean changed = false;
        for (int i = 0; i < regarded.length; i++) {
            if (regarded[i]) {
                final TRSTerm argi = args.get(i);
                if (argi.isVariable()) {
                    if (evilVars.contains(argi)) {
                        newArgs[i] = YNM.NO;
                        changed = true;
                    } else {
                        newArgs[i] = YNM.YES;
                    }
                } else {
                    changed = TriplesToPiDPTransformer.extendPi(Pi, (TRSFunctionApplication) argi, evilVars) || changed;
                    newArgs[i] = YNM.YES;
                }
            } else {
                newArgs[i] = YNM.NO;
            }
        }
        if (changed) {
            Pi.setFiltering(f, newArgs);
        }
        return changed;
    }

    private static boolean extendPi(final Afs Pi, final GeneralizedRule rule) {
        final Set<TRSVariable> lvars = Pi.filterTerm(rule.getLeft()).getVariables();
        final Set<TRSVariable> rvars = Pi.filterTerm(rule.getRight()).getVariables();
        final Set<TRSVariable> evilVars = new LinkedHashSet<TRSVariable>(rvars);
        evilVars.removeAll(lvars);
        if (!evilVars.isEmpty()) {
            //System.err.println("Evil vars ins "+rule+": "+evilVars);
            return TriplesToPiDPTransformer.extendPi(Pi, (TRSFunctionApplication) rule.getRight(), evilVars);
        }
        return false;
    }

    /**
     * Creates a ConditionalRule out of the specified clause using the
     * specified PrologFNG to avoid conflicts due to the use of
     * the same names for different objects.
     * @param clause The PrologClause from which to build a rule.
     * @param fridge The PrologFNG.
     * @return A new ConditionalRule built from this clause.
     */
    private static ConditionalRule toConditionalRule(final PrologClause clause, final PrologFNG fridge) {
        final ImmutableArrayList<? extends TRSTerm> args =
            TriplesToPiDPTransformer.createTermsForGeneralizedRule(clause.getHead(), fridge);
        return ConditionalRule.create(
            TRSTerm.createFunctionApplication(fridge.createInFunctionSymbol(clause.getHead()), args),
            TRSTerm.createFunctionApplication(fridge.createOutFunctionSymbol(clause.getHead()), args),
            clause.getBody() == null ? ImmutableCreator.create(new ArrayList<Condition>()) : TriplesToPiDPTransformer
                .toConditions(clause.getBody(), fridge));
    }

    /**
     * Creates an ImmutableList of Conditions out of the specified term
     * using the specified PrologFNG to avoid conflicts due to
     * the use of the same names for different objects.
     * @param term The PrologTerm to be transformed.
     * @param f The PrologFNG.
     * @return An ImmutableList of Conditions built from this term.
     */
    private static ImmutableList<Condition> toConditions(final PrologTerm term, final PrologFNG fridge) {
        final List<Condition> conditions = new ArrayList<Condition>();
        term.walkConjunction(new TermWalker() {

            @Override
            public boolean goDeeper(final PrologTerm term) {
                return false;
            }

            @Override
            public boolean isApplicable(final PrologTerm term) {
                return true;
            }

            @Override
            public void performAction(final PrologTerm term) {
                final ImmutableArrayList<? extends TRSTerm> args =
                    TriplesToPiDPTransformer.createTermsForGeneralizedRule(term, fridge);
                conditions.add(Condition.create(
                    TRSTerm.createFunctionApplication(fridge.createInFunctionSymbol(term), args),
                    TRSTerm.createFunctionApplication(fridge.createOutFunctionSymbol(term), args),
                    ConditionType.ARROW));
            }

        });
        return ImmutableCreator.create(conditions);
    }

    /**
     * Creates a Term out of the specified PrologTerm interpreting every
     * FunctionSymbol as constructor symbol.
     * @param term The PrologTerm from which to build a Term.
     * @param fridge
     * @param fridge
     * @return A Term built from the specified PrologTerm, where all
     *         FunctionApplications are seen as constructors.
     */
    private static TRSTerm toConstructorTerm(final PrologTerm term, final PrologFNG fridge) {
        return term.isVariable() ? TRSTerm.createVariable(term.getName()) : TRSTerm.createFunctionApplication(
            FunctionSymbol.create(fridge.getFreshName(term.getName(), true), term.getArity()),
            ImmutableCreator.create(TriplesToPiDPTransformer.createConstructorTermsForGeneralizedRule(
                term.getArguments(),
                fridge)));
    }

    public boolean getForce() {
        return this.force;
    }

    @Override
    public boolean isTriplesApplicable(final TriplesProblem tp) {
        return true;
    }

    @Override
    protected Result processTriplesProblem(final TriplesProblem tp, final Abortion aborter) throws AbortionException {
        final PrologProgram triples = tp.getTriples().copy();
        triples.flattenOutConjunctions();
        triples.transformUnderscores();
        final PrologProgram clauses = tp.getClauses().copy();
        clauses.flattenOutConjunctions();
        clauses.transformUnderscores();
        final PrologProgram all = new PrologProgram();
        for (final PrologClause c : triples.getClauses()) {
            all.addClause(c);
        }
        for (final PrologClause c : clauses.getClauses()) {
            all.addClause(c);
        }

        TriplesToPiDPTransformer.logger.log(Level.FINEST, "Dumping triples:\n"); //#
        TriplesToPiDPTransformer.logger.log(Level.FINEST, triples.toString() + "\n"); //#
        TriplesToPiDPTransformer.logger.log(Level.FINEST, "Dumping clauses:\n"); //#
        TriplesToPiDPTransformer.logger.log(Level.FINEST, clauses.toString() + "\n"); //#

        if (!PrologProgram.isLogicProgram(all)) {
            TriplesToPiDPTransformer.logger.log(
                Level.FINE,
                "The triples and clauses do not form a definite logic program.\n");
            return ResultFactory.unsuccessful();
        }

        final Set<FunctionSymbol> preds = all.createSetOfAllPredicates();

        final List<Afs> piList = java.util.Collections.singletonList(this.addIn(tp.getAfs(), preds));
        final List<Triple<Afs, Set<GeneralizedRule>, Set<GeneralizedRule>>> protoR =
            new ArrayList<Triple<Afs, Set<GeneralizedRule>, Set<GeneralizedRule>>>();
        for (final Afs pi : piList) {
            final Set<ConditionalRule> conditionalsP = new LinkedHashSet<ConditionalRule>();
            final Set<ConditionalRule> conditionalsR = new LinkedHashSet<ConditionalRule>();

            final PrologFNG fridge = new PrologFNG(new LinkedHashSet<String>(), FreshNameGenerator.PROLOG_FUNCS);
            for (final PrologClause clause : triples.getClauses()) {
                conditionalsP.add(TriplesToPiDPTransformer.toConditionalRule(clause, fridge));
            }
            for (final PrologClause clause : clauses.getClauses()) {
                conditionalsR.add(TriplesToPiDPTransformer.toConditionalRule(clause, fridge));
            }

            final Set<GeneralizedRule> oneP =
                TriplesToPiDPTransformer.translate(
                    ImmutableCreator.create(conditionalsP),
                    fridge,
                    this.identify,
                    this.eliminate).x;
            final Set<GeneralizedRule> oneR =
                TriplesToPiDPTransformer.translate(
                    ImmutableCreator.create(conditionalsR),
                    fridge,
                    this.identify,
                    this.eliminate).x;
            protoR.add(new Triple<Afs, Set<GeneralizedRule>, Set<GeneralizedRule>>(pi, oneP, oneR));
        }
        final List<PiDPProblem> obligations = new ArrayList<PiDPProblem>();
        final List<Proof> proofs = new ArrayList<Proof>();
        for (final Triple<Afs, Set<GeneralizedRule>, Set<GeneralizedRule>> match : protoR) {
            Afs Pi = match.x;
            Set<GeneralizedRule> P = match.y;
            Set<GeneralizedRule> R = match.z;
            //System.err.println(Pi);
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
            final Triple<Pair<Set<GeneralizedRule>, Set<GeneralizedRule>>, Afs, Map<FunctionSymbol, Set<List<Boolean>>>> pair =
                new AfsModeAnalyser(P, R, Pi, heuristic, this.force).getSplitRules();
            P = pair.x.x;
            R = pair.x.y;
            Pi = pair.y;
            final PiTRSProblem pitrs = PiTRSProblem.create(ImmutableCreator.create(P), new ImmutableAfs(Pi));
            final Pair<ImmutableSet<GeneralizedRule>, Map<FunctionSymbol, FunctionSymbol>> dppair = pitrs.getDPs();
            P = dppair.x;
            Pi = Pi.addTuples(dppair.y);
            final Set<GeneralizedRule> PcupR = new LinkedHashSet<GeneralizedRule>(P);
            PcupR.addAll(R);
            PrologToPiTRSTransformer.extendPi(Pi, PcupR);
            final Set<FunctionSymbol> sig = CollectionUtils.getFunctionSymbols(P);
            sig.addAll(CollectionUtils.getFunctionSymbols(R));
            Pi = Pi.reduceToSignature(sig);
            final PiDPProblem pidp =
                PiDPProblem.create(
                    ImmutableCreator.create(P),
                    PiTRSProblem.create(ImmutableCreator.create(R), new ImmutableAfs(Pi)));
            final Proof proof = new TriplesToPiDPProof(tp, pidp, P, R, pair.z);
            obligations.add(pidp);
            proofs.add(proof);
        }
        final YNMImplication implication = YNMImplication.SOUND;
        if (obligations.size() == 1) {
            return ResultFactory.proved(obligations.get(0), implication, proofs.get(0));
        }
        final Proof proof = new TriplesToPiDPProofs(proofs);
        return ResultFactory.provedAnd(obligations, implication, proof);
    }

    private Afs addIn(final Afs afs, final Set<FunctionSymbol> preds) {
        final Afs newAfs = new Afs();
        for (final Triple<FunctionSymbol, YNM[], Boolean> entry : afs.getFilterings()) {
            FunctionSymbol f = entry.x;
            String name = f.getName();
            if (preds.contains(f)) {
                name += "_in";
                f = FunctionSymbol.create(name, f.getArity());
            }
            newAfs.setFiltering(f, new Pair<YNM[], Boolean>(entry.y, entry.z));
        }
        return newAfs;
    }

}
